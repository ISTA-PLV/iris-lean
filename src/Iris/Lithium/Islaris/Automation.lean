/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode
import Iris.Lithium.Base
import Iris.Lithium.Lithium
import Iris.Lithium.Islaris.Isla
import Iris.Lithium.Islaris.Instructions.InstrLdr
import Iris.Lithium.Islaris.Instructions.InstrStr

namespace Islaris
open Lean Iris BI ProofMode Elab Meta Lithium

variable {PROP : Type u} [BI PROP]

section bitvecCast
def bitvecCastOkR [BI PROP] {n} (b : BitVec n) (n' : Nat) (E : BitVec n' → PROP) : PROP :=
  iprop(∃ h : n = n', E (b.cast h))

@[irun_preprocess]
def bitvecCastOk {n} (b : BitVec n) (n' : Nat) : Li PROP (BitVec n') where
  run := bitvecCastOkR b n'
  mono' E1 E2 := by mysorry

theorem bitvecCastOk_tac n (b : BitVec n) P E :
  (P ⊢ E b) →
  (P ⊢ bitvecCastOkR (PROP:=PROP) b n E) := by mysorry

@[irun_tac bitvecCastOkR _ _ _]
def irunBitvecCast : IRunTacticType := fun goal _config => do profileitM Exception "irunBitvecCast" (← getOptions) do
  let ig := goal
  let { u, prop, bi, hyp, goal:=G } := ig

  let_expr bitvecCastOkR _ _ n b n' E := G | return none
  let .true ← isDefEq n n' | return none
  let g' := IrisGoalShallow.toExpr { ig with goal := Expr.beta E #[b] }
  let goal' ← mkFreshExprSyntheticOpaqueMVar g'
  let pf := mkApp7 (.const ``bitvecCastOk_tac [u]) prop bi n b hyp E goal'
  return .some (pf, [goal'.mvarId!], [])

end bitvecCast

section ValuShape
inductive ValuShape where
| exact (v : Valu)
| struct (ss : List (String × ValuShape))
| mask (n : Nat) (mask : Int) (v : Int)
| bits (n : Nat)
| prop (P : Valu → Prop)
| unknown

@[irun_simp, irun_solve]
def Valu.hasShape : Valu → ValuShape → Prop
| v, .exact v' => v = v'
| .struct s, .struct s' => s.length = s'.length -- TODO: missing
| .base <| .bits _b, .mask _n _m _v' => False -- TODO
| .base <| .bits b, .bits n => b.size = n
| v, .prop P => P v
| _, .unknown => True
| _, _ => False

def hasShapeOkR [BI PROP] (v : Valu) (s : ValuShape) (E : PROP) : PROP :=
  iprop(⌜v.hasShape s⌝ -∗ E)

@[irun_preprocess]
def hasShapeOk (v : Valu) (s : ValuShape) : Li PROP Unit where
  run E := hasShapeOkR v s (E ())
  mono' E1 E2 := by mysorry

@[irun]
theorem hasShapeOk_exact v v' E :
  hasShapeOkR (PROP:=PROP) v (.exact v') E ⊣
    inhaleR (prop (v = v')) λ _ => E
    := by mysorry

end ValuShape


section subst
partial def substBaseValExpr (v : Expr) (x : VarName) (e : Expr) : MetaM Expr :=
  match_expr e with
  | BaseVal.symbolic v' => do
    let some v' := v'.nat?
      | throwError "substBaseValExpr: cannot compute substitution in {e}"
    if v' = x then return v else return e
  | BaseVal.bool _ => return e
  | BaseVal.bits _ => return e
  | BaseVal.enum _ => return e
  | _ => throwError "substBaseValExpr: cannot compute substitution in {e}"

partial def substValuExpr (v : Expr) (x : VarName) (e : Expr) : MetaM Expr :=
  match_expr e with
  | Valu.base v' => do return e.modifyApp1 (← substBaseValExpr v x v')
  | Valu.i _ _ => do return e
  | Valu.string _ => do return e
  | Valu.unit => do return e
  | Valu.vector vs => do
    let some vs ← vs.mapMListLit (substValuExpr v x)
      | throwError "substValuExpr: cannot compute substitution in {e}"
    return e.modifyApp1 vs
  | Valu.list vs => do
    let some vs ← vs.mapMListLit (substValuExpr v x)
      | throwError "substValuExpr: cannot compute substitution in {e}"
    return e.modifyApp1 vs
  | Valu.struct vs => do
    let some vs ← vs.mapMListLit (λ e =>
      match_expr e with
      | Prod.mk _ _ _ v' => do return e.modifyApp1 (← substValuExpr v x v')
      | _ => throwError "substValuExpr: cannot compute substitution in {e}"
      )
      | throwError "substValuExpr: cannot compute substitution in {e}"
    return e.modifyApp1 vs
  | Valu.constructor _ v' => do return e.modifyApp1 (← substValuExpr v x v')
  | Valu.poison => do return e
  | _ => throwError "substValuExpr: cannot compute substitution in {e}"

partial def substExpExpr (v : Expr) (x : VarName) (e : Expr) : MetaM Expr :=
  match_expr e with
  | Exp.val v' => do return e.modifyApp1 (← substBaseValExpr v x v')
  | Exp.unop _ e1 => do return e.modifyApp1 (← substExpExpr v x e1)
  | Exp.binop _ e1 e2 => do return e.modifyApp2 (← substExpExpr v x e1) (← substExpExpr v x e2)
  | Exp.manyop _ es => do
    let some es ← es.mapMListLit (substExpExpr v x)
      | throwError "substExpExpr: cannot compute substitution in {e}"
    return e.modifyApp1 es
  | Exp.ite e1 e2 e3 => do return mkApp3 (mkConst ``Exp.ite) (← substExpExpr v x e1) (← substExpExpr v x e2) (← substExpExpr v x e3)
  | _ => throwError "substExpExpr: cannot compute substitution in {e}"

partial def substSmtExpr (v : Expr) (x : VarName) (e : Expr) : MetaM Expr :=
  -- do logInfo m!"Smt: {e}"
  match_expr e with
  | Smt.declareConst _ _ => do return e
  | Smt.defineConst _ e' => do return e.modifyApp1 (← substExpExpr v x e')
  | Smt.assert e' => do return e.modifyApp1 (← substExpExpr v x e')
  | Smt.defineEnum _ _ _ => do return e
  | _ => throwError "substSmtExpr: cannot compute substitution in {e}"

partial def substEventExpr (v : Expr) (x : VarName) (e : Expr) : MetaM Expr :=
  -- do logInfo m!"Event: {e}"
  match_expr e with
  | Event.smt s => do return e.modifyApp1 (← substSmtExpr v x s)
  | Event.branch _ _ => do return e
  | Event.readReg _ _ v' => do return e.modifyApp1 (← substValuExpr v x v')
  | Event.writeReg _ _ v' => do return e.modifyApp1 (← substValuExpr v x v')
  | Event.readMem v' rkind addr nb tag => do
    let some tag ← tag.mapMOptionLit (substValuExpr v x)
      | throwError "substEventExpr: cannot compute substitution in {e}"
    return mkApp5 (mkConst ``Event.readMem) (← substValuExpr v x v') (← substValuExpr v x rkind) (← substValuExpr v x addr) nb tag
  | Event.writeMem v' wkind addr data nb tag => do
    let some tag ← tag.mapMOptionLit (substValuExpr v x)
      | throwError "substEventExpr: cannot compute substitution in {e}"
    return mkApp6 (mkConst ``Event.writeMem) (← substValuExpr v x v') (← substValuExpr v x wkind) (← substValuExpr v x addr) (← substValuExpr v x data) nb tag
  | Event.branchAddress addr => do return mkApp (mkConst ``Event.branchAddress) (← substValuExpr v x addr)
  | Event.barrier bkind => do return mkApp (mkConst ``Event.barrier) (← substValuExpr v x bkind)
  | Event.cacheOp ckind addr => do return mkApp2 (mkConst ``Event.cacheOp) (← substValuExpr v x ckind) (← substValuExpr v x addr)
  | Event.markReg _ _ => do return e
  | Event.cycle => do return e
  | Event.instr opcode => do return mkApp (mkConst ``Event.instr) (← substValuExpr v x opcode)
  | Event.sleeping _ => do return e
  | Event.wakeRequest => do return e
  | Event.sleepRequest => do return e
  | Event.call _ => do return e
  | Event.return _ => do return e
  | Event.assumeReg _ _ v' => do return e.modifyApp1 (← substValuExpr v x v')
  | Event.assume _ => do return e
  | Event.funAssume _ v' a => do return e.modifyApp2 (← substValuExpr v x v') a
  | Event.useFunAssume _ v' a => do return e.modifyApp2 (← substValuExpr v x v') a
  | Event.abstractCall _ v' a => do return e.modifyApp2 (← substValuExpr v x v') a
  | Event.abstractPrimop _ v' a => do return e.modifyApp2 (← substValuExpr v x v') a
  | _ => throwError "substEventExpr: cannot compute substitution in {e}"


partial def substTraceExpr (v : Expr) (x : VarName) (e : Expr) : MetaM Expr :=
  match_expr e with
  | IslaTrace.nil => return e
  | IslaTrace.cons e t' => return mkApp2 (mkConst ``IslaTrace.cons) (← substEventExpr v x e) (← substTraceExpr v x t')
  | IslaTrace.cases ts => do
    let some ts ← ts.mapMListLit (substTraceExpr v x) | throwError "substTraceExpr: cannot compute substitution in {e}"
    return mkApp (mkConst ``IslaTrace.cases) ts
  | _ => throwError "substTraceExpr: cannot compute substitution in {e}"
-- we could also return [mkApp3 (mkConst ``substTrace) v (mkNatLit x) e], but that would not help

def substTraceOkR (v : BaseVal) (x : VarName) (t : IslaTrace) (E : IslaTrace → PROP) : PROP :=
  E (substTrace v x t)

@[irun_preprocess]
def substTraceOk (v : BaseVal) (x : VarName) (t : IslaTrace) : Li PROP IslaTrace := {
  run := substTraceOkR v x t
  mono' E1 E2 := by mysorry
}

@[irun_tac substTraceOkR _ _ _ _]
def irunSubstTraceOk : IRunTacticType := fun goal _config => do profileitM Exception "irunSubstTraceOk" (← getOptions) do
  let ig := goal
  let G := ig.goal

  let_expr substTraceOkR _ v x t E := G | return none
  let .some x := x.nat? | return none
  let t' := ← substTraceExpr v x t
  let g' := {ig with goal := Expr.beta E #[t']}.toExpr
  let goal' ← mkFreshExprSyntheticOpaqueMVar g'
  let pf ← mkExpectedTypeHint goal' ig.toExpr
  return .some (pf, [goal'.mvarId!], [])

end subst

section fns

def expOkR [BI PROP] (e : Exp) (E : BaseVal → PROP) : PROP := sorry

@[irun_preprocess]
def expOk (e : Exp) : Li PROP BaseVal where
  run := expOkR e
  mono' E1 E2 := by mysorry

def aexpOkR [BI PROP] (e : AExp) (E : BaseVal → PROP) : PROP := sorry

@[irun_preprocess]
def aexpOk (e : AExp) : Li PROP BaseVal where
  run := aexpOkR e
  mono' E1 E2 := by mysorry

def asmOkR [BI PROP] (t : IslaTrace) : PROP := sorry

@[irun_preprocess]
def asmOk (t : IslaTrace) : Li PROP Empty where
  run _ := asmOkR t
  mono' E1 E2 := by mysorry

end fns

section regs

def readAccessor (al : AccessorList) (v : Valu) : Option Valu :=
  match al with
  | [] => some v
  | .field f :: al' => do
    let s ← (match v with | .struct s => some s | _ => none)
    let v' ← s.find? (λ x => x.1 = f)
    readAccessor al' v'.2

def readAccessorOkR (al : AccessorList) (v : Valu) (E : Valu → PROP) : PROP :=
  iprop(∃ v', ⌜readAccessor al v = some v'⌝ ∗ E v')

@[irun_preprocess]
def readAccessorOk (al : AccessorList) (v : Valu) : Li PROP Valu where
  run := readAccessorOkR al v
  mono' E1 E2 := by mysorry

@[irun]
theorem readAccessorOk_field_eq f v s:
  readAccessorOkR (PROP:=PROP) [Accessor.field f] (Valu.struct ((f, v) :: s)) :- do return v := by mysorry

@[irun:mid]
theorem readAccessorOk_field_neq f f' v s:
  f ≠ f' →
  readAccessorOkR (PROP:=PROP) [Accessor.field f] (Valu.struct ((f', v) :: s)) :- readAccessorOk [Accessor.field f] (Valu.struct s) := by mysorry

inductive RegKind where
| reg (re : String)
| field (re f : String)
deriving DecidableEq, ToExpr

def _root_.Lean.Expr.regKind? (e : Expr) : Option RegKind :=
  match_expr e with
  | RegKind.reg re =>
    match re with
    | .lit (Literal.strVal re) => some (.reg re)
    | _ => none
  | RegKind.field re f =>
    match re, f with
    | .lit (Literal.strVal re), .lit (Literal.strVal f) => some (.field re f)
    | _, _ => none
  | _ => none


partial def lookupRegCol (regs : List (RegKind × ValuShape)) (f : RegKind) : Option ValuShape :=
-- TODO: lookup in fields of a struct
  (·.2) <$> (regs.find? (λ (f', _) => if f = f' then true else false))

theorem lookupRegCol_cons_eq regs f f' s :
  f = f' →
  lookupRegCol ((f', s)::regs) f = some s := by mysorry

theorem lookupRegCol_cons_neq regs f f' s s':
  lookupRegCol regs f = some s' →
  if f ≠ f' then -- uses reduction in the kernel
    lookupRegCol ((f', s)::regs) f = some s'
  else
    True := by mysorry

partial def lookupRegColExpr (regs : Expr) (f : RegKind) : MetaM (Option (Expr × Expr)) :=
  do
  match_expr ← whnfR regs with
  | List.nil _ => return none
  | List.cons _ p regs' =>
    match_expr p with
    | Prod.mk _ _ fe' s =>
      let some f' := fe'.regKind? | throwError "lookupRegCol: cannot compute regcol lookup in {regs}"
      if f' == f then
        return some (s, mkApp5 (mkConst ``lookupRegCol_cons_eq) regs (toExpr f) fe' s
          (mkApp2 (.const ``Eq.refl [1]) (mkConst ``RegKind) fe'))
      else
        let some (s', pf) ← lookupRegColExpr regs' f | return none
        return some (s', mkApp6 (mkConst ``lookupRegCol_cons_neq) regs (toExpr f) fe' s s' pf)
    | _ => throwError "lookupRegCol: cannot compute regcol lookup in {regs}"
  | _ => throwError "lookupRegCol: cannot compute regcol lookup in {regs}"

def lookupRegColOkR (regs : List (RegKind × ValuShape)) (f : RegKind) (E : ValuShape → PROP) : PROP :=
  iprop(∃ v, ⌜lookupRegCol regs f = some v⌝ ∗ E v)

@[irun_preprocess]
def lookupRegColOk (regs : List (RegKind × ValuShape)) (f : RegKind) : Li PROP ValuShape where
  run := lookupRegColOkR regs f
  mono' E1 E2 := by mysorry

theorem lookupRegColOk_tac regs f s E P :
  lookupRegCol regs f = some s →
  (P ⊢ E s) →
  P ⊢ lookupRegColOkR (PROP:=PROP) regs f E  := by mysorry

@[irun_tac lookupRegColOkR _ _ _]
def irunLookupRegCol : IRunTacticType := fun goal _config => do profileitM Exception "irunLookupRegCol" (← getOptions) do
  let ig := goal
  let { u, prop, bi, hyp, goal:=G } := ig

  let_expr lookupRegColOkR _ _ regs fe E := G | return none
  let some f := fe.regKind? | return none
  let some (e, epf) ← lookupRegColExpr regs f | return none
  let g' := IrisGoalShallow.toExpr { ig with goal := Expr.beta E #[e] }
  let goal' ← mkFreshExprSyntheticOpaqueMVar g'
  let pf := mkApp9 (.const ``lookupRegColOk_tac [u]) prop bi regs fe e E hyp epf goal'
  return .some (pf, [goal'.mvarId!], [])


def reg (s : String) : Atom PROP Valu := sorry
def regField (s : String) (f : String) : Atom PROP Valu := sorry
def regCol (rs : List (RegKind × ValuShape)) : Atom PROP Unit := sorry

inductive RegPtstoKind where
| reg (_ : Valu)
| regCol (_ : List (RegKind × ValuShape))

def regPtsto (s : String) : Atom PROP RegPtstoKind := Atom.mk λ
  | .reg v => reg s # v
  | .regCol regs => regCol regs # ()

inductive RegStructPtstoKind where
| reg (_ : Valu)
| regCol (_ : List (RegKind × ValuShape))

def regStructPtsto (s : String) (f : String) : Atom PROP RegStructPtstoKind := Atom.mk λ
  | .reg v => regField s f # v
  | .regCol regs => regCol regs # ()

@[irun]
theorem cancel_regPtsto_reg s v :
  cancelR (PROP:=PROP) (reg s # v) (regPtsto s) :- .pure (.reg v) := by mysorry

@[irun]
theorem cancel_regStructPtsto_reg s f v :
  cancelR (PROP:=PROP) (regField s f # v) (regStructPtsto s f) :- .pure (.reg v) := by mysorry


theorem cancel_regPtsto_regCol_tac regs s E P :
  (P ⊢ E (.regCol regs)) →
  P ⊢ cancelR (PROP:=PROP) (regCol regs # ()) (regPtsto s) E  := by mysorry

theorem cancel_regStructPtsto_regCol_tac regs s f E P :
  (P ⊢ E (.regCol regs)) →
  P ⊢ cancelR (PROP:=PROP) (regCol regs # ()) (regStructPtsto s f) E := by mysorry


@[irun_tac cancelR (regCol _ # _) (regPtsto _) _, cancelR (regCol _ # _) (regStructPtsto _ _) _]
def irunCancelRegCol : IRunTacticType := fun goal _config => do profileitM Exception "irunCancelRegCol" (← getOptions) do
  let ig := goal
  let { u, prop, bi, hyp, goal:=G } := ig

  let_expr cancelR _ _ _ A A' E := G | return none
  let_expr Atom.ref _ _ A _ := A | return none
  let_expr regCol _ regs := A | return none
  let some (cst, f, pf) := (match_expr A' with
    | regPtsto _ s =>
      match s with
      | .lit (.strVal ss) =>
        some (``RegPtstoKind.regCol,
        RegKind.reg ss,
        mkApp6 (.const ``cancel_regPtsto_regCol_tac [u]) prop bi regs s E hyp)
      | _ => none
    | regStructPtsto _ re f =>
      match re, f with
      | .lit (.strVal res), .lit (.strVal fs) =>
        some (``RegStructPtstoKind.regCol,
        RegKind.field res fs,
        mkApp7 (.const ``cancel_regStructPtsto_regCol_tac [u]) prop bi regs re f E hyp)
      | _, _ => none
    | _ => none) | return none
  let some _ ← lookupRegColExpr regs f | return none
  let res := mkApp (mkConst cst) regs
  let m ← mkFreshExprSyntheticOpaqueMVar <| IrisGoalShallow.toExpr { ig with goal := Expr.beta E #[res] }
  let pf := mkApp pf m
  return .some (pf, [m.mvarId!], [])


-- @[irun]
theorem cancel_regPtsto_regCol regs s :
  .reg s ∈ regs.map (·.1) →
  cancelR (PROP:=PROP) (regCol regs # ()) (regPtsto s) :- .pure (.regCol regs) := by mysorry

-- @[irun]
theorem cancel_regStructPtsto_regCol regs s f:
  .field s f ∈ regs.map (·.1) →
  cancelR (PROP:=PROP) (regCol regs # ()) (regStructPtsto s f) :- .pure (.regCol regs) := by mysorry

end regs

section spec

inductive Label where
| readMem (a : BitVec 64) (v : BitVecN)
| writeMem (a : BitVec 64) (v : BitVecN)
| instrTrap (pc : BitVec 64)

def Spec : Type := List Label → Prop

def Spec.nil : Spec := λ κs => κs = []
def Spec.cons (lb : Label) (P : Spec) : Spec := λ κs => κs = [] ∨ ∃ κs', κs' = lb::κs' ∧ (κs' = [] ∨ P κs')
def Spec.app (ls : List Label) (P : Spec) : Spec := ls.foldr Spec.cons P


def specTrace : Atom PROP Spec := sorry

def specConsOkR [BI PROP] (lb : Label) (P : Spec) (E : Spec → PROP) : PROP := sorry

@[irun_preprocess]
def specConsOk (lb : Label) (P : Spec) : Li PROP Spec where
  run := specConsOkR lb P
  mono' E1 E2 := by mysorry

@[irun]
theorem specConsOk_cons lb P lb' :
  specConsOkR (PROP:=PROP) lb (Spec.cons lb' P) :- do
    exhale (prop (lb = lb'))
    return P := by mysorry

end spec

section mem

def ptsto (a : BitVec 64) (n : Nat) : Atom PROP (BitVec n) := sorry
def array (a : BitVec 64) (n len : Nat) : Atom PROP (List (BitVec n)) := sorry
def uninit (a : BitVec 64) (len : Nat) : Atom PROP Unit := sorry
def mmio (a : BitVec 64) (len : Nat) : Atom PROP Unit := sorry

inductive MemPtstoKind where
| ptsto (n : Nat) (_ : BitVec n)
| array (a : BitVec 64) (n len : Nat) (_ : List (BitVec n))
| uninit (a : BitVec 64) (len : Nat)
| mmio (a : BitVec 64) (len : Nat)

def memPtsto (a : BitVec 64) : Atom PROP MemPtstoKind := Atom.mk λ
| .ptsto n v => ptsto a n # v
| .array a' n len vs => array a' n len # vs
| .uninit a' len => uninit a' len # ()
| .mmio a' len => mmio a' len # ()

@[irun:high]
theorem cancel_ptsto_memPtsto a n v :
  cancelR (PROP:=PROP) (ptsto a n # v) (memPtsto a) :- .pure (.ptsto n v) := by mysorry

@[irun]
theorem cancel_ptsto_memPtsto_solve a a' n v :
  a = a' →
  cancelR (PROP:=PROP) (ptsto a n # v) (memPtsto a') :- .pure (.ptsto n v) := by mysorry

@[irun]
theorem cancel_ptsto_ptsto_solve a a' n n' v :
  a = a' →
  cancelR (PROP:=PROP) (ptsto a n # v) (ptsto a' n') :- bitvecCastOk v n' := by mysorry

@[irun]
theorem cancel_mmio_memPtsto_solve a a' n v :
  a ≤ a' ∧ a' ≤ a + BitVec.ofNat 64 n →
  cancelR (PROP:=PROP) (mmio a n # v) (memPtsto a') :- .pure (.mmio a n) := by mysorry

end mem

section instr

def instr (a : BitVec 64) : Atom PROP (Option IslaTrace) := sorry

def instrPre'R [BI PROP] (isLater : Bool) (a : BitVec 64) (E : PROP) : PROP := sorry

@[irun_preprocess]
def instrPre' (isLater : Bool) (a : BitVec 64) (G : Li PROP Empty) : Li PROP Empty where
  run E := instrPre'R isLater a (G.run E)
  mono' E1 E2 := by mysorry

abbrev instrPre := @instrPre' PROP _ true
abbrev instrBody := @instrPre' PROP _ false

def instrPreA (a : BitVec 64) : Atom PROP PROP := Atom.mk λ E => instrPre'R true a E

@[irun]
theorem dualizing_instr_pre a P E :
  dualizingR (PROP:=PROP) (λ _ => instrPre'R true a P) E ⊣
    inhaleR (atom_with_ref (instrPreA a) P) E
 := by mysorry


inductive InstrKind PROP where
| instr (_ : Option IslaTrace)
| pre (_ : PROP)

def instrKind (a : BitVec 64) (pre : Bool) : Atom PROP (InstrKind PROP) := Atom.mk λ
  | .instr i => instr a # i
  | .pre P => if pre then instrPreA a # P else iprop(False)

@[irun]
theorem instrKind_instr a i pre :
  cancelR (PROP:=PROP) (instr a # i) (instrKind a pre) :- .pure (.instr i) := by mysorry

@[irun:low]
theorem instrKind_instr_solve a a' i pre:
  a = a' →
  cancelR (PROP:=PROP) (instr a # i) (instrKind a' pre) :- .pure (.instr i) := by mysorry

@[irun]
theorem instrKind_instrPre a P :
  cancelR (PROP:=PROP) (instrPreA a # P) (instrKind a true) :- .pure (.pre P) := by mysorry

@[irun:low]
theorem instrKind_instrPre_solve a a' P :
  a = a' →
  cancelR (PROP:=PROP) (instrPreA a # P) (instrKind a' true) :- .pure (.pre P) := by mysorry

@[irun]
theorem instr_pre_runa la a E :
  instrPre'R (PROP:=PROP) la a E ⊣ (
    (exhale (PROP:=PROP) (atom (instrKind a la))).bind λ
    | .instr (some t) =>
      (dualizing (fromEmpty λ _ => E)).bind λ _ =>
      (inhale (atom_with_ref (reg "_PC") (.base <| .bits a))).bind λ _ =>
      asmOk t
    | .instr (none) => fail "instr_pre instr none"
    | .pre P =>
      (dualizing (fromEmpty λ _ => E)).bind λ _ =>
      fromEmpty (λ _ => P)).go := by mysorry

-- TODO: generalize "_PC" to arch reg
@[irun]
theorem asmOk_nil :
  asmOkR (PROP:=PROP) .nil ⊣ (do
    let .base (.bits (.fromBitVec _ nPC)) ← exhale (atom (reg "_PC")) | fail "pc register is not bitvector"
    let nPC ← bitvecCastOk nPC 64
    (exhale (atom (instrKind (PROP:=PROP) nPC true))).bind λ
    | .instr (some t) => do
      (inhale (atom_with_ref (reg "_PC") (.base <| .bits nPC)))
      asmOk t
    | .instr none => do
      let P ← exhale (atom specTrace)
      let _ ← specConsOk (.instrTrap nPC) P
      done
    | .pre P =>
      fromEmpty (λ _ => P)).go := by mysorry

end instr

section exp

def unopOkR [BI PROP] (op : Unop) (v : BaseVal) (E : BaseVal → PROP) : PROP := sorry

@[irun_preprocess]
def unopOk (op : Unop) (v : BaseVal) : Li PROP BaseVal where
  run := unopOkR op v
  mono' E1 E2 := by mysorry

def binopOkR [BI PROP] (op : Binop) (v1 v2 : BaseVal) (E : BaseVal → PROP) : PROP := sorry

@[irun_preprocess]
def binopOk (op : Binop) (v1 v2 : BaseVal) : Li PROP BaseVal where
  run := binopOkR op v1 v2
  mono' E1 E2 := by mysorry

def manyopOkR [BI PROP] (op : Manyop) (vs : List BaseVal) (E : BaseVal → PROP) : PROP := sorry

@[irun_preprocess]
def manyopOk (op : Manyop) (vs : List BaseVal) : Li PROP BaseVal where
  run := manyopOkR op vs
  mono' E1 E2 := by mysorry


@[irun]
theorem unopOk_not b :
  unopOkR (PROP:=PROP) Unop.not (BaseVal.bool b) :-
    do return (.bool (¬ b)) := by mysorry
@[irun]
theorem unopOk_extract {n} (b : BitVec n) s e :
  unopOkR (PROP:=PROP) (Unop.extract e s) (BaseVal.bits b) :-
    do return (.bits (b.extractLsb' s (e + 1 - s))) := by mysorry
@[irun]
theorem unopOk_zeroExtend {n} (b : BitVec n) m :
  unopOkR (PROP:=PROP) (Unop.zeroExtend m) (BaseVal.bits b) :-
    do return (.bits (b.zeroExtend (m + n))) := by mysorry

@[irun]
theorem binopOk_eq_bits {n} (b1 b2 : BitVec n) :
  binopOkR (PROP:=PROP) (Binop.eq) (BaseVal.bits b1) (BaseVal.bits b2) :-
    do return (.bool (b1 = b2)) := by mysorry
@[irun]
theorem binopOk_eq_bool (b1 b2 : Bool) :
  binopOkR (PROP:=PROP) (Binop.eq) (BaseVal.bool b1) (BaseVal.bool b2) :-
    do return (.bool (b1 = b2)) := by mysorry

@[irun]
theorem manyopOk_bvand2 {n} (b1 b2 : BitVec n) :
  manyopOkR (PROP:=PROP) (Manyop.bvManyArith BvManyArith.bvand) [BaseVal.bits b1, BaseVal.bits b2] :-
    do return (.bits (b1 &&& b2)) := by mysorry
@[irun]
theorem manyopOk_bvor2 {n} (b1 b2 : BitVec n) :
  manyopOkR (PROP:=PROP) (Manyop.bvManyArith BvManyArith.bvor) [BaseVal.bits b1, BaseVal.bits b2] :-
    do return (.bits (b1 ||| b2)) := by mysorry
@[irun]
theorem manyopOk_bvadd2 {n} (b1 b2 : BitVec n) :
  manyopOkR (PROP:=PROP) (Manyop.bvManyArith BvManyArith.bvadd) [BaseVal.bits b1, BaseVal.bits b2] :-
    do return (.bits (b1 + b2)) := by mysorry
@[irun]
theorem manyopOk_concat2 {n1 n2} (b1 : BitVec n1) (b2 : BitVec n2) :
  manyopOkR (PROP:=PROP) (Manyop.concat) [BaseVal.bits b1, BaseVal.bits b2] :-
    do return (.bits (b1 ++ b2)) := by mysorry


@[irun]
theorem expOk_unop op e :
  expOkR (PROP:=PROP) (.unop op e) :- (do
    let v ← expOk e
    unopOk op v) := by mysorry
@[irun]
theorem aexpOk_unop op e :
  aexpOkR (PROP:=PROP) (.unop op e) :- (do
    let v ← aexpOk e
    unopOk op v) := by mysorry

@[irun]
theorem expOk_binop op e1 e2 :
  expOkR (PROP:=PROP) (.binop op e1 e2) :- (do
    let v1 ← expOk e1
    let v2 ← expOk e2
    binopOk op v1 v2) := by mysorry
@[irun]
theorem aexpOk_binop op e1 e2 :
  aexpOkR (PROP:=PROP) (.binop op e1 e2) :- (do
    let v1 ← aexpOk e1
    let v2 ← aexpOk e2
    binopOk op v1 v2) := by mysorry

@[irun]
theorem expOk_manyop2 op e1 e2 :
  expOkR (PROP:=PROP) (.manyop op [e1, e2]) :- (do
    let v1 ← expOk e1
    let v2 ← expOk e2
    manyopOk op [v1, v2]) := by mysorry
@[irun]
theorem aexpOk_manyop2 op e1 e2 :
  aexpOkR (PROP:=PROP) (.manyop op [e1, e2]) :- (do
    let v1 ← aexpOk e1
    let v2 ← aexpOk e2
    manyopOk op [v1, v2]) := by mysorry

@[irun]
theorem expOk_val v :
  expOkR (PROP:=PROP) (.val v) :- (do return v) := by mysorry

@[irun]
theorem aexpOk_var re :
  aexpOkR (PROP:=PROP) (.val <| .var re []) :- (do
    let k ← exhale (atom (regPtsto re))
    match k with
    | .reg v'@(.base v) =>
      inhale (atom_with_ref (reg re) v')
      return v
    | .regCol regs =>
      let s ← lookupRegColOk regs (.reg re)
      let v : Valu ← all
      hasShapeOk v s
      let .base v' := v | fail "variable is not BaseVal"
      inhale (atom_with_ref (regCol regs) ())
      return v'
    | _ => fail "register does not contain not BaseVal") := by mysorry

@[irun]
theorem aexpOk_bits b :
  aexpOkR (PROP:=PROP) (.val <| .bits b) :- (do return (.bits b)) := by mysorry
@[irun]
theorem aexpOk_bool b :
  aexpOkR (PROP:=PROP) (.val <| .bool b) :- (do return (.bool b)) := by mysorry
@[irun]
theorem aexpOk_enum b :
  aexpOkR (PROP:=PROP) (.val <| .enum b) :- (do return (.enum b)) := by mysorry


end exp

section events

@[irun:high]
theorem asmOk_cases1 t:
  asmOkR (PROP:=PROP) (.cases [t]) ⊣ (do asmOk t).go := by mysorry

@[irun]
theorem asmOk_cases_cons t ts:
  asmOkR (PROP:=PROP) (.cases (t::ts)) ⊣ (do
    branch
      (asmOk t)
      (asmOk (.cases ts))).go := by mysorry

@[irun]
theorem asmOk_readReg re v t:
  asmOkR (PROP:=PROP) (.cons (.readReg re [] v) t) ⊣ (do
   let rk ← exhale (atom (regPtsto re))
   match rk with
   | .reg v' =>
     inhale (prop (v = v'))
     inhale (atom_with_ref (reg re) v')
     asmOk t
   | .regCol regs =>
     let s ← lookupRegColOk regs (.reg re)
     inhale (atom_with_ref (regCol regs) ())
     hasShapeOk v s
     asmOk t
     ).go := by mysorry

@[irun]
theorem asmOk_readReg_struct re v f t:
  asmOkR (PROP:=PROP) (.cons (.readReg re [.field f] v) t) ⊣ (do
   let vread ← readAccessorOk [.field f] v
   let rk ← exhale (atom (regStructPtsto re f))
   match rk with
   | .reg v' =>
     inhale (prop (vread = v'))
     inhale (atom_with_ref (regField re f) v')
     asmOk t
   | .regCol regs =>
     let s ← lookupRegColOk regs (.field re f)
     inhale (atom_with_ref (regCol regs) ())
     hasShapeOk vread s
     asmOk t
     ).go := by mysorry

@[irun]
theorem asmOk_writeReg re v t:
  asmOkR (PROP:=PROP) (.cons (.writeReg re [] v) t) ⊣ (do
   let rk ← exhale (atom (regPtsto re))
   match rk with
   | .reg _ =>
     inhale (atom_with_ref (reg re) v)
     asmOk t
   | .regCol _regs =>
     -- TODO
     fail "asmOK_writeReg regCol"
     ).go := by mysorry


@[irun]
theorem asmOk_branchAddress a t:
  asmOkR (PROP:=PROP) (.cons (.branchAddress a) t) ⊣ asmOkR t := by mysorry

@[irun]
theorem asmOk_branch i s t:
  asmOkR (PROP:=PROP) (.cons (.branch i s) t) ⊣ asmOkR t := by mysorry

@[irun]
theorem asmOk_declareConst_bv v b t:
  asmOkR (PROP:=PROP) (.cons (.smt <| .declareConst v (.bitVec b)) t) ⊣ (do
   let n : BitVec b ← all
   asmOk (← substTraceOk (.bits n) v t)
     ).go := by mysorry
@[irun]
theorem asmOk_declareConst_bool v t:
  asmOkR (PROP:=PROP) (.cons (.smt <| .declareConst v .bool) t) ⊣ (do
   let n : Bool ← all
   asmOk (← substTraceOk (.bool n) v t)
     ).go := by mysorry
@[irun]
theorem asmOk_declareConst_enum v i t:
  asmOkR (PROP:=PROP) (.cons (.smt <| .declareConst v (.enum i)) t) ⊣ (do
   let n : SailName ← all
   asmOk (← substTraceOk (.enum n) v t)
     ).go := by mysorry

@[irun]
theorem asmOk_defineConst n e t:
  asmOkR (PROP:=PROP) (.cons (.smt <| .defineConst n e) t) ⊣ (do
   let v ← expOk e
   asmOk (← substTraceOk v n t)
     ).go := by mysorry


@[irun]
theorem asmOk_assert e t:
  asmOkR (PROP:=PROP) (.cons (.smt (.assert e)) t) ⊣ (do
    let .bool b ← expOk e | fail "assert does not return bool"
    inhale (prop (b))
    asmOk t).go := by mysorry

@[irun]
theorem asmOk_assume e t:
  asmOkR (PROP:=PROP) (.cons (.assume e) t) ⊣ (do
    let v ← aexpOk e
    exhale (prop (v = BaseVal.bool true))
    asmOk t).go := by mysorry

@[irun]
theorem asmOk_assumeReg re v t:
  asmOkR (PROP:=PROP) (.cons (.assumeReg re [] v) t) ⊣ (do
   let rk ← exhale (atom (regPtsto re))
   match rk with
   | .reg v' =>
     exhale (prop (v = v'))
     inhale (atom_with_ref (reg re) v')
     asmOk t
   | .regCol regs =>
     let s ← lookupRegColOk regs (.reg re)
     branch (do
       let v' ← all
       hasShapeOk v' s
       exhale (prop (v' = v))
       done) do
     inhale (atom_with_ref (regCol regs) ())
     asmOk t
     ).go := by mysorry

@[irun]
theorem asmOk_assumeRegField re f v t:
  asmOkR (PROP:=PROP) (.cons (.assumeReg re [.field f] v) t) ⊣ (do
   let rk ← exhale (atom (regStructPtsto re f))
   match rk with
   | .reg v' =>
     exhale (prop (v = v'))
     inhale (atom_with_ref (regField re f) v')
     asmOk t
   | .regCol regs =>
     let s ← lookupRegColOk regs (.field re f)
     exhale (prop (s = ValuShape.exact v))
     inhale (atom_with_ref (regCol regs) ())
     asmOk t
     ).go := by mysorry

@[irun]
theorem asmOk_readMem {n na} (vread : BitVec n) (a : BitVec na) kind len tag t :
  asmOkR (PROP:=PROP) (.cons (.readMem (.base <| .bits vread) kind (.base <| .bits a) len tag) t) ⊣ (do
   exhale (prop (n = 8 * len ∧ len ≠ 0))
   let a ← bitvecCastOk a 64
   let rk ← exhale (atom (memPtsto a))
   match rk with
   | .ptsto n' v =>
     let vread ← bitvecCastOk vread n'
     inhale (prop (vread = v))
     inhale (atom_with_ref (ptsto a n') v)
     asmOk t
   | .array a' n' len' vs =>
     exhale (prop ((a - a') % len = 0))
     let i := ((a - a') / len).toNat
     exhale (prop (i < len'))
     let vread ← bitvecCastOk vread n'
     inhale (prop (vread = vs[i]!))
     inhale (atom_with_ref (array a' n' len') vs)
     asmOk t
   | .uninit _a' _len => fail "readMem uninit"
   | .mmio _a' _len => fail "readMem mmio"
     ).go := by mysorry

@[irun]
theorem asmOk_writeMem {n na} (vnew : BitVec n) (a : BitVec na) success kind len tag t :
  asmOkR (PROP:=PROP) (.cons (.writeMem (.base <| .bool success) kind (.base <| .bits a) (.base <| .bits vnew) len tag) t) ⊣ (do
   exhale (prop (n = 8 * len ∧ len ≠ 0))
   let a ← bitvecCastOk a 64
   let rk ← exhale (atom (memPtsto a))
   match rk with
   | .ptsto n' _ =>
     exhale (prop (n' = n))
     inhale (atom_with_ref (ptsto a n) vnew)
     asmOk t
   | .array _a' _n _len _vs => fail "writeMem array"
   | .uninit _a' _len => fail "writeMem uninit"
   | .mmio a' len' =>
     exhale (prop (a' ≤ a ∧ a + len ≤ a' + len'))
     let Pκs ← exhale (atom (specTrace))
     let Pκs' ← specConsOk (.writeMem a vnew) Pκs
     inhale (atom_with_ref specTrace Pκs')
     asmOk t
     ).go := by mysorry


end events

end Islaris

namespace Islaris.Aarch64

-- instance : Coe BaseVal Valu where
--   coe := .base

--@[irun_solve]
abbrev sysRegs : List (RegKind × ValuShape) := [
  (.reg "SCTLR_EL1" , .exact (.base <| .bits 0x0000000004000002#64 )),
  (.reg "SCTLR_EL2" , .exact (.base <| .bits 0x0000000004000002#64 )),
  (.reg "SCR_EL3" , .exact (.base <| .bits 0x00000501#32 )),
  (.reg "TCR_EL2" , .exact (.base <| .bits 0#64 )),
  (.reg "HCR_EL2" , .exact (.base <| .bits 0x0000000080000000#64 )),
  (.reg "CFG_ID_AA64PFR0_EL1_EL0" , .exact (.base <| .bits 1#4 )),
  (.reg "CFG_ID_AA64PFR0_EL1_EL1" , .exact (.base <| .bits 1#4 )),
  (.reg "CFG_ID_AA64PFR0_EL1_EL2" , .exact (.base <| .bits 1#4 )),
  (.reg "CFG_ID_AA64PFR0_EL1_EL3" , .exact (.base <| .bits 1#4 )),
  (.reg "OSLSR_EL1" , .exact (.base <| .bits 0#32 )),
  (.reg "OSDLR_EL1" , .exact (.base <| .bits 0#32 )),
  (.reg "EDSCR" , .exact (.base <| .bits 0#32 )),
  (.reg "MPIDR_EL1" , .exact (.base <| .bits 0#64 )),
  (.reg "MDSCR_EL1" , .exact (.base <| .bits 0#32 )),
  (.reg "MDCR_EL2" , .exact (.base <| .bits 0#32 )),
  (.reg "MDCR_EL3" , .exact (.base <| .bits 0#32 )),
  (.field "PSTATE" "SP" , .exact (.base <| .bits 1#1 )),
  (.field "PSTATE" "EL" , .exact (.base <| .bits 2#2 )),
  (.field "PSTATE" "nRW" , .exact (.base <| .bits 0#1 )),
  (.field "PSTATE" "D" , .exact (.base <| .bits 1#1)),
  (.reg "__isla_monomorphize_writes", .exact (.base <| .bool false)),
  (.reg "__isla_monomorphize_reads", .exact (.base <| .bool false)),
  (.reg "__highest_el_aarch32", .exact (.base <| .bool false)),
  (.reg "__CNTControlBase", .exact (.base <| .bits 0#52)),
  (.reg "__v85_implemented", .exact (.base <| .bool false)),
  (.reg "__v84_implemented", .exact (.base <| .bool false)),
  (.reg "__v83_implemented", .exact (.base <| .bool false)),
  (.reg "__v82_implemented", .exact (.base <| .bool false)),
  (.reg "__v81_implemented", .exact (.base <| .bool true)),
  (.reg "__trickbox_enabled", .exact (.base <| .bool false))
]

-- example x :
--   List.find? (fun x : (_ × _) => x.fst == RegKind.reg "HCR_EL2") sysRegs = x := by
--   unfold sysRegs ; simp?


abbrev CNVZRegs : List (RegKind × ValuShape) := [
  (.field "PSTATE" "C", .bits 1),
  (.field "PSTATE" "N", .bits 1),
  (.field "PSTATE" "V", .bits 1),
  (.field "PSTATE" "Z", .bits 1)
]
end Islaris.Aarch64


namespace Islaris.InstrTest
open Lean Iris BI ProofMode Lithium Instructions Aarch64

variable {PROP} [BI PROP]

def ldrSpec (a : BitVec 64) : Li PROP Empty := do
  exhale (do
    atom_with_ref (reg "R1") (.base <| .bits 0x0000000000000008#64)
    let _ ← atom (reg "R0")
    atom_with_ref (ptsto 0x0000000000000008#64 64) (0x00000000deadbeef#64)
    atom_with_ref (regCol sysRegs) ())
  instrPre a (do
    exhale (do
      atom_with_ref (reg "R1") (.base <| .bits 0x0000000000000008#64)
      atom_with_ref (reg "R0") (.base <| .bits 0x00000000deadbeef#64)
      atom_with_ref (ptsto 0x0000000000000008#64 64) (0x00000000deadbeef#64)
      atom (regCol sysRegs))
    done)

-- #eval instr_ldr

--set_option profiler true in
--set_option trace.profiler true in
set_option Elab.async false in
#time example :
  ⊢ (do
    inhale (PROP:=PROP) (atom_with_ref (instr 0x0000000010300000#64) (some instr_ldr))
    instrBody (0x0000000010300000#64) (ldrSpec (0x0000000010300004#64))
    ).go := by
  unfold ldrSpec
  istart
  simp only [irun_preprocess]
  irun
  -- irun +debug 1
  -- mysorry

def strSpec (a : BitVec 64) : Li PROP Empty := do
  exhale (do
    atom_with_ref (reg "R1") (.base <| .bits 0x0000000000000008#64)
    atom_with_ref (reg "R9") (.base <| .bits 0x00000000cafebabe#64)
    atom_with_ref (ptsto 0x0000000000000008#64 64) (0x00000000deadbeef#64)
    atom_with_ref (regCol sysRegs) ())
  instrPre a (do
    exhale (do
      atom_with_ref (reg "R1") (.base <| .bits 0x0000000000000008#64)
      atom_with_ref (reg "R9") (.base <| .bits 0x00000000cafebabe#64)
      atom_with_ref (ptsto 0x0000000000000008#64 64) (0x00000000cafebabe#64)
      atom (regCol sysRegs))
    done)

set_option Elab.async false in
#time example :
  ⊢ (do
    inhale (PROP:=PROP) (atom_with_ref (instr 0x0000000010300000#64) (some instr_str))
    instrBody (0x0000000010300000#64) (strSpec (0x0000000010300004#64))
    ).go := by
  unfold strSpec
  istart
  simp only [irun_preprocess]
  irun
  -- irun +debug 1
  -- mysorry
