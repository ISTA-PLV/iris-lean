/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode
import Iris.Lithium.IRunAttr
import Iris.Lithium.IRun
import Iris.Lithium.Exp

/-
next steps:
- rename tactics and everything to a consistent name
- add support for ⌜P⌝ -∗ G
- add support for ⌜P⌝ ∗ G
- add support for lif where one cannot prove either side
- add syntax for Lithium goals
- look into performance
- figure out how to avoid dsimp in wpsubst
- define wp
- add more lithium connectives
- prove sorrys
- do more examples
- define a notation for the language
- look into namespaces and using export
-/

syntax:min term " ≫ " term:min1 : term
syntax:min term " ≫= " term:min1 : term

macro_rules
  | `($a ≫= $args) => `(.bind $a $args)
  | `($a ≫ $args) => `(.bind $a λ _ => $args)

namespace HBind
-- this does not really work
class HBind (α : outParam (Type u)) (mα : Type v) (nβ : Type w) where
  hbind : mα → (α → nβ) → nβ
class HPure (α : outParam (Type u)) (mα : Type v) where
  hpure : α → mα
end HBind

namespace Iris.Lithium
open Lean BI Std HBind

variable [BI.{u} PROP]

structure Atom (α : Type v) where
  ref : α → PROP

structure InExM (α : Type v) where
  body : α → PROP

structure LithiumM (α : Type v) where
  run : (α → PROP) → PROP
  mono' E1 E2 : ⊢ run E1 -∗ (∀ a, E1 a -∗ E2 a) -∗ run E2

namespace InExM

variable {α : Type v} {β : Type w}

def pure (a : α) : @InExM PROP α :=
  InExM.mk λ b => iprop(⌜a = b⌝)

def bind (L1 : @InExM PROP α) (L2 : α → @InExM PROP β) :
  @InExM PROP β :=
  InExM.mk λ b => iprop(∃ a, L1.body a ∗ (L2 a).body b)

instance : Monad (@InExM PROP) where
  pure := .pure
  bind := .bind

instance : HBind α (@InExM PROP α) (@InExM PROP β) where
  hbind := .bind
instance : HPure α (@InExM PROP α) where
  hpure := .pure

def atom (A : @Atom PROP α) : @InExM PROP α := InExM.mk A.ref
def own (P : PROP) : @InExM PROP Unit := .mk λ _ => iprop(P)
def ownP (P : PROP) : @InExM PROP PUnit := .mk λ _ => iprop(P)
def prop (P : Prop) : @InExM PROP Unit := own iprop(⌜P⌝)
def propP (P : Prop) : @InExM PROP PUnit := ownP iprop(⌜P⌝)

end InExM

namespace LithiumM

variable {α : Type v} {β : Type w}

def pure (a : α) : @LithiumM PROP _ α := {
  run E := E a
  mono' E1 E2 := by
    iintro HE Hwand
    iapply Hwand $$ HE
}

def bind (G1 : @LithiumM PROP _ α) (G2 : α → @LithiumM PROP _ β) :
  @LithiumM PROP _ β := {
  run E := G1.run (λ a => (G2 a).run E)
  mono' E1 E2 := by
    iintro HE Hwand
    sorry
}

instance : Monad (@LithiumM PROP _) where
  pure := .pure
  bind := .bind

instance : HBind α (@LithiumM PROP _ α) (@LithiumM PROP _ β) where
  hbind := .bind
instance : HPure α (@LithiumM PROP _ α) where
  hpure := .pure

def exhale (L : @InExM PROP α) : @LithiumM PROP _ α := {
  run E := iprop(∃ a, L.body a ∗ E a)
  mono' E1 E2 := by
    iintro ⟨%a, HL, HE⟩ Hwand
    iexists a
    isplitl [HL]
    · iassumption
    · iapply Hwand $$ HE
}

def inhale (L : @InExM PROP α) : @LithiumM PROP _ α := {
  run E := iprop(∀ a, L.body a -∗ E a)
  mono' E1 E2 := by
    iintro HE Hwand %a HL
    iapply Hwand
    iapply HE $$ HL
}

def all (α : Type v) : @LithiumM PROP _ α := {
  run E := iprop(∀ a, E a)
  mono' E1 E2 := by
    iintro HE Hwand %a
    iapply Hwand
    iapply HE
}

def done : @LithiumM PROP _ α := {
  run E := iprop(True)
  mono' E1 E2 := by
    iintro HE Hwand
    iassumption
}

def lif (P : Prop) (G1 G2 : @LithiumM PROP _ α) : @LithiumM PROP _ α := {
  run E := iprop((⌜P⌝ -∗ G1.run E) ∧ (⌜¬P⌝ -∗ G2.run E))
  mono' E1 E2 := by
    iintro HE Hwand
    sorry
}

def dsimp {α : Type _} [BI PROP] (_ : Lean.Name) (a : α) : @LithiumM PROP _ α := {
  run E := E a
  mono' E1 E2 := by
    sorry
}

def empty : Empty → PROP := λ e => nomatch e
def emptyP : PEmpty → PROP := λ e => nomatch e

def dualizing (G : @LithiumM PROP _ Empty) : @LithiumM PROP _ Unit := {
  run E := iprop(G.run empty -∗ E ⟨⟩)
  mono' E1 E2 := by
    iintro HE Hwand HG
    iapply Hwand
    iapply HE $$ HG
}

def dualizingP (G : @LithiumM PROP _ PEmpty) : @LithiumM PROP _ PUnit := {
  run E := iprop(G.run emptyP -∗ E ⟨⟩)
  mono' E1 E2 := by
    iintro HE Hwand HG
    iapply Hwand
    iapply HE $$ HG
}

-- TODO: What are good precedences?
notation:35 G:36 " ⇓ " E:35 => run G E
notation:35 G:36 " ⇓ " "!" => run G empty

def entails (G1 G2 : @LithiumM PROP _ α) : Prop :=
  ∀ E, G1.run E ⊢ G2.run E

--notation:25 G1:29 ":-" G2:25 => (entails G2 G1)
--set_option quotPrecheck false in -- TODO: Why is this necessary?
--notation:25 G1:29 ":-" G2:25 => (∀ E, (G2 ⇓ E ⊢ G1 ⇓ E))
notation:25 P:29 "⊣" Q:25 => (Q ⊢ P)

--notation:25 G1:29 ":-" G2:25 => (run! G2 ⊢ run! G1)

end LithiumM

@[irun]
theorem run_bind (G1 : @LithiumM PROP _ α) (G2 : α → LithiumM β)
  (E : β → PROP) :
   G1.bind G2 ⇓ E ⊣ (G1 ⇓ λ b => G2 b ⇓ E) := by
    simp [LithiumM.bind]

@[irun]
theorem run_pure (a : α) (E : α → PROP) :
   .pure a ⇓ E ⊣ E a := by
    simp [LithiumM.pure]

@[irun]
theorem exhale_bind (L1 : @InExM PROP α) (L2 : α → InExM β) E :
  .exhale (L1.bind L2) ⇓ E ⊣
    LithiumM.exhale L1 ⇓ λ a => LithiumM.exhale (L2 a) ⇓ E := by
    dsimp [bind, LithiumM.bind, LithiumM.exhale, LithiumM.run, InExM.bind, LithiumM.run]
    sorry

@[irun]
theorem inhale_bind (L1 : @InExM PROP α) (L2 : α → InExM β) E :
  .inhale (L1.bind L2) ⇓ E ⊣
   LithiumM.inhale L1 ⇓ λ a => .inhale (L2 a) ⇓ E := by
    dsimp [bind, LithiumM.bind, LithiumM.inhale, LithiumM.run, InExM.bind]
    sorry

@[irun]
theorem exhale_pure (a : α) E :
  .exhale (PROP:=PROP) (.pure a) ⇓ E ⊣ E a := by
    dsimp [bind, LithiumM.pure, LithiumM.exhale, LithiumM.run, InExM.pure]
    sorry

@[irun]
theorem inhale_pure (a : α) E :
  .inhale (PROP:=PROP) (.pure a) ⇓ E ⊣ E a := by
    dsimp [bind, LithiumM.pure, LithiumM.inhale, LithiumM.run, InExM.pure]
    sorry


def test_inexP (A : @Atom PROP (ULift.{u} Nat)) : @InExM PROP (ULift.{u} Bool) := do
  let n ← .atom A
  .ownP (A.ref n)
  return ULift.up (n.down == 1)

set_option pp.universes true

def test_inex (A : @Atom PROP Nat) : @InExM PROP Bool :=
  .atom A ≫= λ n =>
  .own (A.ref n) ≫
  .pure (n == 1)

def test_inexh (A : @Atom PROP Nat) : @InExM PROP Bool :=
  HBind.hbind (InExM.atom A) λ n =>
  HBind.hbind (InExM.own (A.ref n)) λ _ =>
  InExM.pure (n == 1)


def test_lithiumP (A : @Atom PROP (ULift.{u} Nat)) : @LithiumM PROP _ (ULift.{u} Bool) := do
  let b ← .exhale do
    let n ← .atom A
    return ULift.up (n.down == 1)
  .inhale do
    let n ← .atom A
    .propP (b.down = (n.down == 1))
    return ULift.up true


def test_lithium (A : @Atom PROP Nat) : @LithiumM PROP _ Bool := do
  (LithiumM.exhale <|
    .atom A ≫= λ n =>
    .pure (n == 1)) ≫= λ b =>
  LithiumM.inhale <|
    .atom A ≫= λ n =>
    .prop (b = (n == 1)) ≫
    .pure true

-- set_option pp.universes true

-- #check InExM.instHBind
-- #check LithiumM.instHBind

-- /--
-- error: typeclass instance problem is stuck, it is often due to metavariables
--   HBind.{0, u, u} Bool (LithiumM.{u, 0} Bool) (LithiumM.{u, 0} Bool)
-- -/
-- #guard_msgs in
-- def test_lithiumH (A : @Atom PROP Nat) : @LithiumM PROP _ Bool := do
--   HBind.hbind (LithiumM.exhale.{u} (α:=Bool) <|
--     HBind.hbind (InExM.atom A) λ n =>
--     HPure.hpure (n == 1)) λ b =>
--   LithiumM.inhale <|
--     HBind.hbind (InExM.atom A) λ n =>
--     HBind.hbind (InExM.prop (b = (n == 1))) λ _=>
--     HPure.hpure true

end Iris.Lithium

/-
namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std Lithium

theorem inhale_own_tac [BI PROP] {P A : PROP} (E : Unit → PROP)
  (h : P ∗ A ⊢ E ())
 : P ⊢ (LithiumM.inhale (.own A)) ⇓ E := by
    simp [LithiumM.run, LithiumM.inhale, InExM.own, InExM.body]
    sorry

@[irun_tac (LithiumM.inhale (InExM.own _)) ⇓ _]
def irunInhaleOwn : IRunTacticType := fun goal => do profileitM Exception "irunIntro" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop, bi, e, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let ~q(LithiumM.run (LithiumM.inhale (.own $A)) $E) := G | return none
  let ident ← `(binderIdent| _)
  let (b, A') := if A.isAppOfArity ``intuitionistically 3 then
      (q(true), A.getArg! 3)
    else
      (q(false), A)
  let goals ← IO.mkRef #[]
  let Q := q($E ())
  let pf ← iCasesCore bi hyps Q b A A' ⟨⟩ (.one ident) fun hyps => do
    let m ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps, goal:=Q }
    goals.modify (·.push m.mvarId!)
    return m
  let pf := q(@inhale_own_tac $prop $bi $e $A $E $pf)
  goal.assign pf
  return .some ((← goals.get).toList, [])

theorem cancel [BI PROP] {p : Bool} {P P' A : PROP} {E}
  (hP : P ⊣⊢ P' ∗ □?p A)
  (h : P' ⊢ E ())
 : P ⊢ LithiumM.exhale (.own A) ⇓ E := by
   sorry

@[irun_tac LithiumM.exhale (InExM.own _) ⇓ _]
def irunCancel : IRunTacticType := fun goal => do profileitM Exception "irunCancel" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop, bi, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let ~q(LithiumM.exhale (.own $A) ⇓ $E) := G | return none
  let some ⟨_inst, P', hyps, out, ty, b, _, pf⟩ ←
    hyps.removeG false fun _ _ _ ty => do
      -- logInfo m!"ty: ${ty}, A: ${A}"
      if ← isDefEq ty A then return some ty else return none
    | return none
  have : $ty =Q $A := ⟨⟩
  have : $out =Q iprop(□?$b $ty) := ⟨⟩
  let m : Q($P' ⊢ $E ()) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps := hyps, goal := q($E ()) }
  let pf := q(cancel $pf $m)
  goal.assign pf
  return .some ([m.mvarId!], [])

theorem done_tac {α : Type _} [BI PROP] (P : PROP) (E : α → PROP)
 : P ⊢ LithiumM.done ⇓ E := pure_intro .intro

--set_option pp.universes true

@[irun_tac LithiumM.done ⇓ _]
def irunDone : IRunTacticType := fun goal => do profileitM Exception "irunTrue" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop:=prop, bi:=bi, hyps:=_, e, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  match_expr G with
  | LithiumM.run _ _ α G E =>
    let .true := G.isAppOfArity ``LithiumM.done 3 | return none
    let pf := mkApp5 (.const ``done_tac G.getAppFn.constLevels!) prop α bi e E
    goal.assign pf
    return .some ([], [])
  | _ => return none


theorem lif_true {α : Type _} [BI PROP] {cond} {P : PROP} (G1 : LithiumM α) G2 E
  (h1 : cond)
  (h2 : P ⊢ G1 ⇓ E)
 : P ⊢ .lif cond G1 G2 ⇓ E :=
   sorry

theorem lif_false {α : Type _} [BI PROP] {cond} {P : PROP} (G1 : LithiumM α) G2 E
  (h1 : ¬ cond)
  (h2 : P ⊢ G2 ⇓ E)
 : P ⊢ .lif cond G1 G2 ⇓ E :=
   sorry

syntax "istepsolve" : tactic
macro_rules
  | `(tactic|istepsolve) => `(tactic|trivial)
--macro_rules
--  | `(tactic|istepsolve) => `(tactic|solve| simp)

@[irun_tac LithiumM.lif _ _ _ ⇓ _]
def irunLif : IRunTacticType := fun goal => do profileitM Exception "irunLif" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop, bi, e, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let ~q(LithiumM.lif $cond $G1 $G2 ⇓ $E) := G | return none

  let mcond : Q($cond) ← mkFreshExprSyntheticOpaqueMVar cond
  try
    let _ ← evalTacticAtRaw (← `(tactic|istepsolve)) mcond.mvarId!
    let m : Q($e ⊢ $G1 ⇓ $E) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps, goal := q($G1 ⇓ $E) }
    let pf := q(lif_true $G1 $G2 $E $mcond $m)
    goal.assign pf
    return .some ([m.mvarId!], [])
  catch _ => pure ()

  let mnegcond : Q(¬$cond) ← mkFreshExprSyntheticOpaqueMVar q(¬ $cond)
  try
    let _ ← evalTacticAt (← `(tactic|istepsolve)) mnegcond.mvarId!
    let m : Q($e ⊢ $G2 ⇓ $E) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps, goal := q($G2 ⇓ $E) }
    let pf := q(lif_false $G1 $G2 $E $mnegcond $m)
    goal.assign pf
    return .some ([m.mvarId!], [])
  catch _ => pure ()

  throwError "Cannot solve either side of lif"

@[irun_tac LithiumM.dsimp _ _ ⇓ _]
def irunSimp : IRunTacticType := fun goal => do profileitM Exception "irunSimp" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some ig := parseIrisGoal? g | throwError "not in proof mode"
  let { prop:=_, bi:=_, e:=_, hyps:=_, goal:=G } := ig

  let_expr LithiumM.run _ _ _ G E := G | return none
  let_expr LithiumM.dsimp _ _ _ n e := G | return none
  let n : Name ← reduceEval n
  let ⟨e_new, _⟩ ← goal.withContext (dsimpWithExt n e)
  let g' := {ig with goal := Expr.beta E #[e_new]}.toExpr
  let goal' := ← goal.replaceTargetDefEq g'
  return .some ([goal'], [])

section test
variable {u} [BI.{u} PROP]

theorem test1 (P : Nat → PROP) (Q : PROP) :
  ⊢ (.inhale (.own Q) ≫
      .inhale (.own (P 1)) ≫
      .inhale (.own (P 2)) ≫
      .inhale (.own iprop(⌜1 = 1⌝)) ≫
      .exhale (.own (P 1) ≫ .own (P 2)) ≫
      .exhale (.own Q) ≫
   .done) ⇓ ! := by
     istart
     irun ∞


theorem test_intro_cancel (P G : PROP) :
  ⊢ .inhale (.own P ≫ .own G) ⇓ λ _ =>
     .exhale (.own G) ⇓ λ _ =>
     .done ⇓ ! := by
    istart
    irun 1
    irun 1
    irun 1
    irun 1
    irun 1


--set_option profiler true in
--set_option profiler.threshold 1 in
set_option maxRecDepth 30000 in
#time theorem proof_cancel_2 (P : Nat → PROP) :
  ⊢ (List.foldl (λ G n => LithiumM.bind (.inhale (.own (P n))) λ _ => G)
    (List.foldl (λ G n => LithiumM.bind (.exhale (.own (P n))) λ _ => G) .done (
    -- List.reverse makes cancellation basically instant
    -- List.reverse
    (List.range 2)))
    (List.range 2)) ⇓ !
:=
  by
    dsimp [List.foldl, List.range, List.range.loop, List.reverse]
    istart
    -- set_option trace.profiler true in
    -- set_option trace.profiler.threshold 1 in
    irun ∞

--set_option profiler true in
--set_option profiler.threshold 1 in
set_option maxRecDepth 30000 in
#time theorem proof_cancel_3 (P : Nat → PROP) :
  ⊢ (List.foldl (λ G n => LithiumM.inhale (.own (P n)) ⇓ λ _ => G)
    (List.foldl (λ G n => LithiumM.exhale (.own (P n)) ⇓ λ _ => G)
      (.done ⇓ !) (
    -- List.reverse makes cancellation basically instant
    -- List.reverse
    (List.range 2)))
    (List.range 2))
:=
  by
    dsimp [List.foldl, List.range, List.range.loop, List.reverse]
    istart
    -- set_option trace.profiler true in
    -- set_option trace.profiler.threshold 1 in
    -- irun ∞
    sorry

end test

end Iris.ProofMode

namespace Iris.Examples
open Lang Lithium

variable {u} [BI.{u} PROP]

/- Proof automation begins here -/

def expr_ok (e : Exp) : @LithiumM PROP _ Val := {
  run := wp e
  mono' := wp_wand e
}

def expr_okP (e : Exp) : @LithiumM PROP _ (ULift.{u} Val) := {
  run E := wp e (λ v => E (ULift.up v))
  mono' := by sorry
}

/- problem: Monad is not fully universe polymorphic -/
def fn_specP (v : Val) (G : Val → @LithiumM PROP _ (Val → @LithiumM PROP _ PEmpty)) : PROP :=
  iprop(∀ (E : ULift.{u} Val → PROP) va,
  (do
    let L' : Val → LithiumM PEmpty ← G va
    let vr ← .all (ULift.{u} Val)
    LithiumM.dualizingP (L' vr.down)
    return vr) ⇓ E
  -∗
  wp (.app (.val v) (.val va)) λ v => E (ULift.up v))

-- set_option pp.universes true

def fn_spec (v : Val) (G : Val → @LithiumM PROP _ (Val → @LithiumM PROP _ Empty)) : PROP :=
  iprop(∀ E va,
  (.bind (G va) λ L' =>
   .bind (.all Val) λ vr =>
   .bind (.dualizing (L' vr)) λ _ =>
   .pure vr) ⇓ E
  -∗
  wp (.app (.val v) (.val va)) E)

def nat_ok (v : Val) : @LithiumM PROP _ Nat := {
  run E := iprop(∃ n, ⌜v = .nat n⌝ ∗ E n)
  mono' E1 E2 := by sorry
}

def recv_ok (v : Val) : @LithiumM PROP _ (Binder × Binder × Exp) := {
  run E := iprop(∃ f x e, ⌜v = .recv f x e⌝ ∗ E (f, x, e))
  mono' E1 E2 := by sorry
}

def subst_ok (x : Binder) (v : Val) (e : Exp) : @LithiumM PROP _ Exp := {
  run E := E (subst' x v e)
  mono' E1 E2 := by
    simp
    sorry
}

@[irun]
theorem nat_ok_nat (n : Nat) (E : Nat → PROP) :
  nat_ok (.nat n) ⇓ E ⊣ E n := by
  dsimp [nat_ok, LithiumM.run, LithiumM.run]
  iintro HP
  iexists _
  isplit
  · ipure_intro
    rfl
  · iassumption

@[irun]
theorem recv_ok_rec f x e (E : (Binder × Binder × Exp) -> PROP) :
  recv_ok (.recv f x e) ⇓ E ⊣ E (f, x, e) := by
  dsimp [recv_ok, LithiumM.run, LithiumM.run]
  iintro HP
  iexists _
  iexists _
  iexists _
  isplit
  · ipure_intro
    rfl
  · iassumption

@[irun]
theorem expr_ok_val v (E : Val -> PROP) :
  expr_ok (.val v) ⇓ E ⊣ E v := by sorry

@[irun]
theorem expr_ok_plus e1 e2 (E : Val -> PROP) :
  expr_ok (Exp.binop e1 .plus e2) ⇓ E ⊣
   expr_ok e1 ⇓ λ v1 =>
   expr_ok e2 ⇓ λ v2 =>
   nat_ok v1 ⇓ λ n1 =>
   nat_ok v2 ⇓ λ n2 =>
   .dsimp `irun_simp (n1 + n2) ⇓ λ n =>
   E (.nat n) := by sorry

@[irun]
theorem expr_ok_minus e1 e2 (E : Val -> PROP) :
  expr_ok (Exp.binop e1 .minus e2) ⇓ E ⊣
   expr_ok e1 ⇓ λ v1 =>
   expr_ok e2 ⇓ λ v2 =>
   nat_ok v1 ⇓ λ n1 =>
   nat_ok v2 ⇓ λ n2 =>
   .dsimp `irun_simp (n1 - n2) ⇓ λ n =>
   E (.nat n) := by sorry

@[irun]
theorem expr_ok_eq e1 e2 (E : Val -> PROP) :
  expr_ok (Exp.binop e1 .eq e2) ⇓ E ⊣
   expr_ok e1 ⇓ λ v1 =>
   expr_ok e2 ⇓ λ v2 =>
   nat_ok v1 ⇓ λ n1 =>
   nat_ok v2 ⇓ λ n2 =>
   .dsimp `irun_simp (if n1 == n2 then 1 else 0) ⇓ λ n =>
   E (.nat n) := by sorry

@[irun]
theorem expr_ok_rec f x e (E : Val -> PROP) :
  expr_ok (.rece f x e) ⇓ E ⊣ E (.recv f x e) := by sorry

@[irun]
theorem expr_ok_app e1 e2 (E : Val -> PROP) :
  expr_ok (.app e1 e2) ⇓ E ⊣
   expr_ok e2 ⇓ λ v2 =>
   expr_ok e1 ⇓ λ v1 =>
   recv_ok v1 ⇓ λ ⟨f, x, e'⟩ =>
   subst_ok x v2 e' ⇓ λ e =>
   subst_ok f (.recv f x e') e ⇓ λ e =>
   expr_ok e ⇓ E := by sorry

@[irun]
theorem expr_ok_if e1 e2 e3 (E : Val -> PROP) :
  (expr_ok e1 ⇓ λ v1 =>
   nat_ok v1 ⇓ λ n1 =>
   LithiumM.lif (n1 ≠ 0) (expr_ok e2) (expr_ok e3) ⇓ E) ⊢
  expr_ok (.ife e1 e2 e3) ⇓ E := by sorry


section
open Lean Elab Tactic Meta Qq BI Std ProofMode

@[irun_tac subst_ok _ _ _ ⇓  _]
def irunSubst : IRunTacticType := fun goal => do profileitM Exception "irunSubst" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some ig := parseIrisGoal? g | throwError "not in proof mode"
  let { prop:=_, bi:=_, e:=_, hyps:=_, goal:=G } := ig

  let .true := G.isAppOfArity ``LithiumM.run 5 | return none
  let G' := G.getArg! 3
  let E := G.getArg! 4
  let .true := G'.isAppOfArity ``subst_ok 5 | return none
  let some x := Reify.Binder.reify (G'.getArg! 2) | return none
  let v := G'.getArg! 3
  let e := Reify.reify (G'.getArg! 4)
  let e' := (Reify.subst' x v e).unreify
--  logInfo m!"{repr x}, {G'.getArg! 2}, e': {e'}"
  let g' := {ig with goal := Expr.beta E #[e']}.toExpr
--  let ⟨g', _⟩ ← goal.withContext (dsimpWithExt `irun_simp g')
  let goal' := ← goal.replaceTargetDefEq g'
  return .some ([goal'], [])

end

theorem expr_ok_test (P : Val -> PROP) :
  ⊢ .inhale (.own (P (.nat 10))) ⇓ λ _ =>
     expr_ok (.binop (.val (.nat 5)) .plus (.val (.nat 5))) ⇓ λ v =>
     .exhale (.own (P v)) ⇓ λ _ =>
     .done ⇓ ! := by
  istart
  irun 1
  irun 1
  irun 1
  irun 1
  irun 1
  irun 1
  irun 1
  irun 1
  irun 1


attribute [irun_simp] Nat.add_one_sub_one

set_option profiler true in
--set_option profiler.threshold 1 in
#time theorem expr_ok_test2 (P : Val -> PROP) :
   ⊢ .inhale (.own (P (.nat 0))) ⇓ λ _ =>
      expr_ok (.app (.val rec_fn) (.val (.nat 200))) ⇓ λ v =>
      .exhale (.own (P v)) ⇓ λ _ =>
      .done ⇓ ! := by
  istart
  unfold rec_fn
  --set_option trace.profiler true in
  --set_option trace.profiler.threshold 1 in
  --set_option diagnostics true in
  --set_option profiler true in
  irun ∞

end Iris.Examples
-/
