/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
--import Lean.Parser.Do
--import Lean.Elab.Do
--import Lean
import Iris.BI
import Iris.ProofMode
import Iris.Examples.IRunAttr
import Iris.Examples.IRun
import Iris.Examples.Exp

-- this avoids the warnings from sorry
axiom exfalso (P : Prop) : P
syntax "mysorry" : tactic
macro_rules
--| `(tactic|mysorry) => `(tactic|sorry)
| `(tactic|mysorry) => `(tactic|apply exfalso)

syntax:min term " ≫ " term:min1 : term
syntax:min term " ≫= " term:min1 : term

macro_rules
  | `($a ≫= $args) => `(.bind $a $args)
  | `($a ≫ $args) => `(.bind $a λ _ => $args)

/-
Next steps:
- add shelving for not solvable goals
- define a notation for the language
- add subsumption for when atoms do not match up directly as in cancelation
- add support for inhale (atom A) by rewriting to a ← all; inhale (atom_with_ref A a)
- add support for exhale (atom_with_ref A a) by rewriting to a' ← exhale (atom A); exhale (prop (a = a'))
- define wp
- add more lithium connectives
- prove sorrys
- do more examples
- look into namespaces and using export
-/

namespace Iris.ProofMode
open Lean Elab.Tactic Meta Qq BI

structure PartitionHyps {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop)) where
  (espatial : Q($prop)) (hypsspatial : Hyps bi espatial)
  (eintuit : Q($prop)) (hypsintuit : Hyps bi eintuit)
  (pf : Q($e ⊣⊢ $espatial ∗ □ $eintuit))
  deriving Inhabited

-- TODO: use the following similar to Hyps.split?
inductive PartitionHypsCore {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop)) where
  | none
  | spatial
  | intuit
  | main (_ : PartitionHyps bi e)

theorem partition_mk_emp [BI PROP] :
    emp (PROP:=PROP) ⊣⊢ emp ∗ □ emp :=
  sorry

theorem partition_mk_intuit [BI PROP] {P : PROP} :
    □ P ⊣⊢ emp ∗ □ □ P :=
  sorry

theorem partition_mk_spatial [BI PROP] {P : PROP} :
    P ⊣⊢ P ∗ □ emp :=
  sorry

theorem partition_mk_merge [BI PROP] {P Ps Pi Q Qs Qi : PROP}
  (hP : P ⊣⊢ Ps ∗ □ Pi)
  (hQ : Q ⊣⊢ Qs ∗ □ Qi) :
    P ∗ Q ⊣⊢ (Ps ∗ Qs) ∗ □ (Pi ∗ Qi) :=
  sorry

variable  {prop : Q(Type u)} (bi : Q(BI $prop)) in
def Hyps.partition : ∀ {e}, Hyps bi e → PartitionHyps bi e
  | _, .emp _ => ⟨_, .mkEmp bi, _, .mkEmp bi, q(partition_mk_emp)⟩
  | e, h@(.hyp _ _ _ p ty _) =>
   match matchBool p with
   | .inl _ =>
        have : $e =Q iprop(□ $ty) := ⟨⟩
        ⟨_, .mkEmp bi, _, h, q(partition_mk_intuit)⟩
   | .inr _ =>
        ⟨_, h, _, .mkEmp bi, q(partition_mk_spatial)⟩
  | _, .sep _ _ _ _ lhs rhs =>
    let ⟨_, spatl, _, intuitl, pfl⟩ := lhs.partition
    let ⟨_, spatr, _, intuitr, pfr⟩ := rhs.partition
    ⟨_, .mkSep spatl spatr, _, .mkSep intuitl intuitr, q(partition_mk_merge $pfl $pfr)⟩
end Iris.ProofMode


attribute [irun_preprocess] Pure.pure Bind.bind

namespace Iris.Lithium
open Lean BI Std

-- TODO: use something shorter than PROP? E.g. ℙ (\bbP) or Ω?
variable {PROP : Type u} [BI.{u} PROP] {α : Type v} {β : Type w}

structure Atom (PROP : Type u) (α : Type v) where
  ref : α → PROP

-- TODO: Better symbol?
-- TODO: What are good precedences here?
notation:90 A:90 " # " a:90 => (Atom.ref A a)
delab_rule Atom.ref
  | `($_ $A $a) => do ``($A # $a)

structure InEx (PROP : Type u) (α : Type v) where
  body : α → PROP

structure Li (PROP : Type u) [BI.{u} PROP] (α : Type v) where
  run : (α → PROP) → PROP
  mono' E1 E2 : ⊢ run E1 -∗ (∀ a, E1 a -∗ E2 a) -∗ run E2

-- This prevents printing mono := ...
-- TODO: Is this a good idea?
delab_rule Li.mk
  | `($_ $run $_) => do ``($run)

-- make Li.run semireducible instead of a projection that is always reduced
-- TODO: Do we want this?
--def Li.run := @Li.run'
--attribute [irun_preprocess] Li.run


section InEx

def InEx.pure (a : α) : InEx PROP α :=
  InEx.mk λ b => iprop(⌜a = b⌝)

def InEx.bind (L1 : InEx PROP α) (L2 : α → InEx PROP β) :
  InEx PROP β :=
  InEx.mk λ b => iprop(∃ a, L1.body a ∗ (L2 a).body b)

instance : Monad (InEx PROP) where
  pure := .pure
  bind := .bind

def atom (A : Atom PROP α) : InEx PROP α := InEx.mk A.ref
def atom_with_ref (A : Atom PROP α) (a : α) : InEx PROP Unit := .mk λ _ => iprop(A # a)
def prop (P : Prop) : InEx PROP Unit := .mk λ _ => iprop(⌜P⌝)
def pers (L : InEx PROP α) : InEx PROP α := .mk λ a => iprop(□ L.body a)
def persLi (G : Li PROP α) : InEx PROP Unit := .mk λ _ => iprop(□ G.run λ _ => iprop(True))

end InEx

@[irun_preprocess]
def Li.pure (a : α) : Li PROP α := {
  run E := E a
  mono' E1 E2 := by
    iintro HE Hwand
    ispecialize Hwand HE
    iassumption
}

@[irun_preprocess]
def Li.bind (G1 : Li PROP α) (G2 : α → Li PROP β) :
  Li PROP β := {
  run E := G1.run (λ a => (G2 a).run E)
  mono' E1 E2 := by
    iintro HE Hwand
    mysorry
}

instance : Monad (Li PROP) where
  pure := .pure
  bind := .bind

def empty : Empty → PROP := λ e => nomatch e

@[irun_preprocess]
def Li.go (G : Li PROP Empty) : PROP := G.run empty

def exhaleR (L : InEx PROP α) (E : α → PROP) : PROP :=
  iprop(∃ a, L.body a ∗ E a)

@[irun_preprocess]
def exhale (L : InEx PROP α) : Li PROP α := {
  run := exhaleR L
  mono' E1 E2 := by
    dsimp [exhaleR]
    iintro ⟨a, HL, HE⟩ Hwand
    iexists a
    isplit l [HL]
    iassumption
    ispecialize Hwand HE
    iassumption
}

def inhaleR (L : InEx PROP α) (E : α → PROP) : PROP :=
  iprop(∀ a, L.body a -∗ E a)

@[irun_preprocess]
def inhale (L : InEx PROP α) : Li PROP α := {
  run := inhaleR L
  mono' E1 E2 := by
    dsimp [inhaleR]
    iintro HE Hwand a HL
    ispecialize HE HL
    ispecialize Hwand HE
    iassumption
}

def cancelR (P : PROP) (A : Atom PROP α) (E : α → PROP) : PROP :=
  iprop(P -∗ ∃ a, A # a ∗ E a)

@[irun_preprocess]
def cancel (P : PROP) (A : Atom PROP α) : Li PROP α := {
  run := cancelR P A
  mono' E1 E2 := by
    dsimp [cancelR]
    mysorry
}

def allR {α : Type v} (E : α → PROP) : PROP :=
  iprop(∀ a, E a)

@[irun_preprocess]
def all {α : Type v} : Li PROP α := {
  run := @allR _ _ α
  mono' E1 E2 := by
    dsimp [allR]
    iintro HE Hwand a
    ispecialize HE a
    ispecialize Hwand HE
    iassumption
}

def doneR : PROP := iprop(True)

@[irun_preprocess]
def done : Li PROP α := {
  run E := doneR
  mono' E1 E2 := by
    dsimp [doneR]
    iintro HE Hwand
    iassumption
}

def branchR (E1 E2 : PROP) : PROP :=
  iprop(E1 ∧ E2)

@[irun_preprocess]
def branch (G1 G2 : Li PROP α) : Li PROP α := {
  run E := branchR (G1.run E) (G2.run E)
  mono' E1 E2 := by
    iintro HE Hwand
    mysorry
}

def lifR (P : Prop) (E1 E2 : PROP) : PROP :=
  iprop((⌜P⌝ -∗ E1) ∧ (⌜¬P⌝ -∗ E2))

@[irun_preprocess]
def lif (P : Prop) (G1 G2 : Li PROP α) : Li PROP α := {
  run E := lifR P (G1.run E) (G2.run E)
  mono' E1 E2 := by
    iintro HE Hwand
    mysorry
}

def dropSpatialR (G : PROP) : PROP :=
  iprop(□ G)

@[irun_preprocess]
def dropSpatial (G : Li PROP α) : Li PROP α := {
  run E := dropSpatialR (G.run E)
  mono' E1 E2 := by
    iintro HE Hwand
    mysorry
}

def simpR {α : Type _} [BI PROP] (_ : Lean.Name) (_dsimp : Bool) (a : α) (E : α → PROP) : PROP := E a

@[irun_preprocess]
def simp {α : Type _} [BI PROP] (n : Lean.Name) (dsimp : Bool) (a : α) : Li PROP α := {
  run := simpR n dsimp a
  mono' E1 E2 := by
    simp [simpR]
    mysorry
}

def dualizingR (G : (Empty → PROP) → PROP) (E : Unit → PROP) : PROP :=
  iprop(G empty -∗ E ⟨⟩)

@[irun_preprocess]
def dualizing (G : Li PROP Empty) : Li PROP Unit := {
  run := dualizingR G.run
  mono' E1 E2 := by
    dsimp [dualizingR]
    iintro HE Hwand HG
    ispecialize HE HG
    ispecialize Hwand HE
    iassumption
}

@[irun_preprocess]
def fromEmpty (G : (Empty → PROP) → PROP) : Li PROP Empty where
  run := G
  mono' E1 E2 := by
   have HE : (E1 = E2) := by ext x; nomatch x
   simp [HE]
   mysorry


notation:25 P:29 "⊣" Q:25 => (Q ⊢ P)
set_option quotPrecheck false in -- TODO: Why is this necessary?
notation:25 P:29 ":-" Q:25 => (∀ E, Li.run Q E ⊢ P E)

@[irun]
theorem exhale_bind (L1 : InEx PROP α) (L2 : α → InEx PROP β) :
  exhaleR (L1.bind L2) :-
    ((exhale L1).bind λ a => exhale (L2 a)) := by
    dsimp [exhaleR, InEx.bind]
    mysorry

@[irun]
theorem inhale_bind (L1 : InEx PROP α) (L2 : α → InEx PROP β) E :
  inhaleR (L1.bind L2) E ⊣
   inhaleR L1 λ a => inhaleR (L2 a) E := by
    dsimp [inhaleR, InEx.bind]
    mysorry

@[irun]
theorem exhale_pure (a : α) E :
  exhaleR (PROP:=PROP) (.pure a) E ⊣ E a := by
    dsimp [exhaleR, InEx.pure]
    mysorry

@[irun]
theorem inhale_pure (a : α) E :
  inhaleR (PROP:=PROP) (.pure a) E ⊣ E a := by
    dsimp [inhaleR, InEx.pure]
    mysorry

def test_inex (A : Atom PROP Nat) : InEx PROP Bool :=
  atom A ≫= λ n =>
  atom_with_ref A n ≫
  .pure (n == 1)

def test_lithium (A : Atom PROP Nat) : Li PROP Bool := do
  let b ← exhale do
    let n ← atom A
    return (n == 1)
  inhale do
    let n ← atom A
    prop (b = (n == 1))
    return true

def test_lithium2 (A : Atom PROP Nat) : Li PROP Bool := do
  (exhale <|
    atom A ≫= λ n =>
    .pure (n == 1)) ≫= λ b =>
  inhale <|
    atom A ≫= λ n =>
    prop (b = (n == 1)) ≫
    .pure true

end Iris.Lithium

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std Lithium

@[irun]
theorem inhale_atom [BI PROP] {α : Type _} A (E : α → PROP) :
   inhaleR (atom A) E ⊣ allR λ a => inhaleR (atom_with_ref A a) λ _ => E a :=
   by mysorry


theorem inhale_atom_with_ref_tac {α : Type _} [BI PROP] {P : PROP} (A : Atom PROP α) (a : α) (E : Unit → PROP)
  (_h : P ∗ A # a ⊢ E ())
 : P ⊢ (inhaleR (atom_with_ref A a)) E := by
    simp [inhaleR, atom_with_ref]
    mysorry

@[irun_tac (inhaleR (atom_with_ref _ _)) _]
def irunInhaleAtomWithRef : IRunTacticType := fun goal _config => do profileitM Exception "irunInhaleAtomWithRef" (← getOptions) do
  let { u, prop, bi, hyp, goal:=G } := goal
  let_expr inhaleR _ _ _ L E := G | return none
  let_expr atom_with_ref _ α A a := L | return none
  let .some ⟨e, hyps⟩ := parseHypsFromShallow? u prop bi hyp | return none
  let us := L.getAppFn'.constLevels!
  let ident ← `(binderIdent| _)
  let goals ← IO.mkRef #[]
  let Q := Expr.beta E #[mkConst ``Unit.unit]
  let A' := mkApp4 (.const ``Atom.ref us) prop α A a
  let pf ← iCasesCore bi hyps Q q(false) A' A' ⟨⟩ (.one ident) fun hyps => do
    let m ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { u, prop, bi, e:=_, hyps, goal:=Q }
    goals.modify (·.push m.mvarId!)
    return m
  let pf := mkApp8 (.const ``inhale_atom_with_ref_tac us) prop α bi e A a E pf
  return .some (pf, (← goals.get).toList, [])

theorem inhale_pers_atom_with_ref_tac {α : Type _} [BI PROP] {P : PROP} (A : Atom PROP α) (a : α) (E : Unit → PROP)
  (_h : P ∗ □ A # a ⊢ E ())
 : P ⊢ (inhaleR (pers (atom_with_ref A a))) E := by
    simp [inhaleR, atom_with_ref]
    mysorry

-- TODO: unify with irunInhaleAtomWithRef?
@[irun_tac (inhaleR (pers (atom_with_ref _ _))) _]
def irunInhalePersAtomWithRef : IRunTacticType := fun goal _config => do profileitM Exception "irunInhaleAtomWithRef" (← getOptions) do
  let { u, prop, bi, hyp, goal:=G } := goal
  let_expr inhaleR _ _ _ L E := G | return none
  let_expr pers _ _ _ L := L | return none
  let_expr atom_with_ref _ α A a := L | return none
  let .some ⟨e, hyps⟩ := parseHypsFromShallow? u prop bi hyp | return none
  let us := L.getAppFn'.constLevels!
  let ident ← `(binderIdent| _)
  let goals ← IO.mkRef #[]
  let Q := Expr.beta E #[mkConst ``Unit.unit]
  let A' := mkApp4 (.const ``Atom.ref us) prop α A a
  let A'' := mkApp3 (.const ``intuitionistically [u]) prop (mkApp2 (.const ``BI.toBIBase [u]) prop bi) A'
  let pf ← iCasesCore bi hyps Q q(true) A'' A' ⟨⟩ (.one ident) fun hyps => do
    let m ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { u, prop, bi, e:=_, hyps, goal:=Q }
    goals.modify (·.push m.mvarId!)
    return m
  let pf := mkApp8 (.const ``inhale_pers_atom_with_ref_tac us) prop α bi e A a E pf
  return .some (pf, (← goals.get).toList, [])

theorem inhale_prop_tac [BI PROP] φ (P : PROP) E
  (_h : φ → P ⊢ E ())
 : P ⊢ inhaleR (prop φ) E := by
   mysorry


-- TODO: There are really strange compiler bugs here. If this
-- definition is inline, lean crashes in files that import this one
-- and use irunInhaleProp. Using [noinline] does not help. Also
-- removing irunInhaleProp2, which is unused, causes the crash
def irunInhalePropCases (m : MVarId) (n : Name) : TacticM (List MVarId) :=
  m.withContext do
    let some d := (← getLCtx).findFromUserName? n | throwError "cannot find freshly generated name"
    let ty := d.type
    -- TODO: when to we want to call cases?
    unless ty.isEq || ty.isFalse || ty.isTrue do
      return [m]
    let r? ← observing? (m.cases d.fvarId)
    return r?.elim [m] (λ m => m.toList.map (·.mvarId))

def irunInhaleProp2 : IRunTacticType := fun goal _config => do profileitM Exception "irunInhaleProp" (← getOptions) do
  let { u, prop, bi, hyp, goal:=G } := goal
  let_expr inhaleR _ _ _ L E := G | return none
  let_expr prop _ _ φ := L | return none
  let n ← mkFreshUserName (.mkStr1 "h")
  let (pf, m) ← withLocalDeclD n φ fun x => do
    -- TODO: iintros has this, what does this do?
    -- addLocalVarInfo ref (← getLCtx) x α
    let m ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoalShallow.toExpr { u, prop, bi, hyp, goal := Expr.beta E #[mkConst ``Unit.unit]}
    let mbound ← mkLambdaFVars #[x] m
    let pf := mkApp6 (.const ``inhale_prop_tac [u]) prop bi φ hyp E mbound
    return (pf, m.mvarId!)
  let mvars ← irunInhalePropCases m n
  --let mvars := [m]
  return .some (pf, mvars, [])


@[irun_tac inhaleR (prop _) _]
def irunInhaleProp : IRunTacticType := fun goal _config => do profileitM Exception "irunInhaleProp" (← getOptions) do
  let { u, prop, bi, hyp, goal:=G } := goal
  let_expr inhaleR _ _ _ L E := G | return none
  let_expr prop _ _ φ := L | return none
  let n ← mkFreshUserName (.mkStr1 "h")
  let (pf, m) ← withLocalDeclD n φ fun x => do
    -- TODO: iintros has this, what does this do?
    -- addLocalVarInfo ref (← getLCtx) x α
    let m ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoalShallow.toExpr { u, prop, bi, hyp, goal := Expr.beta E #[mkConst ``Unit.unit]}
    let mbound ← mkLambdaFVars #[x] m
    let pf := mkApp6 (.const ``inhale_prop_tac [u]) prop bi φ hyp E mbound
    return (pf, m.mvarId!)
  let tac ← `(tactic|simp [*, irun_simp] at $(mkIdent n):ident)
  let res ← try
      evalTacticAtRaw tac m
    catch _e =>
      --logInfo m!"{e.toMessageData}"
      .pure [m]
  if res == [] then return .some (pf, [], [])
  let [m] := res | throwError "simp created too many subgoals"
  let mvars ← irunInhalePropCases m n
  return .some (pf, mvars, [])


@[irun]
theorem exhale_atom_with_ref [BI PROP] {α : Type _} (A : Atom PROP α) a (E : Unit → PROP) :
   exhaleR (atom_with_ref A a) E ⊣ exhaleR (atom A) λ a' => exhaleR (prop (a = a')) λ _ => E () :=
   by mysorry


theorem exhale_atom_direct_tac {α : Type _} [BI PROP] {p : Bool} {P P' : PROP} (A : Atom PROP α) (a : α) {E}
  (_hP : P ⊣⊢ P' ∗ □?p A # a)
  (_h : P' ⊢ E a)
 : P ⊢ exhaleR (atom A) E := by
   mysorry

@[match_pattern] def mkApp11 (f a b c d e₁ e₂ e₃ e₄ e₅ e₆ e₇ : Expr) := mkApp7 (mkApp4 f a b c d) e₁ e₂ e₃ e₄ e₅ e₆ e₇

@[irun_tac exhaleR (atom _) _]
def irunExhaleAtomDirect : IRunTacticType := fun goal _config => do profileitM Exception "irunExhaleAtomDirect" (← getOptions) do
  let {u, prop, bi, hyp, goal:=G} := goal
  let_expr exhaleR _ _ _ L E := G | return none
  let_expr atom _ α A := L | return none
  let .some ⟨e, hyps⟩ := parseHypsFromShallow? u prop bi hyp | return none
  let us := L.getAppFn'.constLevels!
  let some ⟨a, P', hyps, _out, _ty, b, _, pf⟩ ←
    hyps.removeG false fun _ _ _ ty => do
      let_expr Atom.ref _ _ A' a := ty | return none
      let eq ← withReducible <| isDefEq A' A
      -- logInfo m!"ty: {ty}, A: {A} / {repr A}, A': {A'} / {repr A'}, eq: {eq}"
      if eq then return some a else return none
    | return none
  let m ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { u, prop, bi, e:=_, hyps := hyps, goal := Expr.beta E #[a] }
  let pf := mkApp11 (.const ``exhale_atom_direct_tac us) prop α bi b e P' A a E pf m
  return .some (pf, [m.mvarId!], [])

theorem exhale_atom_cancel_tac {α : Type _} [BI PROP] {p : Bool} {P P' Q : PROP} (A : Atom PROP α) {E}
  (_hP : P ⊣⊢ P' ∗ □?p Q)
  (_h : P' ⊢ cancelR Q A E)
 : P ⊢ exhaleR (atom A) E := by
   mysorry

-- below default priority for direct cancelation since direct cancellation can be a lot faster
@[irun_tac:mid exhaleR (atom _) _]
def irunExhaleAtomCancel : IRunTacticType := fun goal config => do profileitM Exception "irunExhaleAtomCancel" (← getOptions) do
  let { u, prop, bi, hyp, goal:=G } := goal
  let_expr exhaleR _ _ _ L E := G | return none
  let_expr atom _ α A := L | return none
  let .some ⟨e, hyps⟩ := parseHypsFromShallow? u prop bi hyp | return none
  let hyp' := ← mkFreshExprMVar (.some prop)
  let us := L.getAppFn'.constLevels!
  let tree := irunExt.getState (← getEnv)
  let some ⟨(tacpf, goals, shelved), P', hyps, _out, ty, b, _, pf⟩ ←
    hyps.removeG false fun _ _ _ Q => do
      let ig' := { u, prop, bi, hyp := hyp', goal := mkApp6 (.const ``cancelR us) prop bi α Q A E }
      let .some (pf, goals, shelved) ← irunSearch config ig' tree | return none
      return (pf, goals, shelved)
    | return none
  hyp'.mvarId!.assign hyps.tm
  let pf := mkApp11 (.const ``exhale_atom_cancel_tac us) prop α bi b e P' ty A E pf tacpf
  return .some (pf, goals, shelved)

@[irun]
theorem cancel_match [BI PROP] {α : Type _} (A : Atom PROP α) a E :
  cancelR (A # a) A E ⊣ E a := by mysorry

@[irun]
theorem exhale_prop [BI PROP] P (E : Unit → PROP) :
   P →
   exhaleR (prop P) E ⊣ E () :=
   by mysorry

theorem exhale_prop_tac [BI PROP] (P : PROP) (φ : Prop) E
  (_hφ : φ)
  (_h : P ⊢ E ())
 : P ⊢ exhaleR (prop φ) E := by
   mysorry

@[irun_tac:low exhaleR (prop _) _]
def irunExhaleProp : IRunTacticType := fun goal _config => do profileitM Exception "irunExhaleProp" (← getOptions) do
  let { u, prop, bi, hyp, goal:=G } := goal
  let_expr exhaleR _ _ _ L E := G | return none
  let_expr prop _ _ P := L | return none
  let mP ← mkFreshExprSyntheticOpaqueMVar P
  let m ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoalShallow.toExpr { u, prop, bi, hyp, goal := Expr.beta E #[mkConst ``Unit.unit] }
  let pf := mkApp7 (.const ``exhale_prop_tac [u]) prop bi hyp P E mP m
  return .some (pf, [m.mvarId!], [mP.mvarId!])

@[irun]
theorem exhaleR_persLi (α : Type _) [BI PROP] (G : Li PROP α) :
  exhaleR (PROP:=PROP) (persLi G) :-
    branch ((dropSpatial G).bind λ _ => Lithium.done) (return ()) := by
  mysorry

theorem all_tac [BI PROP] {α : Type _} (P : PROP) E
  (_h : ∀ a : α, P ⊢ E a)
 : P ⊢ allR E := by
   mysorry

@[irun_tac allR _]
def irunAll : IRunTacticType := fun goal _config => do profileitM Exception "irunAll" (← getOptions) do
  let { u, prop, bi, hyp, goal:=G } := goal
  let_expr allR _ _ α E := G | return none
  -- TODO: can we generate better names?
  let n ← mkFreshUserName (.mkStr1 "x")
  let (pf, m) ← withLocalDeclD n α fun x => do
    -- addLocalVarInfo ref (← getLCtx) x α
    let m ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoalShallow.toExpr { u, prop, bi, hyp, goal := Expr.beta E #[x] }
    let mbound ← mkLambdaFVars #[x] m
    let pf := mkApp6 (.const ``all_tac G.getAppFn'.constLevels!) prop bi α hyp E mbound
    return (pf, m)
  return .some (pf, [m.mvarId!], [])

theorem done_tac [BI PROP] (P : PROP)
 : P ⊢ doneR := pure_intro .intro

@[irun_tac doneR]
def irunDone : IRunTacticType := fun goal _config => do profileitM Exception "irunDone" (← getOptions) do
  let { u:=_, prop, bi, hyp, goal:=G } := goal
  let .true := G.isAppOfArity ``doneR 2 | return none
  let pf := mkApp3 (.const ``done_tac G.getAppFn'.constLevels!) prop bi hyp
  return .some (pf, [], [])

theorem branch_tac [BI PROP] P (E1 E2 : PROP)
  (_ : P ⊢ E1)
  (_ : P ⊢ E2)
 : P ⊢ branchR E1 E2 := by
   simp [branchR]
   apply and_intro <;> trivial

@[irun_tac branchR _ _]
def irunBranch : IRunTacticType := fun goal _config => do profileitM Exception "irunBranch" (← getOptions) do
  let ig := goal
  let { u, prop, bi, hyp, goal:=G } := ig

  let_expr branchR _ _ E1 E2 := G | return none
  let m1 ← mkFreshExprSyntheticOpaqueMVar <| IrisGoalShallow.toExpr { ig with goal := E1 }
  let m2 ← mkFreshExprSyntheticOpaqueMVar <| IrisGoalShallow.toExpr { ig with goal := E2 }
  let pf := mkApp7 (.const ``branch_tac [u]) prop bi hyp E1 E2 m1 m2
  return .some (pf, [m1.mvarId!, m2.mvarId!], [])


@[irun]
theorem lif_true [BI PROP] {cond : Prop} (E1 E2 : PROP) :
   cond →
   lifR cond E1 E2 ⊣ E1  :=
   by mysorry

@[irun]
theorem lif_false [BI PROP] {cond : Prop} (E1 E2 : PROP) :
   ¬ cond →
   lifR cond E1 E2 ⊣ E2 :=
   by mysorry

@[irun:low]
theorem lif_branch [BI PROP] {cond : Prop} (E1 E2 : PROP) :
   lifR cond E1 E2 ⊣ branchR (inhaleR (prop cond) λ _ => E1) (inhaleR (prop (¬ cond)) λ _ => E2) :=
   by mysorry

theorem drop_spatial_tac [BI PROP] [BIAffine PROP] P Ps Pi (E : PROP)
  (_ : P ⊣⊢ Ps ∗ □ Pi)
  (_ : Pi ⊢ E)
 : P ⊢ dropSpatialR E := by
    mysorry

@[irun_tac dropSpatialR _]
def irunDropSpatial : IRunTacticType := fun goal _config => do profileitM Exception "irunDropSpatial" (← getOptions) do
  let { u, prop, bi, hyp, goal:=G } := goal
  let_expr dropSpatialR _ _ E := G | return none
  let .some ⟨e, hyps⟩ := parseHypsFromShallow? u prop bi hyp | return none
  let .some aff ← synthInstance? (mkApp2 (.const ``BIAffine [u]) prop bi) | throwError "cannot synthesize BIAffine"
  let ⟨es, _, ei, hypsi, pf⟩ := hyps.partition
  let m ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoalShallow.toExpr { u, prop, bi, hyp := hypsi.tm, goal := E }
  let pf := mkApp9 (.const ``drop_spatial_tac [u]) prop bi aff e es ei E pf m
  return .some (pf, [m.mvarId!], [])

@[irun_tac simpR _ _ _ _]
def irunSimp : IRunTacticType := fun goal _config => do profileitM Exception "irunSimp" (← getOptions) do
  let ig := goal
  let G := ig.goal

  let_expr simpR _ _ _ n dodsimp e E := G | return none
  let n : Name ← reduceEval n
  let dodsimp : Bool ← reduceEval dodsimp
  if dodsimp then
    let ⟨e_new, _⟩ ← dsimpWithExt n e
    let g' := {ig with goal := Expr.beta E #[e_new]}.toExpr
    let goal' ← mkFreshExprSyntheticOpaqueMVar g'
    let pf ← mkExpectedTypeHint goal' ig.toExpr
    return .some (pf, [goal'.mvarId!], [])
  else
    throwError "simp not implemented"

section test
variable [BI.{u} PROP]

example (P : Nat → Atom PROP Unit) (Q : Atom PROP Unit) :
  ⊢ (do
      inhale (PROP:=PROP) (atom_with_ref Q ())
      let n ← all
      let m ← all
      inhale (atom_with_ref (P n) ())
      inhale (atom_with_ref (P m) ())
      inhale (atom_with_ref (P 1) ())
      exhale do
        atom (P n)
        atom (P m)
        atom (P 1)
      exhale (atom Q)
      done).go := by
     istart
     simp only [irun_preprocess]
     irun 1
     irun 1
     irun 1
     irun 1
     irun 1
     irun 1
     irun 1
     irun 1
     irun 1
     irun ∞


example (P G : Atom PROP Unit) :
  ⊢ (do
      inhale (PROP := PROP) do
        atom_with_ref P ()
        atom_with_ref G ()
      exhale do
        atom G
      done).go := by
    istart
    simp only [irun_preprocess]
    irun 1
    irun 1
    irun 1
    irun 1
    irun 1

/-
not reversed:
- time with direct cancellation for 100: 659ms
- time with direct cancellation for 200: 2873ms
- time with generic cancellation for 100: 1461ms (when creating mvars: 10884ms)
- time with generic cancellation for 200: 5782ms (when creating mvars: 39206ms)
reversed:
- time is basically identical between the two versions
-/
--set_option profiler true in
--set_option profiler.threshold 1 in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
set_option Elab.async false in
-- set_option trace.profiler true in
-- set_option trace.IRun.step true in
#time example (P : Nat → Atom PROP Unit) :
  ⊢ inhaleR (List.foldl (λ G n => (atom_with_ref (P n) () ≫ G)) (.pure tt) (List.range 100)) λ _ =>
    (List.foldl (λ G n => exhaleR (atom (P n)) λ _ => G)
      (doneR) (
    -- List.reverse makes cancellation faster
    -- List.reverse
    (List.range 100)))

:=
  by
    -- set_option trace.profiler true in
    dsimp [List.foldl, List.range, List.range.loop, List.reverse]
    istart
    --set_option trace.profiler true in
    -- set_option trace.profiler.threshold 1 in
    irun ∞

end test

end Iris.ProofMode

namespace Iris.Examples
open Lang Lithium BI

variable [BI.{u} PROP]

/- Proof automation begins here -/

def expr_okR := @wp PROP _

@[irun_preprocess]
def expr_ok (e : Exp) : Li PROP Val := {
  run := expr_okR e
  mono' := wp_wand e
}

def app_okR (v1 v2 : Val) : (Val → PROP) → PROP := expr_okR (.app (.val v1) (.val v2))

@[irun_preprocess]
def app_ok (v1 v2 : Val) : Li PROP Val := {
  run := app_okR v1 v2
  mono' := wp_wand (.app (.val v1) (.val v2))
}

-- TODO: Make this an atom?
def natL (v : Val) : InEx PROP Nat := InEx.mk λ n => iprop(⌜v = .nat n⌝)
def pairL (v : Val) : InEx PROP (Val × Val) := InEx.mk λ p => iprop(⌜v = .pair p.1 p.2⌝)

def recv_okR (v : Val) (E : Binder → Binder → Exp → PROP) : PROP :=
  iprop(∃ f x e, ⌜v = .recv f x e⌝ ∗ E f x e)

@[irun_preprocess]
def recv_ok (v : Val) : Li PROP (Binder × Binder × Exp) := {
  run E := recv_okR v λ f x e => E (f, x, e)
  mono' E1 E2 := by mysorry
}

def subst_okR (x : Binder) (v : Val) (e : Exp) (E : Exp → PROP) : PROP :=
  E (subst' x v e)

@[irun_preprocess]
def subst_ok (x : Binder) (v : Val) (e : Exp) : Li PROP Exp := {
  run := subst_okR x v e
  mono' E1 E2 := by
    simp [subst_okR]
    mysorry
}

@[irun]
theorem natL_exhale_nat (n : Nat) (E : Nat → PROP) :
  exhaleR (natL (.nat n)) E ⊣ E n := by
  dsimp [exhaleR, natL]
  iintro HP
  iexists _
  isplit
  · ipure_intro
    rfl
  · iassumption

@[irun]
theorem natL_inhale_nat v :
  inhaleR (PROP:=PROP) (natL v) :- do
    let n ← all
    inhale (prop (v = .nat n))
    return n := by
  dsimp [inhaleR, natL]
  intro E
  iintro HP n Hn
  mysorry

@[irun]
theorem pairL_exhale_pair (v1 v2 : Val) (E : (Val × Val) → PROP) :
  exhaleR (pairL (.pair v1 v2)) E ⊣ E (v1, v2) := by
  dsimp [exhaleR, pairL]
  iintro HP
  iexists (_, _)
  isplit
  · ipure_intro
    rfl
  · iassumption

@[irun]
theorem pairL_inhale_pair v :
  inhaleR (PROP:=PROP) (pairL v) :- do
    let v1 ← all
    let v2 ← all
    inhale (prop (v = .pair v1 v2))
    return (v1, v2) := by
  dsimp [inhaleR, pairL]
  intro E
  iintro HP n Hn
  mysorry

@[irun]
theorem recv_okR_rec f x e (E : Binder → Binder → Exp -> PROP) :
  recv_okR (.recv f x e) E ⊣ E f x e := by
  dsimp [recv_okR]
  iintro HP
  iexists _
  iexists _
  iexists _
  isplit
  · ipure_intro
    rfl
  · iassumption

@[irun]
theorem expr_okR_val v (E : Val -> PROP) :
  expr_okR (.val v) E ⊣ E v := by mysorry

@[irun]
theorem expr_okR_plus e1 e2 :
  expr_okR (PROP:=PROP) (Exp.binop e1 .plus e2) :- do
   let n1 ← exhale (natL (← expr_ok e1))
   let n2 ← exhale (natL (← expr_ok e2))
   let n ← simp `irun_simp true (n1 + n2)
   return (Val.nat n) := by mysorry

@[irun]
theorem expr_okR_minus e1 e2 :
  expr_okR (PROP:=PROP) (Exp.binop e1 .minus e2) :- do
   let n1 ← exhale (natL (← expr_ok e1))
   let n2 ← exhale (natL (← expr_ok e2))
   let n ← simp `irun_simp true (n1 - n2)
   return (Val.nat n) := by mysorry

@[irun]
theorem expr_okR_eq e1 e2 :
  expr_okR (PROP:=PROP) (Exp.binop e1 .eq e2) :- do
   let n1 ← exhale (natL (← expr_ok e1))
   let n2 ← exhale (natL (← expr_ok e2))
   let n ← simp `irun_simp true (if n1 == n2 then 1 else 0)
   return (Val.nat n)
   := by mysorry

@[irun]
theorem expr_okR_rec f x e (E : Val -> PROP) :
  expr_okR (.rece f x e) E ⊣ E (.recv f x e) := by mysorry

@[irun]
theorem expr_okR_let x e1 e2 :
  expr_okR (PROP:=PROP) (.lete x e1 e2) :- do
   let v1 ← expr_ok e1
   let e2 ← subst_ok x v1 e2
   let v ← expr_ok e2
   return v
  := by mysorry

@[irun]
theorem expr_okR_app e1 e2 :
  expr_okR (PROP:=PROP) (.app e1 e2) :- do
   let v2 ← expr_ok e2
   let v1 ← expr_ok e1
   let v ← app_ok v1 v2
   return v
   -- let ⟨f, x, e'⟩ ← recv_ok (← expr_ok e1)
   -- let v ← expr_ok (← subst_ok f (.recv f x e') (← subst_ok x v2 e'))
   -- return v
  := by mysorry

@[irun]
theorem app_okR_recv f x e v2 :
  app_okR (PROP:=PROP) (.recv f x e) v2 :- do
   let v ← expr_ok (← subst_ok f (.recv f x e) (← subst_ok x v2 e))
   return v
  := by mysorry

@[irun]
theorem expr_okR_if e1 e2 e3 :
  expr_okR (.ife e1 e2 e3) :- (do
    let n1 ← exhale (natL (← expr_ok (PROP:=PROP) e1))
    lif (n1 ≠ 0) (expr_ok e2) (expr_ok e3))
   := by mysorry

@[irun]
theorem expr_okR_fst e :
  expr_okR (PROP:=PROP) (.fst e) :- do
   let v ← expr_ok e
   let (v1, _) ← exhale (pairL v)
   return v1 := by mysorry

@[irun]
theorem expr_okR_snd e :
  expr_okR (PROP:=PROP) (.snd e) :- do
   let v ← expr_ok e
   let (_, v2) ← exhale (pairL v)
   return v2 := by mysorry

@[irun]
theorem expr_okR_pair e1 e2 :
  expr_okR (PROP:=PROP) (.binop e1 .pair e2) :- do
   let v1 ← expr_ok e1
   let v2 ← expr_ok e2
   return (.pair v1 v2) := by mysorry


section
open Lean Elab Tactic Meta Qq BI Std ProofMode

@[irun_tac subst_okR _ _ _ _]
def irunSubst : IRunTacticType := fun goal _config => do profileitM Exception "irunSubst" (← getOptions) do
  let ig := goal
  let G := ig.goal

  let_expr subst_okR _ x v e E := G | return none
  let some x := Reify.Binder.reify x | return none
  let e := Reify.reify e
  let e' := (Reify.subst' x v e).unreify
  let g' := {ig with goal := Expr.beta E #[e']}.toExpr
  let goal' ← mkFreshExprSyntheticOpaqueMVar g'
  let pf ← mkExpectedTypeHint goal' ig.toExpr
  return .some (pf, [goal'.mvarId!], [])

end

example (P : Val -> Atom PROP Unit) :
  ⊢ (do
      inhale (atom_with_ref (P (.nat 10)) ())
      let v ← expr_ok (.binop (.val (.nat 5)) .plus (.val (.nat 5)))
      exhale (atom (P v))
      done).go := by
  istart
  simp only [irun_preprocess]
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

-- time: ~1700ms (when using trivial for irun_solve)
-- time: ~2559ms (when using simp for irun_solve)
-- time: ~3190ms (when using simp for irun_solve after updating to 4.19.0?)
-- set_option profiler true in
--set_option profiler.threshold 1 in
set_option Elab.async false in
--set_option trace.profiler true in
--set_option trace.profiler.threshold 5 in
--set_option trace.IRun.step true in
#time example (P : Val -> Atom PROP Unit) :
   ⊢ (do
        inhale (atom_with_ref (P (.nat 0)) ())
        let v ← expr_ok (.app (.val rec_fn) (.val (.nat 200)))
        exhale (atom (P v))
        done).go := by
  istart
  unfold rec_fn
  simp only [irun_preprocess]
  --set_option trace.profiler true in
  --set_option trace.profiler.threshold 1 in
  --set_option diagnostics true in
  --set_option profiler true in
  irun ∞


def fn_spec (v : Val) : Atom PROP ((α : Type w) × (Val → Li PROP α) × (α → Val → Li PROP Empty)) := Atom.mk λ ⟨_, Gpre, Gpost⟩ =>
  iprop(∀ E va,
  (Li.bind (Gpre va) λ a =>
   Li.bind all λ vr =>
   Li.bind (dualizing (Gpost a vr)) λ _ =>
   Li.pure vr).run E
  -∗
  wp (.app (.val v) (.val va)) E)

def fn_okR {α β : Type _} (v : Val) (Gpre : Val → Li PROP α) (Gpost : α → Val → Li PROP β) (E : β → PROP) : PROP :=
  iprop(∀ va E', (Gpre va).run E' -∗ wp (.app (.val v) (.val va)) (λ vr => iprop(∃ a, E' a ∗ (Gpost a vr).run E)))

@[irun_preprocess]
def fn_ok {α β : Type _} (v : Val) (Gpre : Val → Li PROP α) (Gpost : α → Val → Li PROP β) : Li PROP β where
  run := fn_okR v Gpre Gpost
  mono' E1 E2 := by mysorry

def fn_spec_inex (v : Val) : Atom PROP ((α : Type w) × (Val → InEx PROP α) × (α → Val → InEx PROP Unit)) :=
  Atom.mk λ ⟨α, Lpre, Lpost⟩ =>
    fn_spec v # ⟨α, λ va => exhale (Lpre va), λ a vr => (exhale (Lpost a vr)).bind λ _ => done⟩

theorem prove_fn_spec {α : Type _} v Gpre Gpost :
  fn_spec (PROP:=PROP) v # ⟨α, Gpre, Gpost⟩ ⊣ (fn_ok v Gpre Gpost).go := by
  mysorry

@[irun]
theorem fn_okR_recv α β f x e Gpre Gpost E :
  @fn_okR PROP _ α β (.recv f x e) Gpre Gpost E ⊣
   allR λ va =>
   allR λ v' =>
   allR λ Φ : Atom PROP α =>
   inhaleR (pers (atom_with_ref (fn_spec v') ⟨α, Gpre, λ a vr => (Gpost a vr).bind λ _ => done⟩)) λ _ =>
   -- simpR `irun_preprocess true ((Gpre va).run) λ Gpre' =>
   ((Gpre va).run) |> λ Gpre' =>
   dualizingR (λ _ => Gpre' λ a => exhaleR (atom_with_ref Φ a) λ _ => doneR) λ _ =>
   subst_okR x va e λ e =>
   subst_okR f v' e λ e =>
   -- TODO make this something like app ok such that one can use
   -- subtyping from other function specs? Needs care with the
   -- recursive assumption
   expr_okR e λ vr =>
   exhaleR (atom Φ) λ a =>
   -- simpR `irun_preprocess true ((Gpost a vr).run) λ Gpost =>
   ((Gpost a vr).run) |> λ Gpost =>
   Gpost E := by mysorry

@[irun:mid] -- This should be tried after the .recv version
theorem fn_okR_subsume (α β : Type _) v Gpre Gpost E :
  @fn_okR PROP _ α β v Gpre Gpost E ⊣
   exhaleR (atom (fn_spec v)) λ ⟨_, Gpre2, Gpost2⟩ =>
   allR λ va =>
   allR λ Φpre : Atom PROP α =>
   dualizingR (λ _ => (Gpre va).run λ a => exhaleR (atom_with_ref Φpre a) λ _ => doneR) λ _ =>
   (Gpre2 va).run λ c =>
   exhaleR (atom Φpre) λ a =>
   allR λ vr =>
   dualizingR ((Gpost2 c vr).run) λ _ =>
   (Gpost a vr).run E
    := by mysorry

-- should be applied after the inlining rule
@[irun:low]
theorem app_okR_spec v1 v2 :
  app_okR (PROP:=PROP) v1 v2 :-
   (exhale (atom (fn_spec v1))).bind λ ⟨_, Gpre, Gpost⟩ =>
   (Gpre v2).bind λ a =>
   all.bind λ vr =>
   (dualizing (Gpost a vr)).bind λ _ =>
   Li.pure vr
  := by mysorry

/-
theorem prove_fn_spec_inex {α : Type _} v Lpre Lpost :
  (fn_spec_inex (PROP:=PROP) v).ref ⟨α, Lpre, Lpost⟩ ⊣ (do
     all.bind λ va =>
     all.bind λ v' =>
     (inhale (Lpre va)).bind λ a =>
     (inhale (atom_with_ref (fn_spec_inex v') ⟨α, Lpre, Lpost⟩)).bind λ _ =>
     (recv_ok v).bind λ ⟨f, x, e⟩ =>
     (subst_ok x va e).bind λ e =>
     (subst_ok f v' e).bind λ e =>
     (expr_ok e).bind λ vr =>
     (exhale (Lpost a vr)).bind λ _ =>
     done).go := by
  mysorry

theorem app_okR_inex v1 v2 :
  app_okR (PROP:=PROP) v1 v2 :-
   (exhale (atom (fn_spec_inex v1))).bind λ ⟨_, Lpre, Lpost⟩ =>
   (exhale (Lpre v2)).bind λ a =>
   (all).bind λ vr =>
   (inhale (Lpost a vr)).bind λ _ =>
   Li.pure vr
  := by mysorry
-/

@[irun]
theorem dualizing_exhale α (L : InEx PROP α) (G : (Empty → PROP) → α → PROP) E :
  dualizingR (PROP:=PROP) (λ E => exhaleR L (G E)) E ⊣
   inhaleR L λ a =>
   dualizingR (λ E => G E a) E := by mysorry

@[irun]
theorem dualizing_inhale α (L : InEx PROP α) (G : (Empty → PROP) → α → PROP) E :
  dualizingR (PROP:=PROP) (λ E => inhaleR L (G E)) E ⊣
   exhaleR L λ a =>
   dualizingR (λ E => G E a) E := by mysorry

@[irun]
theorem dualizing_done E :
  dualizingR (PROP:=PROP) (λ _ => doneR) E ⊣ E () := by mysorry

@[irun]
theorem dualizing_fn_ok α β E v Gpre Gpost (G : _ → _) :
  dualizingR (PROP:=PROP) (λ E => @fn_okR PROP _ α β v Gpre Gpost (G E)) E ⊣
    inhaleR (atom_with_ref (fn_spec v) ⟨_, Gpre, λ a vr => (Gpost a vr).bind λ b => fromEmpty (λ E => G E b)⟩) E
 := by mysorry

-- TODO: Allow G E instead of just E in the continuation for fn_okR?
@[irun]
theorem inhale_persLi_fn_ok α β E v Gpre Gpost (hmono : ∀ _ _, ⊢ _) :
  inhaleR (PROP:=PROP)
    (persLi (Li.mk (λ E => @fn_okR PROP _ α β v Gpre Gpost E) hmono)) E ⊣
    inhaleR (pers (atom_with_ref (fn_spec v) ⟨_, Gpre, λ a vr => (Gpost a vr).bind λ _ => done⟩)) E
 := by mysorry

example :
  ⊢ fn_spec (PROP:=PROP) rec_fn # ⟨Nat, λ va => exhale (natL va), λ _ _ => done⟩ := by
  --istart
  unfold rec_fn
  --simp [fn_spec_inex]
  apply (BI.BIBase.Entails.trans _ (prove_fn_spec _ _ _))
  istart
  simp only [irun_preprocess]
  irun

def getc_fn : Val := .recv .anon .anon (.val (.nat 1))
def putc_fn : Val := .recv .anon .anon (.val (.nat 1))
def echo_fn : Val := .recv .anon .anon (.lete "x" (.app (.val getc_fn) (.val (.nat 0))) (.app (.val putc_fn) (.var "x")))
def main_fn : Val := .recv .anon .anon (.app (.val echo_fn) (.val (.nat 0)))

def echo_spec PROP [BI PROP] : PROP :=
  fn_spec echo_fn # ⟨_,
     λ _ => do
      fn_ok getc_fn
        (λ _ => .pure ())
         λ _ vr => do
      fn_ok putc_fn
        (λ va => exhale (prop (va = vr)))
         λ _ vrp => .pure vrp,
     λ vrp vr => do exhale (prop (vrp = vr)); done ⟩

theorem echo_ok :
  ⊢ echo_spec PROP := by
  unfold echo_spec echo_fn
  apply (BI.BIBase.Entails.trans _ (prove_fn_spec _ _ _))
  istart
  simp only [irun_preprocess]
  irun

theorem main_ok [BIAffine PROP] :
  echo_spec PROP ⊢ (fn_spec main_fn) # ⟨_, λ _ => .pure (), λ _ vr => do exhale (prop (vr = .nat 1)); done⟩ := by
  unfold echo_spec main_fn getc_fn putc_fn
  apply (BI.BIBase.Entails.trans _ (prove_fn_spec _ _ _))
  istart
  iintro x
  simp only [irun_preprocess]
  irun

def fib_fn : Val := .recv "f" "x" <|
  .ife (.binop (.var "x") .eq (.val (.nat 0)))
    (.val (.nat 0)) <|
  .ife (.binop (.var "x") .eq (.val (.nat 1)))
    (.val (.nat 1)) <|
   .binop (.app (.var "f") (.binop (.var "x") .minus (.val (.nat 1)))) .plus
     (.app (.var "f") (.binop (.var "x") .minus (.val (.nat 2))))

@[irun_solve]
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+1+1 => fib n + fib (n + 1)

theorem fib_ok [BIAffine PROP] :
  ⊢ (fn_spec (PROP:=PROP) fib_fn) # ⟨_,
    λ va => do {let n ← exhale (natL va); exhale (prop (0 ≤ n)); return n},
    λ n vr => do {let nr ← exhale (natL vr); exhale (prop (nr = fib n)); done}⟩ := by
  unfold fib_fn
  apply (BI.BIBase.Entails.trans _ (prove_fn_spec _ _ _))
  istart
  simp only [irun_preprocess]
  irun
  · rename Nat => x
    cases x using fib.fun_cases <;> simp [fib] at * <;> omega


def ptsto (v : Val) : Atom PROP Val := sorry

@[irun]
theorem expr_okR_alloc :
  expr_okR (PROP:=PROP) .alloc :- do
    let v ← all
    inhale (atom_with_ref (ptsto v) (.nat 0))
    return v := by mysorry

@[irun]
theorem expr_okR_store e1 e2 :
  expr_okR (PROP:=PROP) (.store e1 e2) :- do
    let v2 ← expr_ok e2
    let v1 ← expr_ok e1
    let _ ← exhale (atom (ptsto v1))
    inhale (atom_with_ref (ptsto v1) v2)
    return v2 := by mysorry

@[irun]
theorem expr_okR_load e :
  expr_okR (PROP:=PROP) (.load e) :- do
    let v ← expr_ok e
    let vl ← exhale (atom (ptsto v))
    inhale (atom_with_ref (ptsto v) vl)
    return vl := by mysorry

def ptsto_test : Exp :=
  .lete "l" (.alloc) <|
  .lete .anon (.store (.var "l") (.load (.var "l"))) <|
  .var "l"

example :
  ⊢ (do
    let v ← expr_ok (PROP:=PROP) ptsto_test
    let vl ← exhale (atom (ptsto v) >>= natL)
    exhale (prop (0 ≤ vl))
    done).go := by
  istart
  simp [irun_preprocess, ptsto_test]
  irun

def NULL : Val := .nat 0

def is_list (v : Val) : Atom PROP (List Val) := sorry

@[irun]
theorem exhaleR_is_list_NULL :
  exhaleR (PROP:=PROP) (atom (is_list NULL)) :- return [] := by mysorry

@[irun]
theorem cancel_ptsto_list v x :
  cancelR (PROP:=PROP) (ptsto v # x) (is_list v) :- do
    let (v1, v2) ← exhale (pairL x)
    let xs ← exhale (atom (is_list v2))
    return v1 :: xs := by mysorry

@[irun]
theorem cancel_list_ptsto v xs :
  cancelR (PROP:=PROP) (is_list v # xs) (ptsto v) :- do
    exhale (prop (0 < xs.length))
    let v' ← all
    let x ← all
    let xs' ← inhale (atom (is_list v'))
    inhale (prop (xs = x::xs'))
    return .pair x v' := by mysorry


def is_null (v : Val) : Atom PROP Bool := sorry

-- TODO: handle this with binop ok to allow proper overloading
@[irun:high]
theorem expr_okR_eq_NULL e1 :
  expr_okR (PROP:=PROP) (Exp.binop e1 .eq (.val NULL)) :- do
   let b ← exhale (atom (is_null (← expr_ok e1)))
   return (Val.nat (if b then 1 else 0))
   := by mysorry

@[irun]
theorem cancel_is_null_ptsto v v' :
  cancelR (PROP:=PROP) (ptsto v # v') (is_null v) :- do
    inhale (atom_with_ref (ptsto v) v')
    return false := by mysorry

@[irun]
theorem cancel_is_null_list v xs :
  cancelR (PROP:=PROP) (is_list v # xs) (is_null v) :- do
    inhale (atom_with_ref (is_list v) xs)
    return xs.isEmpty := by mysorry


def empty_fn : Val := .recv .anon .anon (.val NULL)
def cons_fn : Val := .recv .anon "a" <|
  .lete "v" (.fst (.var "a")) <|
  .lete "l" (.snd (.var "a")) <|
  .lete "new_l" (.alloc) <|
  .lete .anon (.store (.var "new_l") (.binop (.var "v") .pair (.var "l"))) <|
  .var "new_l"

def mklist_fn : Val := .recv .anon .anon <|
  .lete "l" (.app (.val empty_fn) (.val (.nat 0))) <|
  .lete "l" (.app (.val cons_fn) (.binop (.val (.nat 1)) .pair (.var "l"))) <|
  .lete "l" (.app (.val cons_fn) (.binop (.val (.nat 2)) .pair (.var "l"))) <|
  .var "l"

theorem empty_ok [BIAffine PROP] :
  ⊢ fn_spec (PROP:=PROP) empty_fn # ⟨_,
    λ _ => do {return ()},
    λ _ vr => do {let vs ← exhale (atom (is_list vr)); exhale (prop (vs = [])); done}⟩ := by
  unfold empty_fn
  apply (BI.BIBase.Entails.trans _ (prove_fn_spec _ _ _))
  istart
  simp only [irun_preprocess]
  irun

theorem cons_ok [BIAffine PROP] :
  ⊢ (fn_spec (PROP:=PROP) cons_fn) # ⟨_,
    λ va => do {let (x, v) ← exhale (pairL va); let xs ← exhale (atom (is_list v)); return (x, xs)},
    λ (x, xs) vr => do {let vs ← exhale (atom (is_list vr)); exhale (prop (vs = x::xs)); done}⟩ := by
  unfold cons_fn
  apply (BI.BIBase.Entails.trans _ (prove_fn_spec _ _ _))
  istart
  simp only [irun_preprocess]
  irun

theorem mklist_ok [BIAffine PROP] :
  □ fn_spec (PROP:=PROP) empty_fn # ⟨_,
    λ _ => do {return ()},
    λ _ vr => do {let vs ← exhale (atom (is_list vr)); exhale (prop (vs = [])); done}⟩ ∗
  □ fn_spec (PROP:=PROP) cons_fn # ⟨_,
    λ va => do {let (x, v) ← exhale (pairL va); let xs ← exhale (atom (is_list v)); return (x, xs)},
    λ (x, xs) vr => do {let vs ← exhale (atom (is_list vr)); exhale (prop (vs = x::xs)); done}⟩
  ⊢ fn_spec (PROP:=PROP) mklist_fn # ⟨_,
    λ _ => do {return ()},
    λ _ vr => do {let vs ← exhale (atom (is_list vr)); exhale (prop (vs = [.nat 2, .nat 1])); done}⟩ := by
  unfold mklist_fn
  apply (BI.BIBase.Entails.trans _ (prove_fn_spec _ _ _))
  istart
  iintro ⟨□ h1, □ h2⟩
  simp only [irun_preprocess]
  irun


def head_fn : Val := .recv .anon "l" (.fst (.load (.var "l")))

theorem head_ok :
  ⊢ fn_spec (PROP:=PROP) head_fn # ⟨_,
    λ va => do {let xs ← exhale (atom (is_list va)); exhale (prop (0 < xs.length)); return (va, xs)},
    λ (va, xs) vr => do {exhale (atom_with_ref (is_list va) xs); exhale (prop (xs.head? = some vr)); done}⟩ := by
  unfold head_fn
  apply (BI.BIBase.Entails.trans _ (prove_fn_spec _ _ _))
  istart
  simp only [irun_preprocess]
  irun

def length_fn : Val := .recv "f" "l" <|
  .ife (.binop (.var "l") .eq (.val NULL))
    (.val (.nat 0)) <|
  .lete "r" (.app (.var "f") (.snd (.load (.var "l")))) <|
  .binop (.var "r") .plus (.val (.nat 1))

theorem length_ok :
  ⊢ fn_spec (PROP:=PROP) length_fn # ⟨_,
    λ va => do {let xs ← exhale (atom (is_list va)); return (va, xs)},
    λ (va, xs) vr => do {exhale (atom_with_ref (is_list va) xs); exhale (prop (vr = .nat xs.length)); done}⟩ := by
  unfold length_fn
  apply (BI.BIBase.Entails.trans _ (prove_fn_spec _ _ _))
  istart
  simp only [irun_preprocess]
  irun
  rename List Val => xs
  cases xs <;> simp at *

def contains_fn : Val := .recv "f" "x" <|
  .lete "l" (.fst (.var "x")) <|
  .lete "cb" (.snd (.var "x")) <|
  .ife (.binop (.var "l") .eq (.val NULL))
    (.val (.nat 0)) <|
  .ife (.app (.var "cb") (.fst (.load (.var "l"))))
    (.val (.nat 1)) <|
  .app (.var "f") (.binop (.snd (.load (.var "l"))) .pair (.var "cb"))

def contains_spec_pre (P : Val → Bool) : Val → Li PROP (Val × List Val) :=
    λ v => do
      let (va, cb) ← exhale (pairL v)
      let xs ← exhale (atom (is_list va))
      exhale (persLi (fn_ok cb
        (λ va => do {exhale (prop (va ∈ xs)); return va})
        (λ va vr => do {exhale (prop (vr = .nat (if P va then 1 else 0))); return ()})))
      return (va, xs)

def contains_spec_post (P : Val → Bool) : (Val × List Val) → Val → Li PROP Empty :=
  λ (va, xs) vr => do
      exhale (atom_with_ref (is_list va) xs)
      exhale (prop (vr = .nat (if xs.any P then 1 else 0)))
      done

def contains_spec (P : Val → Bool) : PROP :=
  fn_spec (PROP:=PROP) contains_fn # ⟨_, contains_spec_pre P, contains_spec_post P⟩


set_option Elab.async false in
--set_option trace.profiler true in
--set_option trace.IRun.step true in
--set_option trace.profiler.threshold 5 in
-- time: ~578ms
#time theorem contains_ok [BIAffine PROP] P :
  ⊢ contains_spec (PROP:=PROP) P := by
  unfold contains_spec contains_spec_pre contains_spec_post contains_fn
  apply (BI.BIBase.Entails.trans _ (prove_fn_spec _ _ _))
  istart
  simp only [irun_preprocess]
  irun
  rename List Val => xs
  cases xs <;> simp at *

def contains_one_fn : Val := .recv .anon "x" <|
  .app (.val contains_fn) (.binop (.var "x") .pair (.rece .anon "y" <| .binop (.var "y") .eq (.val (.nat 1))))

-- TODO: profile this, this is slower than the Rocq version
-- TODO: The profile says "tactic execution of Lean.Parser.Tactic.refine took 654ms". Where does this come from?
set_option Elab.async false in
--set_option trace.profiler true in
--set_option trace.profiler.threshold 10 in
--set_option trace.IRun.step true in
--set_option profiler true in
-- time: 261ms
#time theorem contains_one_ok [BIAffine PROP] :
  ⊢ (do
    inhale (pers (atom_with_ref (fn_spec contains_fn)
      ⟨_, contains_spec_pre (λ v => v == Val.nat 1), contains_spec_post (λ v => v == Val.nat 1)⟩))
    fn_ok (PROP:=PROP) contains_one_fn
      (λ va => do
        let xs ← exhale (atom (is_list va))
        exhale (prop (∀ x ∈ xs, ∃ n, x = Val.nat n))
        return (va, xs))
      (λ (va, xs) vr => do
        exhale (atom_with_ref (is_list va) xs)
        exhale (prop (vr = Val.nat (if Val.nat 1 ∈ xs then 1 else 0)))
        done)).go := by
  unfold contains_spec_pre contains_spec_post contains_one_fn
  istart

  -- Time goes from ~300ms to ~2000ms if one removes the only. Why?
  simp only [irun_preprocess]
  -- iintro □h
  irun
--  all_goals mysorry
  -- TODO: automate this somehow?
  rename_i v v2 Φ Hin
  have ⟨n, Hn⟩ : ∃ n, v = .nat n := by simp [*]
  simp only [Hn]
  irun

end Iris.Examples
