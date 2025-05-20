/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode
import Iris.Lithium.IRunAttr
import Iris.Lithium.IRun

namespace Iris.Lithium
open Lean Elab.Tactic Meta Qq BI

attribute [irun_preprocess] Pure.pure Bind.bind

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

section InEx

def InEx.pure (a : α) : InEx PROP α :=
  InEx.mk λ b => iprop(⌜a = b⌝)

def InEx.bind (L1 : InEx PROP α) (L2 : α → InEx PROP β) :
  InEx PROP β :=
  InEx.mk λ b => iprop(∃ a, L1.body a ∗ (L2 a).body b)

instance : Monad (InEx PROP) where
  pure := .pure
  bind := .bind

-- TODO: Use this and add it for Li
instance : HAndThen (InEx PROP α) (InEx PROP β) (InEx PROP β) where
  hAndThen L1 L2 := L1.bind λ _ => L2 ()

def atom (A : Atom PROP α) : InEx PROP α := InEx.mk A.ref
def atom_with_ref (A : Atom PROP α) (a : α) : InEx PROP Unit := .mk λ _ => iprop(A # a)
def prop (P : Prop) : InEx PROP Unit := .mk λ _ => iprop(⌜P⌝)
def pers (L : InEx PROP α) : InEx PROP α := .mk λ a => iprop(□ L.body a)
def persLi (G : Li PROP α) : InEx PROP Unit := .mk λ _ => iprop(□ G.run λ _ => iprop(True))

end InEx

section Li
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

def failR {α : Type} (_ : α) : PROP := iprop(False)

@[irun_preprocess]
def fail {β : Type} (a : β) : Li PROP α := {
  run E := failR a
  mono' E1 E2 := by
    dsimp [failR]
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

end Li

def test_lithium (A : Atom PROP Nat) : Li PROP Bool := do
  let b ← exhale do
    let n ← atom A
    return (n == 1)
  inhale do
    let n ← atom A
    prop (b = (n == 1))
    return true

notation:25 P:29 "⊣" Q:25 => (Q ⊢ P)
set_option quotPrecheck false in -- TODO: Why is this necessary?
notation:25 P:29 ":-" Q:25 => (∀ E, Li.run Q E ⊢ P E)

section irun
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

end irun

end Iris.Lithium

namespace Iris.Lithium
open Lean Elab Tactic Meta Qq BI Std Lithium ProofMode

section inhale

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

end inhale

section exhale

-- not necessary since there is the direct matching running first
-- @[irun]
theorem cancel_match [BI PROP] {α : Type _} (A : Atom PROP α) a E :
  cancelR (A # a) A E ⊣ E a := by mysorry

@[irun]
theorem exhaleR_persLi (α : Type _) [BI PROP] (G : Li PROP α) :
  exhaleR (PROP:=PROP) (persLi G) :-
    branch ((dropSpatial G).bind λ _ => Lithium.done) (return ()) := by
  mysorry

@[irun]
theorem exhale_atom_with_ref [BI PROP] {α : Type _} (A : Atom PROP α) a (E : Unit → PROP) :
   exhaleR (atom_with_ref A a) E ⊣ exhaleR (atom A) λ a' => exhaleR (prop (a = a')) λ _ => E () :=
   by mysorry

@[irun]
theorem exhale_prop [BI PROP] P (E : Unit → PROP) :
   P →
   exhaleR (prop P) E ⊣ E () :=
   by mysorry


theorem exhale_atom_direct_tac {α : Type _} [BI PROP] {p : Bool} {P P' : PROP} (A : Atom PROP α) (a : α) {E}
  (_hP : P ⊣⊢ P' ∗ □?p A # a)
  (_h : P' ⊢ E a)
 : P ⊢ exhaleR (atom A) E := by
   mysorry

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

end exhale

section all

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

end all

section done
theorem done_tac [BI PROP] (P : PROP)
 : P ⊢ doneR := pure_intro .intro

@[irun_tac doneR]
def irunDone : IRunTacticType := fun goal _config => do profileitM Exception "irunDone" (← getOptions) do
  let { u:=_, prop, bi, hyp, goal:=G } := goal
  let .true := G.isAppOfArity ``doneR 2 | return none
  let pf := mkApp3 (.const ``done_tac G.getAppFn'.constLevels!) prop bi hyp
  return .some (pf, [], [])

end done

section branch
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

end branch

section dropSpatial

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

end dropSpatial

section simp

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

end simp

section dualizing

@[irun]
theorem dualizing_exhale [BI PROP] α (L : InEx PROP α) (G : (Empty → PROP) → α → PROP) E :
  dualizingR (PROP:=PROP) (λ E => exhaleR L (G E)) E ⊣
   inhaleR L λ a =>
   dualizingR (λ E => G E a) E := by mysorry

@[irun]
theorem dualizing_inhale [BI PROP] α (L : InEx PROP α) (G : (Empty → PROP) → α → PROP) E :
  dualizingR (PROP:=PROP) (λ E => inhaleR L (G E)) E ⊣
   exhaleR L λ a =>
   dualizingR (λ E => G E a) E := by mysorry

@[irun]
theorem dualizing_done [BI PROP] E :
  dualizingR (PROP:=PROP) (λ _ => doneR) E ⊣ E () := by mysorry
end dualizing

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
     irun

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
    irun

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
  ⊢ inhaleR (List.foldl (λ G n => ((atom_with_ref (P n) ()).bind λ _ => G)) (.pure tt) (List.range 100)) λ _ =>
    (List.foldl (λ G n => exhaleR (atom (P n)) λ _ => G)
      (doneR) (
    -- List.reverse makes cancellation faster
    -- List.reverse
    (List.range 100)))

:=
  by
    dsimp [List.foldl, List.range, List.range.loop, List.reverse]
    istart
    irun

end test

end Iris.Lithium
