/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode
import Iris.Examples.IRunAttr
import Iris.Examples.IRun
import Iris.Examples.Exp


namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

@[irun 5]
theorem li_assoc_star.{u} {PROP : Type u} [BI PROP] {P1 P2 P3 : PROP}
 : P1 ∗ (P2 ∗ P3) ⊢ (P1 ∗ P2) ∗ P3 :=
   sorry

@[irun 5]
theorem li_assoc_wand.{u} {PROP : Type u} [BI PROP] {P1 P2 P3 : PROP}
 : (P1 -∗ P2 -∗ P3) ⊢ (P1 ∗ P2) -∗ P3 :=
   sorry

axiom PROPTest : Type
axiom BIPROPTest : BI PROPTest
noncomputable instance BIPROPTest_inst : BI PROPTest := BIPROPTest

noncomputable def PROPTest_test : PROPTest := iprop(True)

def prop_test [BI PROP] : PROP := iprop(True)

@[irun_tac 100 | PROPTest_test, iprop((∃ _, ∀ _, prop_test ∗ _)), iprop((⌜_⌝ ∗ _ ∗ _) -∗ _), _ ∗ _]
def irunTest : IRunTacticType := fun goal => do
  IO.println s!"Test Tac {← ppExpr (← goal.getType)}"
  return none

theorem intro_tac [BI PROP] {P A Q : PROP}
  (h : P ∗ A ⊢ Q)
 : P ⊢ A -∗ Q := wand_intro h

@[irun_tac _ -∗ _]
def irunIntro : IRunTacticType := fun goal => do profileitM Exception "irunIntro" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop, bi, e, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let ~q(iprop($A -∗ $Q)) := G | return none
  let ident ← `(binderIdent| _)
  let (b, A') := if A.isAppOfArity ``intuitionistically 3 then
      (q(true), A.getArg! 3)
    else
      (q(false), A)
  let goals ← IO.mkRef #[]
  let pf ← iCasesCore bi hyps Q b A A' ⟨⟩ (.one ident) fun hyps => do
    let m ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps, goal:=Q }
    goals.modify (·.push m.mvarId!)
    return m
  let pf := q(@intro_tac $prop $bi $e $A $Q $pf)
  goal.assign pf
  return .some ((← goals.get).toList, [])

theorem cancel [BI PROP] {p : Bool} {P P' A Q' : PROP}
  (hP : P ⊣⊢ P' ∗ □?p A)
  (h : P' ⊢ Q')
 : P ⊢ A ∗ Q' :=
   hP.1.trans <| sep_comm.1.trans <| sep_mono intuitionisticallyIf_elim h

@[irun_tac _ ∗ _]
def irunCancel : IRunTacticType := fun goal => do profileitM Exception "irunCancel" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop, bi, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let ~q(iprop($A ∗ $Q)) := G | return none
  let some ⟨_inst, P', hyps, out, ty, b, _, pf⟩ ←
    hyps.removeG false fun _ _ _ ty => do
      -- logInfo m!"ty: ${ty}, A: ${A}"
      if ← isDefEq ty A then return some ty else return none
    | return none
  have : $ty =Q $A := ⟨⟩
  have : $out =Q iprop(□?$b $ty) := ⟨⟩
  let m : Q($P' ⊢ $Q) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps := hyps, goal := Q }
  let pf := q(cancel $pf $m)
  goal.assign pf
  return .some ([m.mvarId!], [])

theorem true_tac [BI PROP] (P : PROP)
 : P ⊢ True := pure_intro .intro

@[irun_tac True]
def irunTrue : IRunTacticType := fun goal => do profileitM Exception "irunTrue" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop:=prop, bi:=bi, hyps:=_, e, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let ~q(iprop(True)) := G | return none
  let pf := q(@true_tac $prop $bi $e)
  goal.assign pf
  return .some ([], [])

def lif [BI PROP] (cond : Prop) (P1 P2 : PROP) : PROP :=
  iprop((⌜cond⌝ -∗ P1) ∧ (⌜¬cond⌝ -∗ P2))

theorem lif_true [BI PROP] {cond} {P P1 P2 : PROP}
  (h1 : cond)
  (h2 : P ⊢ P1)
 : P ⊢ lif cond P1 P2 :=
   sorry

theorem lif_false [BI PROP] {cond} {P P1 P2 : PROP}
  (h1 : ¬ cond)
  (h2 : P ⊢ P2)
 : P ⊢ lif cond P1 P2 :=
   sorry

syntax "istepsolve" : tactic
macro_rules
  | `(tactic|istepsolve) => `(tactic|trivial)
--macro_rules
--  | `(tactic|istepsolve) => `(tactic|solve| simp)

@[irun_tac lif _ _ _]
def irunLif : IRunTacticType := fun goal => do profileitM Exception "irunLif" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop, bi, e, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let ~q(iprop(lif $cond $P1 $P2)) := G | return none

  let mcond : Q($cond) ← mkFreshExprSyntheticOpaqueMVar cond
  try
    let _ ← evalTacticAtRaw (← `(tactic|istepsolve)) mcond.mvarId!
    let m : Q($e ⊢ $P1) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps, goal := P1 }
    let pf := q(lif_true (P2:=$P2) $mcond $m)
    goal.assign pf
    return .some ([m.mvarId!], [])
  catch _ => pure ()

  let mnegcond : Q(¬$cond) ← mkFreshExprSyntheticOpaqueMVar q(¬ $cond)
  try
    let _ ← evalTacticAt (← `(tactic|istepsolve)) mnegcond.mvarId!
    let m : Q($e ⊢ $P2) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps, goal := P2 }
    let pf := q(lif_false (P1:=$P1) $mnegcond $m)
    goal.assign pf
    return .some ([m.mvarId!], [])
  catch _ => pure ()

  throwError "Cannot solve either side of lif"

def wpsimp {α : Type _} [BI PROP] (_ : Lean.Name) (a : α) (P : α -> PROP) : PROP := P a

@[irun_tac wpsimp _ _ _]
def irunSimp : IRunTacticType := fun goal => do profileitM Exception "irunSimp" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some ig := parseIrisGoal? g | throwError "not in proof mode"
  let { prop:=_, bi:=_, e:=_, hyps:=_, goal:=G } := ig

  let .true := G.isAppOfArity ``wpsimp 6 | return none
  let n : Name ← reduceEval (G.getArg! 3)
  let e := G.getArg! 4
  let P := G.getArg! 5
  let ⟨e_new, _⟩ ← goal.withContext (dsimpWithExt n e)
  let g' := {ig with goal := Expr.beta P #[e_new]}.toExpr
  let goal' := ← goal.replaceTargetDefEq g'
  return .some ([goal'], [])


section test
variable {u} [BI.{u} PROP]

theorem proof_test (P : Nat → PROP) (Q : PROP) :
  ⊢ Q -∗ P 1 -∗ P 2 -∗ ⌜1=1⌝ -∗ (P 1 ∗ P 2) ∗ Q ∗ True
:= by
  istart
  irun


theorem proof_intro_custom_auto (P G : PROP) :
  ⊢ P -∗ G -∗ G ∗ True := by
    istart
    irun

theorem proof_intro_pers_auto (P G : PROP) :
  ⊢ P -∗ □ G -∗ G ∗ G ∗ True := by
    istart
    irun

--set_option profiler true in
theorem proof_intro_2 [BIAffine PROP] (P : Nat → PROP) :
  ⊢ List.foldl (λ G n => iprop((P n) -∗ G)) (P 119) (List.range 120)
:=
  -- set_option trace.profiler true in by
   by
     dsimp [List.foldl, List.range, List.range.loop] <;> (repeat iintro _) <;> iassumption



-- TODO: why does ilif sometimes take more than 1ms here if there a no lif in the goal?
--set_option profiler true in
--set_option profiler.threshold 1 in
set_option maxRecDepth 30000 in
#time theorem proof_cancel_2 (P : Nat → PROP) :
  ⊢ (List.foldl (λ G n => iprop((P n) ∗ G)) iprop(True) (List.range 200)) -∗
    (List.foldl (λ G n => iprop(P n ∗ G)) iprop(True) (
    -- List.reverse makes cancellation basically instant
    -- List.reverse
    (List.range 200)))
:=
  by
    dsimp [List.foldl, List.range, List.range.loop, List.reverse]
    istart
    -- set_option trace.profiler true in
    -- set_option trace.profiler.threshold 1 in
    irun ∞

end test

end Iris.ProofMode

namespace Iris.Examples
open BI Lang

variable {u} [BI.{u} PROP]

def wpnat (v : Val) (P : Nat -> PROP) : PROP := iprop(∃ n, ⌜v = .nat n⌝ ∗ P n)
def wprecv (v : Val) (P : Binder -> Binder -> Exp -> PROP) : PROP := iprop(∃ f x e, ⌜v = .recv f x e⌝ ∗ P f x e)
def wpsubst (x : Binder) (v : Val) (e : Exp) (P : Exp -> PROP) : PROP := P (subst' x v e)

@[irun]
theorem wpnat_nat (n : Nat) (P : Nat -> PROP) : P n ⊢ wpnat (.nat n) P := by
  unfold wpnat
  iintro HP
  iexists _
  isplit
  · ipure_intro
    rfl
  · iassumption

@[irun]
theorem wprecv_rec f x e (P : Binder -> Binder -> Exp -> PROP) : P f x e ⊢ wprecv (.recv f x e) P := by
  unfold wprecv
  iintro HP
  iexists _
  iexists _
  iexists _
  isplit
  · ipure_intro
    rfl
  · iassumption

@[irun]
 theorem wp_val v (P : Val -> PROP) :
  P v ⊢ wp (.val v) P := by sorry

@[irun]
theorem wp_plus e1 e2 (P : Val -> PROP) :
  (wp e1 λ v1 =>
   wp e2 λ v2 =>
   wpnat v1 λ n1 =>
   wpnat v2 λ n2 =>
   ProofMode.wpsimp `irun_simp (n1 + n2) λ n =>
   P (.nat n)) ⊢ wp (Exp.binop e1 .plus e2) P := by sorry

@[irun]
theorem wp_minus e1 e2 (P : Val -> PROP) :
  (wp e1 λ v1 =>
   wp e2 λ v2 =>
   wpnat v1 λ n1 =>
   wpnat v2 λ n2 =>
   ProofMode.wpsimp `irun_simp (n1 - n2) λ n =>
   P (.nat n)) ⊢ wp (Exp.binop e1 .minus e2) P := by sorry

@[irun]
theorem wp_eq e1 e2 (P : Val -> PROP) :
  (wp e1 λ v1 =>
   wp e2 λ v2 =>
   wpnat v1 λ n1 =>
   wpnat v2 λ n2 =>
   ProofMode.wpsimp `irun_simp (if n1 == n2 then 1 else 0) λ n =>
   P (.nat n)) ⊢ wp (Exp.binop e1 .eq e2) P := by sorry

@[irun]
theorem wp_rec (P : Val -> PROP) :
  (P (.recv f x e)) ⊢ wp (.rece f x e) P := by sorry

@[irun]
theorem wp_app e1 e2 (P : Val -> PROP) :
  (wp e2 λ v2 =>
   wp e1 λ v1 =>
   wprecv v1 λ f x e' =>
   wpsubst x v2 e' λ e =>
   wpsubst f (.recv f x e') e λ e =>
   wp e P) ⊢ wp (.app e1 e2) P := by sorry

@[irun]
theorem wp_if e1 e2 e3 (P : Val -> PROP) :
  (wp e1 λ v1 =>
   wpnat v1 λ n1 =>
   ProofMode.lif (n1 ≠ 0) (wp e2 P) (wp e3 P)) ⊢
  wp (.ife e1 e2 e3) P := by sorry


section
open Lean Elab Tactic Meta Qq BI Std ProofMode

@[irun_tac wpsubst _ _ _ _]
def irunSubst : IRunTacticType := fun goal => do profileitM Exception "irunSubst" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some ig := parseIrisGoal? g | throwError "not in proof mode"
  let { prop:=_, bi:=_, e:=_, hyps:=_, goal:=G } := ig

  let .true := G.isAppOfArity ``wpsubst 5 | return none
  let some x := Reify.Binder.reify (G.getArg! 1) | return none
  let v := G.getArg! 2
  let P := G.getArg! 4
  let e := Reify.reify (G.getArg! 3)
  let e' := (Reify.subst' x v e).unreify
  let g' := {ig with goal := Expr.beta P #[e']}.toExpr
  let goal' := ← goal.replaceTargetDefEq g'
  return .some ([goal'], [])

end


theorem wp_test (P : Val -> PROP) :
  P (.nat 10) ⊢ wp (Exp.binop (.val (.nat 5)) .plus (.val (.nat 5))) (λ v => iprop(P v ∗ True)) := by
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

/-
time for 200 iterations:
- with match reduction, no dsimp in IRun, reified subst in irunSubst, solve if using trivial, wpsimp: ~1686ms
  - In LithiumM, without unfolding LithiumM.run: 2244ms
- with match reduction, no dsimp in IRun, reified subst + dsimp in irunSubst, solve if using trivial: ~1723ms
- with match reduction, no dsimp in IRun, reified subst in irunSubst, solve if using simp, wpsimp: ~2299ms
- with match reduction, no dsimp in IRun, reified subst + dsimp in irunSubst, solve if using simp: ~2299ms
- no match reduction, no dsimp in IRun, reified subst + dsimp in irunSubst, solve if using simp: ~2299ms
- with match reduction, no dsimp in IRun, dsimp [wpsubst, subst] in irunSubst, solve if using simp: ~2991ms
- dsimp in IRun, reified subst in irunSubst, solve if using simp: ~3725ms
- dsimp in IRun, reified subst + dsimp in irunSubst, solve if using simp: ~3725ms

comparison in Rocq:
- 200 steps: 4579ms for rep liTStep, 5026ms for Qed
- 100 steps: 1905ms for rep liTStep, 1496ms for Qed
-/
set_option profiler true in
--set_option profiler.threshold 1 in
#time theorem wp_test2 (P : Val -> PROP) :
  P (.nat 0) ⊢ wp (.app (.val rec_fn) (.val (.nat 200))) (λ v => iprop(P v ∗ True)) := by
  istart
  unfold rec_fn
  -- set_option trace.profiler true in
  --set_option trace.profiler.threshold 1 in
  irun ∞

end Iris.Examples
