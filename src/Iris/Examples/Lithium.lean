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

namespace Iris.Lithium
open Lean BI Std

variable [BI.{u} PROP] {α : Type v} {β : Type w}

structure Atom (α : Type v) where
  ref : α → PROP

structure InEx (α : Type v) where
  body : α → PROP

structure Li (α : Type v) where
  run : (α → PROP) → PROP
  mono' E1 E2 : ⊢ run E1 -∗ (∀ a, E1 a -∗ E2 a) -∗ run E2

section InEx

def InEx.pure (a : α) : @InEx PROP α :=
  InEx.mk λ b => iprop(⌜a = b⌝)

def InEx.bind (L1 : @InEx PROP α) (L2 : α → @InEx PROP β) :
  @InEx PROP β :=
  InEx.mk λ b => iprop(∃ a, L1.body a ∗ (L2 a).body b)

instance : Monad (@InEx PROP) where
  pure := .pure
  bind := .bind

def atom (A : @Atom PROP α) : @InEx PROP α := InEx.mk A.ref
def own (P : PROP) : @InEx PROP Unit := .mk λ _ => iprop(P)
def prop (P : Prop) : @InEx PROP Unit := own iprop(⌜P⌝)

end InEx

def Li.pure (a : α) : @Li PROP _ α := {
  run E := E a
  mono' E1 E2 := by
    dsimp
    iintro HE Hwand
    ispecialize Hwand HE
    iassumption
}

def Li.bind (G1 : @Li PROP _ α) (G2 : α → @Li PROP _ β) :
  @Li PROP _ β := {
  run E := G1.run (λ a => (G2 a).run E)
  mono' E1 E2 := by
    dsimp
    iintro HE Hwand
    sorry
}

instance : Monad (@Li PROP _) where
  pure := .pure
  bind := .bind

def exhaleR (L : @InEx PROP α) (E : α → PROP) : PROP :=
  iprop(∃ a, L.body a ∗ E a)

def exhale (L : @InEx PROP α) : @Li PROP _ α := {
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

def inhaleR (L : @InEx PROP α) (E : α → PROP) : PROP :=
  iprop(∀ a, L.body a -∗ E a)

def inhale (L : @InEx PROP α) : @Li PROP _ α := {
  run := inhaleR L
  mono' E1 E2 := by
    dsimp [inhaleR]
    iintro HE Hwand a HL
    ispecialize HE HL
    ispecialize Hwand HE
    iassumption
}

def allR (α : Type v) (E : α → PROP) : PROP :=
  iprop(∀ a, E a)

def all (α : Type v) : @Li PROP _ α := {
  run := allR α
  mono' E1 E2 := by
    dsimp [allR]
    iintro HE Hwand a
    ispecialize HE a
    ispecialize Hwand HE
    iassumption
}

def doneR : PROP := iprop(True)

def done : @Li PROP _ α := {
  run E := doneR
  mono' E1 E2 := by
    dsimp [doneR]
    iintro HE Hwand
    iassumption
}

def lifR (P : Prop) (E1 E2 : PROP) : PROP :=
  iprop((⌜P⌝ -∗ E1) ∧ (⌜¬P⌝ -∗ E2))

def lif (P : Prop) (G1 G2 : @Li PROP _ α) : @Li PROP _ α := {
  run E := lifR P (G1.run E) (G2.run E)
  mono' E1 E2 := by
    dsimp
    iintro HE Hwand
    sorry
}

def dsimpR {α : Type _} [BI PROP] (_ : Lean.Name) (a : α) (E : α → PROP) : PROP := E a

def dsimp {α : Type _} [BI PROP] (n : Lean.Name) (a : α) : @Li PROP _ α := {
  run := dsimpR n a
  mono' E1 E2 := by
    simp [dsimpR]
    sorry
}

def empty : Empty → PROP := λ e => nomatch e

-- TODO: add R variant
def dualizing (G : @Li PROP _ Empty) : @Li PROP _ Unit := {
  run E := iprop(G.run empty -∗ E ⟨⟩)
  mono' E1 E2 := by
    dsimp
    iintro HE Hwand HG
    ispecialize HE HG
    ispecialize Hwand HE
    iassumption
}

---- TODO: What are good precedences?
--notation:35 G:36 " ⇓ " E:35 => run G E
--notation:35 G:36 " ⇓ " "!" => run G empty

--def entails (G1 G2 : @Li PROP _ α) : Prop :=
--  ∀ E, G1.run E ⊢ G2.run E

--notation:25 G1:29 ":-" G2:25 => (entails G2 G1)
--set_option quotPrecheck false in -- TODO: Why is this necessary?
--notation:25 G1:29 ":-" G2:25 => (∀ E, (G2 ⇓ E ⊢ G1 ⇓ E))
notation:25 P:29 "⊣" Q:25 => (Q ⊢ P)
set_option quotPrecheck false in -- TODO: Why is this necessary?
notation:25 P:29 ":-" Q:25 => (∀ E, Li.run Q E ⊢ P E)

--notation:25 G1:29 ":-" G2:25 => (run! G2 ⊢ run! G1)

-- @[irun]
-- theorem run_bind (G1 : @Li PROP _ α) (G2 : α → Li β)
--   (E : β → PROP) :
--    G1.bind G2 ⇓ E ⊣ (G1 ⇓ λ b => G2 b ⇓ E) := by
--     simp [Li.bind, Li.run, Li.run]

-- @[irun]
-- theorem run_pure (a : α) (E : α → PROP) :
--    .pure a ⇓ E ⊣ E a := by
--     simp [Li.pure, Li.run, Li.run]

attribute [irun_preprocess] inhale exhale Lithium.done Li.run Li.bind

@[irun]
theorem exhale_bind (L1 : @InEx PROP α) (L2 : α → InEx β) :
  exhaleR (L1.bind L2) :-
    ((exhale L1).bind λ a => exhale (L2 a)) := by
    dsimp [exhaleR, InEx.bind]
    sorry

@[irun]
theorem inhale_bind (L1 : @InEx PROP α) (L2 : α → InEx β) E :
  inhaleR (L1.bind L2) E ⊣
   inhaleR L1 λ a => inhaleR (L2 a) E := by
    dsimp [inhaleR, InEx.bind]
    sorry

@[irun]
theorem exhale_pure (a : α) E :
  exhaleR (PROP:=PROP) (.pure a) E ⊣ E a := by
    dsimp [exhaleR, InEx.pure]
    sorry

@[irun]
theorem inhale_pure (a : α) E :
  inhaleR (PROP:=PROP) (.pure a) E ⊣ E a := by
    dsimp [inhaleR, InEx.pure]
    sorry


set_option pp.universes true

def test_inex (A : @Atom PROP Nat) : @InEx PROP Bool :=
  atom A ≫= λ n =>
  own (A.ref n) ≫
  .pure (n == 1)

def test_lithium (A : @Atom PROP Nat) : @Li PROP _ Bool := do
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

theorem inhale_own_tac [BI PROP] {P A : PROP} (E : Unit → PROP)
  (h : P ∗ A ⊢ E ())
 : P ⊢ (inhaleR (own A)) E := by
    simp [inhaleR, own]
    sorry

@[irun_tac (inhaleR (own _)) _]
def irunInhaleOwn : IRunTacticType := fun goal => do profileitM Exception "irunIntro" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop, bi, e, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let ~q(inhaleR (own $A) $E) := G | return none
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
 : P ⊢ exhaleR (own A) E := by
   sorry

@[irun_tac exhaleR (own _) _]
def irunCancel : IRunTacticType := fun goal => do profileitM Exception "irunCancel" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop, bi, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let ~q(exhaleR (own $A) $E) := G | return none
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

theorem done_tac [BI PROP] (P : PROP)
 : P ⊢ doneR := pure_intro .intro

--set_option pp.universes true

@[irun_tac doneR]
def irunDone : IRunTacticType := fun goal => do profileitM Exception "irunTrue" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop:=prop, bi:=bi, hyps:=_, e, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let .true := G.isAppOfArity ``doneR 2 | return none
  let pf := mkApp3 (.const ``done_tac G.getAppFn.constLevels!) prop bi e
  goal.assign pf
  return .some ([], [])


theorem lif_true [BI PROP] {cond} {P : PROP} (E1 E2 : PROP)
  (h1 : cond)
  (h2 : P ⊢ E1)
 : P ⊢ lifR cond E1 E2 :=
   sorry

theorem lif_false [BI PROP] {cond} {P : PROP} (E1 E2 : PROP)
  (h1 : ¬ cond)
  (h2 : P ⊢ E2)
 : P ⊢ lifR cond E1 E2 :=
   sorry

syntax "istepsolve" : tactic
macro_rules
  | `(tactic|istepsolve) => `(tactic|trivial)
--macro_rules
--  | `(tactic|istepsolve) => `(tactic|solve| simp)

@[irun_tac lifR _ _ _]
def irunLif : IRunTacticType := fun goal => do profileitM Exception "irunLif" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop, bi, e, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let ~q(lifR $cond $E1 $E2) := G | return none

  let mcond : Q($cond) ← mkFreshExprSyntheticOpaqueMVar cond
  try
    let _ ← evalTacticAtRaw (← `(tactic|istepsolve)) mcond.mvarId!
    let m : Q($e ⊢ $E1) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps, goal := E1 }
    let pf := q(lif_true $E1 $E2 $mcond $m)
    goal.assign pf
    return .some ([m.mvarId!], [])
  catch _ => pure ()

  let mnegcond : Q(¬$cond) ← mkFreshExprSyntheticOpaqueMVar q(¬ $cond)
  try
    let _ ← evalTacticAt (← `(tactic|istepsolve)) mnegcond.mvarId!
    let m : Q($e ⊢ $E2) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps, goal := E2 }
    let pf := q(lif_false $E1 $E2 $mnegcond $m)
    goal.assign pf
    return .some ([m.mvarId!], [])
  catch _ => pure ()

  throwError "Cannot solve either side of lif"

@[irun_tac dsimpR _ _ _]
def irunSimp : IRunTacticType := fun goal => do profileitM Exception "irunSimp" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some ig := parseIrisGoal? g | throwError "not in proof mode"
  let { prop:=_, bi:=_, e:=_, hyps:=_, goal:=G } := ig

  let_expr dsimpR _ _ _ n e E := G | return none
  let n : Name ← reduceEval n
  let ⟨e_new, _⟩ ← goal.withContext (dsimpWithExt n e)
  let g' := {ig with goal := Expr.beta E #[e_new]}.toExpr
  let goal' := ← goal.replaceTargetDefEq g'
  return .some ([goal'], [])

section test
variable {u} [BI.{u} PROP]

theorem test1 (P : Nat → PROP) (Q : PROP) :
  ⊢ ((inhale (own Q)).bind λ _ =>
      inhale (own (P 1)) ≫
      inhale (own (P 2)) ≫
      inhale (own iprop(⌜1 = 1⌝)) ≫
      exhale (own (P 1) ≫ own (P 2)) ≫
      exhale (own Q) ≫
     done).run empty := by
     istart
     simp [irun_preprocess]
     irun ∞


theorem test_intro_cancel (P G : PROP) :
  ⊢ (inhale ((own P) ≫ own G)).run λ _ =>
     (exhale (own G)).run λ _ =>
     done.run empty := by
    istart
    simp [irun_preprocess]
    irun 1
    irun 1
    irun 1
    irun 1
    irun 1

--set_option profiler true in
--set_option profiler.threshold 1 in
set_option maxRecDepth 30000 in
#time theorem proof_cancel_3 (P : Nat → PROP) :
  ⊢ (List.foldl (λ G n => inhaleR (own (P n)) λ _ => G)
    (List.foldl (λ G n => exhaleR (own (P n)) λ _ => G)
      (doneR) (
    -- List.reverse makes cancellation basically instant
    -- List.reverse
    (List.range 2)))
    (List.range 2))
:=
  by
    dsimp [List.foldl, List.range, List.range.loop, List.reverse]
    istart
    set_option trace.profiler true in
    -- set_option trace.profiler.threshold 1 in
    irun ∞

end test

end Iris.ProofMode

namespace Iris.Examples
open Lang Lithium

variable {u} [BI.{u} PROP]

/- Proof automation begins here -/

def expr_okR := @wp PROP _

@[irun_preprocess]
def expr_ok (e : Exp) : @Li PROP _ Val := {
  run := expr_okR e
  mono' := wp_wand e
}

-- set_option pp.universes true
/-
def fn_spec (v : Val) (G : Val → @Li PROP _ (Val → @Li PROP _ Empty)) : PROP :=
  iprop(∀ E va,
  (.bind (G va) λ L' =>
   .bind (.all Val) λ vr =>
   .bind (.dualizing (L' vr)) λ _ =>
   .pure vr) ⇓ E
  -∗
  wp (.app (.val v) (.val va)) E)
-/

def nat_okR (v : Val) (E : Nat → PROP) : PROP :=
  iprop(∃ n, ⌜v = .nat n⌝ ∗ E n)

@[irun_preprocess]
def nat_ok (v : Val) : @Li PROP _ Nat := {
  run := nat_okR v
  mono' E1 E2 := by sorry
}

def recv_okR (v : Val) (E : String → String → Exp → PROP) : PROP :=
  iprop(∃ f x e, ⌜v = .recv f x e⌝ ∗ E f x e)

@[irun_preprocess]
def recv_ok (v : Val) : @Li PROP _ (String × String × Exp) := {
  run E := recv_okR v λ f x e => E (f, x, e)
  mono' E1 E2 := by sorry
}

def subst_okR (x : String) (v : Val) (e : Exp) (E : Exp → PROP) : PROP :=
  E (subst x v e)

@[irun_preprocess]
def subst_ok (x : String) (v : Val) (e : Exp) : @Li PROP _ Exp := {
  run := subst_okR x v e
  mono' E1 E2 := by
    simp [subst_okR]
    sorry
}

@[irun]
theorem nat_okR_nat (n : Nat) (E : Nat → PROP) :
  nat_okR (.nat n) E ⊣ E n := by
  dsimp [nat_okR]
  iintro HP
  iexists _
  isplit
  · ipure_intro
    rfl
  · iassumption

@[irun]
theorem recv_okR_rec f x e (E : String → String → Exp -> PROP) :
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
  expr_okR (.val v) E ⊣ E v := by sorry

@[irun]
theorem expr_okR_plus e1 e2 (E : Val -> PROP) :
  expr_okR (Exp.binop e1 .plus e2) E ⊣
   expr_okR e1 λ v1 =>
   expr_okR e2 λ v2 =>
   nat_okR v1 λ n1 =>
   nat_okR v2 λ n2 =>
   dsimpR `irun_simp (n1 + n2) λ n =>
   E (.nat n) := by sorry

@[irun]
theorem expr_okR_minus e1 e2 (E : Val -> PROP) :
  expr_okR (Exp.binop e1 .minus e2) E ⊣
   expr_okR e1 λ v1 =>
   expr_okR e2 λ v2 =>
   nat_okR v1 λ n1 =>
   nat_okR v2 λ n2 =>
   dsimpR `irun_simp (n1 - n2) λ n =>
   E (.nat n) := by sorry

@[irun]
theorem expr_okR_eq e1 e2 (E : Val -> PROP) :
  expr_okR (Exp.binop e1 .eq e2) E ⊣
   expr_okR e1 λ v1 =>
   expr_okR e2 λ v2 =>
   nat_okR v1 λ n1 =>
   nat_okR v2 λ n2 =>
   dsimpR `irun_simp (if n1 == n2 then 1 else 0) λ n =>
   E (.nat n) := by sorry

@[irun]
theorem expr_okR_rec f x e (E : Val -> PROP) :
  expr_okR (.rece f x e) E ⊣ E (.recv f x e) := by sorry

@[irun]
theorem expr_okR_app e1 e2 (E : Val -> PROP) :
  expr_okR (.app e1 e2) E ⊣
   expr_okR e2 λ v2 =>
   expr_okR e1 λ v1 =>
   recv_okR v1 λ f x e' =>
   subst_okR x v2 e' λ e =>
   subst_okR f (.recv f x e') e λ e =>
   expr_okR e E := by sorry

@[irun]
theorem expr_okR_if e1 e2 e3 E :
  (expr_okR (PROP:=PROP) e1 λ v1 =>
   nat_okR v1 λ n1 =>
   lifR (n1 ≠ 0) (expr_okR e2 E) (expr_okR e3 E)) ⊢
  expr_okR (.ife e1 e2 e3) E := by sorry


section
open Lean Elab Tactic Meta Qq BI Std ProofMode

@[irun_tac subst_okR _ _ _ _]
def irunSubst : IRunTacticType := fun goal => do profileitM Exception "irunSubst" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some ig := parseIrisGoal? g | throwError "not in proof mode"
  let { prop:=_, bi:=_, e:=_, hyps:=_, goal:=G } := ig

  let_expr subst_okR _ x v e E := G | return none
  let .lit (.strVal x) := x | return none
  let e := Reify.reify e
  let e' := (Reify.subst x v e).unreify
  let g' := {ig with goal := Expr.beta E #[e']}.toExpr
--  let ⟨g', _⟩ ← goal.withContext (dsimpWithExt `irun_simp g')
  let goal' := ← goal.replaceTargetDefEq g'
  return .some ([goal'], [])

end

theorem expr_okR_test (P : Val -> PROP) :
  ⊢ (inhale (own (P (.nat 10)))).run λ _ =>
     (expr_ok (.binop (.val (.nat 5)) .plus (.val (.nat 5)))).run λ v =>
     (exhale (own (P v))).run λ _ =>
     done.run empty := by
  istart
  simp [irun_preprocess]
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
   ⊢ ((inhale (own (P (.nat 0)))) |>.bind λ _ =>
      (expr_ok (.app (.val rec_fn) (.val (.nat 200)))) |>.bind λ v =>
      (exhale (own (P v))) |>.bind λ _ =>
      done).run empty := by
  istart
  unfold rec_fn
  simp [irun_preprocess]
  --set_option trace.profiler true in
  --set_option trace.profiler.threshold 1 in
  --set_option diagnostics true in
  --set_option profiler true in
  irun ∞

end Iris.Examples
