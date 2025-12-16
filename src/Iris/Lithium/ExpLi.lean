/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode
import Iris.Lithium.Lithium
import Iris.Lithium.Exp

namespace Iris.ExampleLang
open Lithium BI

variable [BI.{u} PROP]

section InEx
-- TODO: Make this an atom?
def natL (v : Val) : InEx PROP Nat := InEx.mk λ n => iprop(⌜v = .nat n⌝)
def pairL (v : Val) : InEx PROP (Val × Val) := InEx.mk λ p => iprop(⌜v = .pair p.1 p.2⌝)
end InEx

section Li
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
end Li

section irun
attribute [irun_simp] Nat.add_one_sub_one

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

end irun

section subst
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

end subst

section fn

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
   ((Gpre va).run) |> λ Gpre' =>
   dualizingR (λ _ => Gpre' λ a => exhaleR (atom_with_ref Φ a) λ _ => doneR) λ _ =>
   subst_okR x va e λ e =>
   subst_okR f v' e λ e =>
   expr_okR e λ vr =>
   exhaleR (atom Φ) λ a =>
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
end fn

section ptsto
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
end ptsto

section test
example (P : Val -> Atom PROP Unit) :
  ⊢ (do
      inhale (atom_with_ref (P (.nat 10)) ())
      let v ← expr_ok (.binop (.val (.nat 5)) .plus (.val (.nat 5)))
      exhale (atom (P v))
      done).go := by
  istart
  simp only [irun_preprocess]
  irun

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


example :
  ⊢ fn_spec (PROP:=PROP) rec_fn # ⟨Nat, λ va => exhale (natL va), λ _ _ => done⟩ := by
  unfold rec_fn
  iapply (prove_fn_spec (PROP:=PROP))
  simp only [irun_preprocess]
  irun

end test

section echo
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
  iapply (prove_fn_spec (PROP:=PROP))
  simp only [irun_preprocess]
  irun

theorem main_ok [BIAffine PROP] :
  echo_spec PROP ⊢ (fn_spec main_fn) # ⟨_, λ _ => .pure (), λ _ vr => do exhale (prop (vr = .nat 1)); done⟩ := by
  unfold echo_spec main_fn getc_fn putc_fn
  iintro _
  iapply (prove_fn_spec (PROP:=PROP))
  simp only [irun_preprocess]
  irun

end echo

section fib
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
  iapply (prove_fn_spec (PROP:=PROP))
  simp only [irun_preprocess]
  irun
  · rename Nat => x
    cases x using fib.fun_cases <;> simp [fib] at * <;> omega

end fib

section ptsto
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
end ptsto

section tutorial
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
  iapply (prove_fn_spec (PROP:=PROP))
  simp only [irun_preprocess]
  irun

theorem cons_ok [BIAffine PROP] :
  ⊢ (fn_spec (PROP:=PROP) cons_fn) # ⟨_,
    λ va => do {let (x, v) ← exhale (pairL va); let xs ← exhale (atom (is_list v)); return (x, xs)},
    λ (x, xs) vr => do {let vs ← exhale (atom (is_list vr)); exhale (prop (vs = x::xs)); done}⟩ := by
  unfold cons_fn
  iapply (prove_fn_spec (PROP:=PROP))
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
  iintro ⟨□ h1, □ h2⟩
  iapply (prove_fn_spec (PROP:=PROP))
  simp only [irun_preprocess]
  irun


def head_fn : Val := .recv .anon "l" (.fst (.load (.var "l")))

theorem head_ok :
  ⊢ fn_spec (PROP:=PROP) head_fn # ⟨_,
    λ va => do {let xs ← exhale (atom (is_list va)); exhale (prop (0 < xs.length)); return (va, xs)},
    λ (va, xs) vr => do {exhale (atom_with_ref (is_list va) xs); exhale (prop (xs.head? = some vr)); done}⟩ := by
  unfold head_fn
  iapply (prove_fn_spec (PROP:=PROP))
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
  iapply (prove_fn_spec (PROP:=PROP))
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
  iapply (prove_fn_spec (PROP:=PROP))
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

end tutorial

end Iris.ExampleLang
