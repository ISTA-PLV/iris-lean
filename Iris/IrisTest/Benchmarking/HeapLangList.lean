module

public import Iris
public import IrisTest.Benchmarking.Timing

namespace IrisTest.ListBenchmarking

open Iris BI ProgramLogic List HeapLang

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def nil : Val := hl_val% none()

def cons : Val := hl_val% λ x, some(ref(x))

def llength : Val := hl_val% λ x, #(0 : Int)

/-- Continuation-passing list builder: keeps the generated program term linear
    in `n` rather than quadratic. Same shape as `makeList2` in the uploads. -/
def makeList2 : List Int → (Exp → Exp) → Exp
  | [] => λ cont => cont nil
  | l :: ls => λ cont =>
    makeList2 ls λ e => hl%
    let vls := &e;
    &(cont hl(&cons (#l, vls)))

/-- Opaque variant, matching Rocq's `Admitted` `isList`. -/
opaque isList [HeapLangGS hlc GF] (v : Val) (xs : List Int) : IProp GF

theorem isList_nil {v} [HeapLangGS hlc GF] :
  isList (GF := GF) v [] ⊣⊢ iprop(⌜v = hl_val(none())⌝) := sorry

theorem isList_cons {v x xs} [HeapLangGS hlc GF] :
  isList (GF := GF) v (x :: xs) ⊣⊢ iprop(∃ l tl, ⌜v = hl_val(some(#(.loc l)))⌝ ∗
    l ↦ some hl_val((#x, &tl)) ∗ isList tl xs) := sorry

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

theorem nil_spec (Φ : Val → IProp GF) :
    (∀ v, isList v [] -∗ Φ v) -∗
    WP hl(v(&nil)) {{ Φ }} := sorry

theorem cons_spec (x : Int) (l : Val) (ls : List Int) (Φ : Val → IProp GF) :
    isList (GF := GF) l ls -∗
    (∀ v, isList v (x :: ls) -∗ Φ v) -∗
    WP hl(&cons v((#x, &l))) {{ Φ }} := sorry

theorem length_spec (l : Val) (ls : List Int) (Φ : Val → IProp GF) :
    isList (GF := GF) l ls -∗
    (∀ v, isList v ls -∗ ⌜v = hl_val(#(ls.length : Int))⌝ -∗ Φ v) -∗
    WP hl(&llength v(&l)) {{ Φ }} := sorry

def buildList (l : List Int) : Exp :=
  makeList2 l λ e => hl%
  let v := &e;
  &llength v

/-- Set the length of the list. -/
abbrev n : Nat := 250

example :
    ⊢@{IProp GF} WP (buildList (replicate n 1)) {{ fun bv => iprop% ⌜bv = hl_val(#((n : Int)))⌝ }} := by
  unfold buildList n
  /- Setup phase -/
  dsimp only [reduceReplicate, makeList2]
  wp_pures
  wp_bind &cons _
  iapply cons_spec
  · unfold nil; iapply isList_nil; itrivial
  /- Loop phase -/
  itime
    repeat
      iintro %_ _ <;> wp_pures
      wp_bind &cons _
      iapply cons_spec $$ [$]
  /- Tail phase -/
  iintro %v Hv <;>
  wp_pures <;>
  wp_bind &llength _
  iapply length_spec $$ Hv
  iintro %w Hw %Hlen //

-- set_option profiler true in
-- set_option trace.profiler true in
-- set_option trace.profiler.threshold 1 in
#time
example :
    ⊢@{IProp GF} WP (buildList (replicate n 1)) {{ fun bv => iprop% ⌜bv = hl_val(#((n : Int)))⌝ }} := by
  unfold buildList n
  /- Setup phase -/
  dsimp only [reduceReplicate, makeList2]
  wp_pures
  wp_bind &cons _
  iapply cons_spec
  · unfold nil; iapply isList_nil; itrivial
  /- Loop phase -/
  itimeN 5
    repeat
      iintro %_ _ <;> wp_pures
      wp_bind &cons _
      iapply cons_spec $$ [$]
  /- Tail phase -/
  iintro %v Hv <;>
  wp_pures <;>
  wp_bind &llength _
  iapply length_spec $$ Hv
  iintro %w Hw %Hlen //
