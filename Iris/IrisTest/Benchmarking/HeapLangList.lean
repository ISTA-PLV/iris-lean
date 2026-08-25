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

def makeList2 : List Int → (Exp → Exp) → Exp
  | [] => λ cont => cont nil
  | l :: ls => λ cont =>
    makeList2 ls λ e => hl%
    let vls := &e;
    &(cont hl(&cons (#l, vls)))

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

syntax "list_bench " num : command

macro_rules
  | `(list_bench $n:num) => do
    let name := Lean.mkIdent (Lean.Name.mkSimple s!"wp_buildList_{n.getNat}")
    let lbl := Lean.Syntax.mkStrLit s!"heaplang_list|cons_loop|{n.getNat}"
    `(theorem $name :
        ⊢@{IProp GF} WP (buildList (replicate $n 1)) {{ fun bv => iprop% ⌜bv = hl_val(# $n)⌝ }} := by
      unfold buildList
      dsimp only [reduceReplicate, makeList2]
      wp_pures
      wp_bind &cons _
      iapply cons_spec
      · unfold nil; iapply isList_nil; itrivial
      itimeN 5 $lbl
        repeat
          iintro %_ _ <;> wp_pures
          wp_bind &cons _
          iapply cons_spec $$ [$]
      iintro %v Hv <;>
      wp_pures <;>
      wp_bind &llength _
      iapply length_spec $$ Hv
      iintro %w Hw %Hlen //)

/-

list_bench 10  reps 5
list_bench 20  reps 5
list_bench 30  reps 5
list_bench 40  reps 5
list_bench 50  reps 5
list_bench 60  reps 5
list_bench 70  reps 5
list_bench 80  reps 5
list_bench 90  reps 5
list_bench 100  reps 5
list_bench 110  reps 5
list_bench 120  reps 5
list_bench 130  reps 5
list_bench 140  reps 5
list_bench 150  reps 5
list_bench 160  reps 5
list_bench 170  reps 5
list_bench 180  reps 5
list_bench 190  reps 5
list_bench 200  reps 5
list_bench 210  reps 5
list_bench 220  reps 5
list_bench 230  reps 5
list_bench 240  reps 5
list_bench 250  reps 5
list_bench 260  reps 5

-/
