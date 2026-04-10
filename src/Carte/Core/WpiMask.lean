import Carte.Core.Handler
import Carte.Core.ITree
import Carte.Core.Wpi
import Iris.ProofMode
import Iris.BI.Lib.Fixpoint
import ITree.Definition
import ITree.Effect

open Iris BI ITree

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

section wpi_tree_mask_def

variable {E} (M : CoPset) (H : IHandler (PROP := PROP) E)

open OFE

def wpi_mask (t : ITree E R) (Φ : R → PROP) : PROP :=
  iprop(|={M,∅}=> wpi H t (λ v => iprop(|={∅,M}=> Φ v)))

instance wpi_mask_ne (t : ITree E R) :
    OFE.NonExpansive (λ Φ => wpi_mask (H := H) M t Φ) := by
  constructor
  intro n Φ₁ Φ₂ HΦ
  apply BIFUpdate.ne.ne
  apply NonExpansive.ne
  exact λ v => BIFUpdate.ne.ne (HΦ v)

end wpi_tree_mask_def

macro:20 "WPi " t:term:20 " @> " H:term:20 ";" M:term:20 " {{ " Φ:term:20 " }}" : term => `(wpi_mask (H := $H) $M $t $Φ)
macro:20 "WPi " t:term:20 " @> " H:term:20 ";" M:term:20 " {{ " v:ident " , " Q:term:20 " }}" : term => `(wpi_mask (H := $H) $M $t <| λ $v => $Q)

section wpi_tree_mask_def

open OFE

variable {E} {M : CoPset} {H : IHandler (PROP := PROP) E}

theorem wpi_empty_mask_equiv {R} (t : ITree E R) (Φ : R → PROP) :
    (WPi t @> H;∅ {{ Φ }}) ⊣⊢ (WPi t @> H {{ Φ }}) :=
  (equiv_iff.mp <| BIFUpdate.ne.eqv <| equiv_iff.mpr <|
    wpi_update_post_emp_mask H t).trans <| wpi_update_emp_mask H Φ t

theorem wpi_unfold {R} (t : ITree E R) Φ :
    (WPi t @> H;∅ {{ Φ }}) ⊣⊢ ((wpiF H <| λ t Φ => WPi t @> H;∅ {{ Φ }}) t Φ) := by
  apply (wpi_empty_mask_equiv t Φ).trans; apply (wpi_unfold_emp_mask H t Φ).trans
  isplit <;> iintro Hwp
  · iapply wpiF_mono (H := H) <| wpi H
    · iintro !> %t %Φ Hwp; iapply (wpi_empty_mask_equiv (H := H) t Φ).mpr $$ Hwp
    · iexact Hwp
  · iapply wpiF_mono (H := H) _ <| wpi H
    · iintro !> %t %Φ Hwp; iapply (wpi_empty_mask_equiv (H := H) t Φ).mp $$ Hwp
    · iexact Hwp

instance wpi_ne {R} (t : ITree E R) : NonExpansive (λ Φ => WPi t @> H; M {{ Φ }}) :=
  wpi_mask_ne M H t

theorem wpi_mask_post_congr (t : ITree E R) {Φ Ψ : R → PROP}
    (HΦ : Φ ≡ Ψ) :
    (WPi t @> H; M {{ Φ }}) ⊣⊢ (WPi t @> H; M {{ Ψ }}) :=
  equiv_iff.mp <| NonExpansive.eqv (f := λ Φ => WPi t @> H; M {{ Φ }}) HΦ

end wpi_tree_mask_def

-- Induction principles for WPi (mask version)
section wp_itree_induction

open OFE ITree

variable {E R} {H : IHandler (PROP := PROP) E} (G : ITree E R → (R → PROP) → PROP)

theorem wpi_ind : (∀ t, NonExpansive (G t)) →
    □ (∀ t Φ, wpiF H (λ t' Ψ => iprop(G t' Ψ ∧ (WPi t' @> H;∅ {{ Ψ }}))) t Φ -∗ G t Φ) ⊢
    ∀ t Φ, (WPi t @> H;∅ {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HPre %t %Φ Hwp
  iapply wpi_ind_emp_mask H G Hne
  · iintro !> %t %Φ Hx; iapply HPre; iapply wpiF_mono H <| λ t' Ψ => iprop(G t' Ψ ∧ (WPi t' @> H {{ Ψ }}))
    · iintro !> %t' %Φ' Hpair; isplit
      · iapply and_elim_l $$ Hpair
      · iapply wpi_empty_mask_equiv; iapply and_elim_r $$ Hpair
    · iexact Hx
  · iapply wpi_empty_mask_equiv $$ Hwp

theorem wpi_iter : (∀ t, NonExpansive (G t)) →
    □ (∀ t Φ, wpiF H G t Φ -∗ G t Φ) ⊢
    ∀ t Φ, (WPi t @> H;∅ {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HRet %t %Φ Hwp
  iapply wpi_iter_emp_mask H G Hne $$ HRet
  iapply wpi_empty_mask_equiv $$ Hwp

theorem wpi_iter' : (∀ t, OFE.NonExpansive (G t)) →
    ⊢ □ (∀ Φ r, (|={∅}=> Φ r) -∗ G (ret r) Φ) -∗
      □ (∀ Φ t, (|={∅}=> G t Φ) -∗ G (tau t) Φ) -∗
      □ (∀ Φ i k, (|={∅}=> H.ihandle i
          (λ a => G (k a) Φ)
          (λ a => iprop(|={⊤,∅}=> G (k a) (λ _ => iprop(False))))) -∗
            G (vis i k) Φ) -∗
      ∀ t Φ, (WPi t @> H;∅ {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HRet #HTau #HVis %t %Φ Hwp
  iapply wpi_iter_emp_mask' H G Hne
  · iexact HRet
  · iexact HTau
  · iexact HVis
  · iapply wpi_empty_mask_equiv $$ Hwp

end wp_itree_induction

section wp_itree_derived

open ITree BIUpdate OFE

variable {E R} {H : IHandler (PROP := PROP) E} (t : ITree E R)

theorem wpi_wand (M : CoPset) (Φ Ψ : R → PROP) :
    ⊢ (∀ r, iprop(Φ r -∗ Ψ r)) -∗
      (WPi t @> H; M {{ Φ }}) -∗
      (WPi t @> H; M {{ Ψ }}) := by
  iintro Hwand Hwp; unfold wpi_mask; imod Hwp; imodintro;
  iapply wpi_wand_emp_mask _ _  <| λ v => iprop(|={∅,M}=> Φ v) $$ [Hwand]
  · iintro %r HΦ; imod HΦ; imodintro; iapply Hwand $$ HΦ
  · iexact Hwp

theorem wpi_bind {A} (t : ITree E A) (k : A → ITree E R) (M : CoPset) (Φ : R → PROP) :
    ⊢ (WPi t @> H; M {{ r, WPi (k r) @> H; M {{ Φ }} }}) -∗
      (WPi (t >>= k) @> H; M {{ Φ }}) := by
  iintro Hwp
  -- Lost Coq step: the original proof uses `iMod`/`iModIntro` with fancy
  -- updates while following the `wpi_bind_emp_mask` argument.
  sorry

theorem fupd_wpi (M : CoPset) (Φ : R → PROP) :
    (|={M}=> WPi t @> H; M {{ Φ }}) ⊣⊢
    (WPi t @> H; M {{ Φ }}) := by
  isplit
  · iintro Hwp
    -- Lost Coq step: need to eliminate a fancy update in front of `wpi_mask`.
    sorry
  · iintro Hwp
    -- Lost Coq step: need to re-introduce a fancy update around `wpi_mask`.
    sorry

theorem wpi_fupd (M : CoPset) (Φ : R → PROP) :
    (WPi t @> H; M {{ v, iprop(|={M}=> Φ v) }}) ⊣⊢
    (WPi t @> H; M {{ Φ }}) := by
  isplit <;> iintro Hwp
  · iapply wpi_wand t M <| λ v => iprop(|={M}=> Φ v)
    · iintro %r HΦ
      -- Lost Coq step: collapse `|={M}=> |={M}=> Φ r` to `|={M}=> Φ r`.
      sorry
    · iexact Hwp
  · iapply wpi_wand t M Φ <| λ v => iprop(|={M}=> Φ v)
    · iintro %r HΦ
      -- Lost Coq step: introduce `|={M}=>` around `Φ r`.
      sorry
    · iexact Hwp

end wp_itree_derived

section wp_itree_mask_manipulation

open ITree BIUpdate OFE

variable {E R} {H : IHandler (PROP := PROP) E}

theorem wpi_shift_mask (M' M : CoPset) (Φ : R → PROP) (t : ITree E R) :
    ⊢ (|={M, M'}=> WPi t @> H; M' {{ v, iprop(|={M', M}=> Φ v) }}) -∗
      (WPi t @> H; M {{ Φ }}) := by
  iintro Hwp
  -- Lost Coq step: the original proof performs two consecutive `iMod`
  -- eliminations on fancy updates before applying `wpi_wand_emp_mask`.
  sorry

theorem wpi_empty_mask (M : CoPset) (Φ : R → PROP) (t : ITree E R) :
    (|={M, ∅}=> WPi t @> H; ∅ {{ v, iprop(|={∅, M}=> Φ v) }}) ⊣⊢
    (WPi t @> H; M {{ Φ }}) := by
  isplit
  · iintro Hwp; iapply wpi_shift_mask ∅ M Φ t $$ Hwp
  · iintro Hwp
    -- Lost Coq step: the original proof uses `iMod` to open the masked
    -- hypothesis before re-closing it around `wpi_mask`.
    sorry

theorem wpi_empty_mask_false (M : CoPset) (t : ITree E R) :
    ⊢ (|={M, ∅}=> WPi t @> H; ∅ {{ λ _ => iprop(False) }}) -∗
      (WPi t @> H; M {{ λ _ => iprop(False) }}) := by
  iintro Hwp
  -- Lost Coq step: after clearing the mask we still need to normalize
  -- `|={∅, M}=> False` back to `False`, which again requires fancy-update
  -- elimination support in the proof mode.
  sorry

theorem wpi_mask_mono (M M' : CoPset) (Φ : R → PROP) (t : ITree E R) :
    M ⊆ M' →
    ⊢ (WPi t @> H; M {{ Φ }}) -∗
      (WPi t @> H; M' {{ Φ }}) := by
  intro Hsubset
  iintro Hwp
  -- Lost Coq step: the original proof uses `fupd_mask_intro`, which does
  -- not yet exist as a derived lemma in this Lean development.
  sorry

end wp_itree_mask_manipulation

section wp_itree_invariant

-- Invariant rules from the Coq development are omitted for now.
-- This Lean repository does not yet expose an invariant API with
-- `inv`, `inv_acc`, or `inv_acc_timeless`, so the corresponding masked
-- WPi lemmas cannot be stated here yet.

end wp_itree_invariant

section wp_itree_stepping

open ITree BIUpdate OFE

variable {E} {H : IHandler (PROP := PROP) E}

theorem wpi_ret' {R} (M : CoPset) (Φ : R → PROP) (r : R) :
    (|={M}=> Φ r) ⊣⊢
    (WPi (ret r) @> H; M {{ Φ }}) := by
  -- Lost Coq step: the original proof combines `wpi_ret_emp_mask'` with
  -- fancy-mask introduction and elimination.
  sorry

theorem wpi_ret {R} (M : CoPset) (Φ : R → PROP) (r : R) :
    ⊢ Φ r -∗
      (WPi (ret r) @> H; M {{ Φ }}) := by
  iintro HΦ
  -- Lost Coq step: need to introduce `|={M}=> Φ r` before using `wpi_ret'`.
  sorry

theorem wpi_tau {R} (M : CoPset) (Φ : R → PROP) (t : ITree E R) :
    (WPi t @> H; M {{ λ v => Φ v }}) ⊣⊢
    (WPi (tau t) @> H; M {{ Φ }}) := by
  -- Lost Coq step: the original proof rewrites `wpi_mask` and then uses
  -- the unmasked `wpi_tau_emp_mask`.
  sorry

theorem wpi_vis' {R} (M : CoPset) (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    (|={M, ∅}=> H.ihandle i
      (λ a => WPi (k a) @> H; ∅ {{ v, iprop(|={∅, M}=> Φ v) }})
      (λ a => WPi (k a) @> H; CoPset.full {{ λ _ => iprop(False) }})) ⊣⊢
    (WPi (vis i k) @> H; M {{ Φ }}) := by
  -- Lost Coq step: the original proof relies on `iMod`/`iModIntro` with
  -- fancy updates and an `ihandle_mono` transport.
  sorry

theorem wpi_vis {R} (M : CoPset) (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    ⊢ (|={M, ∅}=> H.ihandle i
      (λ a => WPi (k a) @> H; ∅ {{ v, iprop(|={∅, M}=> Φ v) }})
      (λ a => WPi (k a) @> H; CoPset.full {{ λ _ => iprop(False) }})) -∗
      (WPi (vis i k) @> H; M {{ Φ }}) := by
  iintro HH; iapply (wpi_vis' M Φ i k).mp $$ HH

theorem wpi_trigger {E'} [E' -< E] (H' : IHandler (PROP := PROP) E') [InH H' H]
    (M : CoPset) (i : E'.I) (Φ : E'.O i → PROP) :
    ⊢ (|={M, ∅}=> H'.ihandle i
      (λ a => iprop(|={∅, M}=> Φ a))
      (λ _ => iprop(False))) -∗
      (WPi (ITree.trigger E' i) @> H; M {{ Φ }}) := by
  iintro HH
  -- Lost Coq step: this proof depends on the masked `wpi_vis` rule together
  -- with fancy-update manipulations inside the event handler.
  sorry

end wp_itree_stepping

section wp_itree_structural

open ITree BIUpdate OFE

variable {E R} {H : IHandler (PROP := PROP) E} (Φ : R → PROP) (t : ITree E R)

theorem wpi_frame_l (M : CoPset) (P : PROP) :
    ⊢ P ∗ (WPi t @> H; M {{ Φ }}) -∗
      (WPi t @> H; M {{ v, iprop(P ∗ Φ v) }}) := by
  iintro ⟨Hp, Hwp⟩
  iapply wpi_wand t M Φ $$ [Hp]
  · iintro %r Hr; isplitl [Hp]; iexact Hp; iexact Hr
  · iexact Hwp

theorem wpi_frame_r (M : CoPset) (P : PROP) :
    ⊢ (WPi t @> H; M {{ Φ }}) ∗ P -∗
      (WPi t @> H; M {{ v, iprop(Φ v ∗ P) }}) := by
  iintro ⟨Hwp, Hp⟩
  iapply wpi_wand t M Φ $$ [Hp]
  · iintro %r Hr; isplitl [Hr]; iexact Hr; iexact Hp
  · iexact Hwp

end wp_itree_structural
