import Carte.Core.Handler
import Carte.Core.ITree
import Carte.Core.Wpi
import Iris.ProofMode
import Iris.BI.Lib.Fixpoint
import ITree.Definition
import ITree.Effect

open Iris BI ITree

variable {PROP : Type _} [BI PROP] [BIUpdate PROP] [BIFUpdate PROP]

section wpi_tree_mask_def

variable {E} {H : IHandler (PROP := PROP) E}

open OFE

def wpi_mask (M : CoPset) (t : ITree E R) (Φ : R → PROP) : PROP :=
  iprop(|={M, ∅}=> wpi H t (fun v => iprop(|={∅, M}=> Φ v)))

instance wpi_mask_ne (M : CoPset) (t : ITree E R) :
    OFE.NonExpansive (fun Φ => wpi_mask (H := H) M t Φ) := by
  constructor
  intro n Φ₁ Φ₂ HΦ
  apply BIFUpdate.ne.ne
  apply NonExpansive.ne
  exact fun v => BIFUpdate.ne.ne (HΦ v)

end wpi_tree_mask_def

macro:20 "WPi " t:term:20 " @> " H:term:20 " ; " M:term:20 " {{ " Φ:term:20 " }}" : term => `(wpi_mask (H := $H) $M $t $Φ)
macro:20 "WPi " t:term:20 " @> " H:term:20 " ; " M:term:20 " {{ " v:ident " , " Q:term:20 " }}" : term => `(wpi_mask (H := $H) $M $t <| fun $v => $Q)

section wpi_tree_mask_def

open OFE

variable {E} {H : IHandler (PROP := PROP) E}

-- [Warning]: Helper function, only for the current development stage
-- After fancy update finished, if we can replace the basic update in Wpi
-- This thoeorem does not need any longer
theorem hmask_equiv {R} (t : ITree E R) Φ : (WPi t @> H; ∅ {{ Φ }}) ⊣⊢ wpi H t Φ := by
  have fup_bup_equiv : ∀ {P : PROP}, iprop(|={∅, ∅}=> P) ⊣⊢ iprop(|==> P) := by
    sorry
  apply fup_bup_equiv.trans
  have hpost := wpi_post_congr H t (fun v => equiv_iff.mpr <| fup_bup_equiv (P := Φ v))
  exact equiv_iff.mp <| (BIUpdate.bupd_ne.eqv <| equiv_iff.mpr hpost).trans <|
      (BIUpdate.bupd_ne.eqv <| equiv_iff.mpr <| wpi_update_post_emp_mask H t (Φ := Φ)).trans <|
      equiv_iff.mpr <| wpi_update_emp_mask H Φ t

theorem wpi_unfold {R} (t : ITree E R) Φ :
    (WPi t @> H;∅ {{ Φ }}) ⊣⊢ ((wpiF H <| fun t Φ => WPi t @> H;∅ {{ Φ }}) t Φ) := by
  apply (hmask_equiv t Φ).trans; apply (wpi_unfold_emp_mask H t Φ).trans
  isplit
  · iintro Hwp; iapply wpiF_mono H (wpi H) <| fun t Φ => WPi t @> H; ∅ {{ Φ }}
    · iintro !> %t %Φ Hw; iapply (hmask_equiv t Φ).mpr $$ Hw
    · iexact Hwp
  · iintro Hwp; iapply wpiF_mono H (fun t Φ => WPi t @> H; ∅ {{ Φ }}) <| wpi H
    · iintro !> %t %Φ Hw; iapply (hmask_equiv t Φ).mp $$ Hw
    · iexact Hwp

instance (M : CoPset)  (t : ITree E R) : NonExpansive (fun Φ => WPi t @> H; M {{ Φ }}) :=
  wpi_mask_ne (H := H) M t

theorem wpi_mask_post_congr (M : CoPset) (t : ITree E R) {Φ Ψ : R → PROP}
    (HΦ : Φ ≡ Ψ) :
    (WPi t @> H; M {{ Φ }}) ⊣⊢ (WPi t @> H; M {{ Ψ }}) :=
  equiv_iff.mp <| NonExpansive.eqv (f := fun Φ => WPi t @> H; M {{ Φ }}) HΦ

end wpi_tree_mask_def

-- Induction principles for WPi (mask version)
section wp_itree_induction

open OFE ITree

variable {E R} {H : IHandler (PROP := PROP) E} (G : ITree E R → (R → PROP) → PROP)

theorem wpi_ind : (∀ t, NonExpansive (G t)) →
    ⊢ □ (∀ t Φ, wpiF H (fun t' Ψ => iprop(G t' Ψ ∧ (WPi t' @> H;∅ {{ Ψ }}))) t Φ -∗ G t Φ) -∗
      ∀ t Φ, (WPi t @> H;∅ {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HPre %t %Φ Hwp
  iapply wpi_ind_emp_mask H G Hne
  . iintro !> %t %Φ Hx; iapply HPre; iapply wpiF_mono H <| fun t' Ψ => iprop(G t' Ψ ∧ (WPi t' @> H {{ Ψ }}))
    . iintro !> %t' %Φ' Hpair; isplit
      . iapply and_elim_l $$ Hpair
      . iapply (hmask_equiv t' Φ').mpr; iapply and_elim_r $$ Hpair
    . iexact Hx
  . iapply hmask_equiv t Φ $$ Hwp

theorem wpi_iter : (∀ t, NonExpansive (G t)) →
    ⊢ □ (∀ t Φ, wpiF H G t Φ -∗ G t Φ) -∗
      ∀ t Φ, (WPi t @> H;∅ {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HRet %t %Φ Hwp
  iapply wpi_iter_emp_mask H G Hne $$ HRet
  iapply hmask_equiv $$ Hwp

theorem wpi_iter' : (∀ t, OFE.NonExpansive (G t)) →
    ⊢ □ (∀ Φ r, (|==> Φ r) -∗ G (ret r) Φ) -∗
      □ (∀ Φ t, (|==> G t Φ) -∗ G (tau t) Φ) -∗
      □ (∀ Φ i k, (|==> H.ihandle i (fun a => G (k a) Φ)
          (fun a => iprop(|==> G (k a) (fun _ => iprop(False))))) -∗
        G (vis i k) Φ) -∗
      ∀ t Φ, (WPi t @> H;∅ {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HRet #HTau #HVis %t %Φ Hwp
  iapply wpi_iter_emp_mask' H G Hne $$ HRet, HTau, HVis
  iapply hmask_equiv $$ Hwp

end wp_itree_induction

-- Structural rules for WPi (mask version)
section wp_itree_induction

variable {E R} {H : IHandler (PROP := PROP) E} (G : ITree E R → (R → PROP) → PROP)

theorem wpi_wand (t : ITree E R) (M : CoPset) Φ Ψ :
    ⊢ (∀ r, iprop(Φ r -∗ Ψ r)) -∗
      (WPi t @> H;M {{ Φ }}) -∗
      (WPi t @> H;M {{ Ψ }}) := by
  iintro Hwand Hwp;
  -- TODO: Unprovable
  sorry

theorem wpi_bind (t : ITree E A) (k : A → ITree E R) M Φ:
    (WPi t @> H; M {{ r, WPi (k r) @> H; M {{ Φ }} }}) ⊢
    (WPi (t >>= k) @> H; M {{ Φ }}) := by
  iintro Hwp;
  -- TODO: Unprovable, waiting for imod support Fancy update
  sorry

theorem wpi_fupd M Φ (t : ITree E R) :
    (|={M}=> WPi t @> H; M {{ Φ }}) ⊣⊢
    (WPi t @> H; M {{ Φ }}) := by
  isplit
  . iintro Hwp
    unfold wpi_mask
    -- TODO: imod Hwp
    sorry
  . iintro Hwp
    -- TODO: imodintro
    sorry

theorem wpi_fupd_post M Φ (t : ITree E R) :
    (WPi t @> H; M {{ v, iprop(|={M}=> Φ v) }}) ⊣⊢
    (WPi t @> H; M {{ Φ }}) := by
  sorry

end wp_itree_induction
