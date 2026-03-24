import Carte.Handler
import Iris.ProofMode
import Iris.BI.Lib.Fixpoint
import ITree.Definition
import ITree.Effect

open Iris BI ITree

section wp_itree_def

variable {E} {PROP : Type _} [BI PROP] [BIUpdate PROP] (H : IHandler (PROP := PROP) E)

-- The definition of the weakest precondition, prior to taking the fixpoint.
def wpiF {R} (wpi : ITree E R → (R → PROP) → PROP) :
    ITree E R → (R → PROP) → PROP :=
  fun t Φ =>
    iprop(
      |==> match t.unfold with
      | ITreeF.ret r => Φ r
      | ITreeF.tau t' => wpi t' Φ
      | ITreeF.vis i k =>
          H.ihandle i
            (fun a => wpi (k a) Φ)
            (fun a => iprop(|==> wpi (k a) (fun _ => iprop(False))))
    )

-- [LeibnizO] wrapped version of wpiF
def wpiF' {R} (wpi : LeibnizO (ITree E R) × (R → PROP) → PROP) :
    LeibnizO (ITree E R) × (R → PROP) → PROP :=
  fun ⟨t, Φ⟩ => wpiF H (fun t Φ => wpi (⟨t⟩, Φ)) t.car Φ

/-- Helper function for proving BIMonoPred -/
instance wpiF'_ne {R} : OFE.NonExpansive (wpiF' H (R := R)) := by
  constructor
  intro n wp1 wp2 Hwp ⟨t, Φ⟩
  cases h : t.car.unfold <;> simp [wpiF', wpiF, h]
  case tau t' => exact BIUpdate.bupd_ne.ne <| Hwp (⟨t'⟩, Φ)
  case vis i k =>
    apply BIUpdate.bupd_ne.ne
    apply OFE.NonExpansive₂.ne (f := H.ihandle i)
    · intro a; apply Hwp (⟨k a⟩, Φ)
    · intro a; apply BIUpdate.bupd_ne.ne <| Hwp (⟨k a⟩, fun _ => iprop(False))

theorem wpiF_mono {R} (wp1 wp2 : ITree E R → (R → PROP) → PROP) :
    ⊢ □ (∀ t Φ, wp1 t Φ -∗ wp2 t Φ) -∗
      ∀ t Φ, wpiF H wp1 t Φ -∗ wpiF H wp2 t Φ := by
  iintro □Hwand %t %Φ Hwp
  unfold wpiF
  cases t.unfold <;> simp
  case ret => iexact Hwp
  case tau t' => imod Hwp; imodintro; iapply Hwand $$ Hwp
  case vis i k =>
    imod Hwp; imodintro; iapply H.ihandle_mono
    · iintro %a Hk; iapply Hwand $$ Hk
    · iintro !> %a Hk; imod Hk; imodintro; iapply Hwand $$ Hk
    · iexact Hwp

theorem wpiF'_mono {R} (wp1 wp2 : LeibnizO (ITree E R) × (R → PROP) → PROP) :
    ⊢ □ (∀ t Φ, wp1 (t, Φ) -∗ wp2 (t, Φ)) -∗
      ∀ t Φ, wpiF' H wp1 (t, Φ) -∗ wpiF' H wp2 (t, Φ) := by
  simp [wpiF']
  iintro □Hwand %t' %Φ Hwp
  cases t' with | mk t =>
    simp only
    iapply wpiF_mono (wp1 := fun t Φ => wp1 ({ car := t }, Φ)) (wp2 := fun t Φ => wp2 ({ car := t }, Φ))
    . iintro !> %t' %Φ' Hw; iapply Hwand $$ %⟨t'⟩, %Φ', Hw
    . iexact Hwp
/-- End of Helper -/

instance {R} : BIMonoPred (λ wp_itree : LeibnizO (ITree E R) × (R → PROP) → PROP => wpiF' H wp_itree) where
  mono_pred := by
    iintro %Φ %Ψ %HΦ %HΨ □H %pair Hsim
    iapply wpiF'_mono (wp1 := Φ) (wp2 := Ψ)
    . iintro !> %t %Φ1; iapply H
    . iexact Hsim
  mono_pred_ne := by
    intro wp Hwp; constructor; intro n ⟨t1, Ψ1⟩ ⟨t2, Ψ2⟩ ⟨Ht, HΨ⟩
    simp at Ht HΨ; subst Ht
    cases h : t1.car.unfold <;> simp [wpiF', wpiF, h]
    case ret r => exact BIUpdate.bupd_ne.ne (HΨ r)
    case tau t' => exact BIUpdate.bupd_ne.ne <| Hwp.ne ⟨rfl, HΨ⟩
    case vis i k =>
      apply BIUpdate.bupd_ne.ne
      apply OFE.NonExpansive₂.ne (f := H.ihandle i)
      · intro a; exact Hwp.ne ⟨rfl, HΨ⟩
      · intro a; apply BIUpdate.bupd_ne.ne <| Hwp.ne ⟨rfl, fun _ => .rfl⟩

/-- The weakest precondition is defined as the least fixpoint of [wpiF']. -/
def wpi {E R} (H : IHandler (PROP := PROP) E) (t : ITree E R) (Φ : R → PROP) : PROP :=
  bi_least_fixpoint (wpiF' H) (⟨t⟩, Φ)

/-- Unfolding [wpi] reveals one step of the weakest precondition functional. -/
theorem wpi_unfold_mask {R} (t : ITree E R) Φ : wpi H t Φ ⊣⊢ wpiF H (wpi H) t Φ := by
  apply equiv_iff.mp
  apply least_fixpoint_unfold

end wp_itree_def

macro:20 "WPi " t:term:20 " @ " H:term:20 " {{ " Φ:term:20 " }}" : term => `(wpi $H $t $Φ)
macro:20 "WPi " t:term:20 " @ " H:term:20 " {{ " v:ident " , " Q:term:20 " }}" : term => `(wpi $H $t (fun $v => $Q))
