import Carte.Handler
import Iris.ProofMode
import Iris.BI.Lib.Fixpoint
import ITree.Definition
import ITree.Effect

open Iris BI ITree

section wp_itree

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
instance {R} : OFE (LeibnizO (ITree E R) × (R → PROP) → PROP) := by
  infer_instance

-- set_option trace.Meta.synthInstance true in
-- instance {R} : OFE.NonExpansive (wpiF' H) where
--   ne {n wp1 wp2} Hwp x := by
--     sorry


theorem wpiF_mono {R} (wp1 wp2 : ITree E R → (R → PROP) → PROP) :
    ⊢ □ (∀ t Φ, wp1 t Φ -∗ wp2 t Φ) -∗
      ∀ t Φ, wpiF H wp1 t Φ -∗ wpiF H wp2 t Φ := by
  iintro □Hwand %t %Φ Hwp
  unfold wpiF
  cases t.unfold <;> simp only
  case ret => iexact Hwp
  case tau t' => imod Hwp; imodintro; irevert Hwp; iexact Hwand
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
    intros Φ HΦ
    -- unfold OFE.NonExpansive
    sorry

def wpi {E R} (H : IHandler (PROP := PROP) E) (t : ITree E R) (Φ : R → PROP) : PROP :=
  bi_least_fixpoint (wpiF' H) (⟨t⟩, Φ)

-- set_option trace.Meta.synthInstance true in
-- theorem wpiF_ne {E R n} (H : IHandler (PROP := PROP) E)
--     (wp1 wp2 : ITree E R → (R → PROP) → PROP) :
--     ∀ t1 t2 (Φ1 Φ2 : R → PROP), t1 ≡{n}≡ t2 → Φ1 ≡{n}≡ Φ2 → wpiF H wp1 t1 ≡{n}≡ wpiF H wp2 t2 := by
--   intros t1 t2 Φ1 Φ2 Ht HΦ
--   subst Ht
--   unfold wpiF at ⊢
--   apply OFE.NonExpansive.ne (f := BUpd.bupd (PROP := PROP))

--   iintro
-- set_option pp.all true in

-- theorem wpi_unfold_mask H (t : ITree E R) Φ : wpi H t Φ ⊣⊢ wpiF H (wpi H) t Φ := by
--   sorry

end wp_itree
