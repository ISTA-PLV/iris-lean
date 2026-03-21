import Carte.Handler
import Iris.ProofMode
import Iris.BI.Lib.Fixpoint
import ITree.Definition
import ITree.Effect

open Iris BI ITree

section wp_itree

variable {PROP : Type _} [BI PROP] [BUpd PROP]

-- The definition of the weakest precondition, prior to taking the fixpoint.
def wpiF {E R} (H : IHandler (PROP := PROP) E)
    (wpi : LeibnizO (ITree E R) → (R → PROP) → PROP) :
    LeibnizO (ITree E R) → (R → PROP) → PROP :=
  fun t Φ =>
    iprop(
      |==> match t.car.unfold with
      | ITreeF.ret r => Φ r
      | ITreeF.tau t' => wpi ⟨t'⟩ Φ
      | ITreeF.vis i k =>
          H.ihandle i
            (fun a => wpi ⟨k a⟩ Φ)
            (fun a => iprop(|==> wpi ⟨k a⟩ (fun _ => iprop(False))))
    )
def wpiF' {E R} (H : IHandler (PROP := PROP) E)
    (wpi : LeibnizO (ITree E R) × (R → PROP) → PROP) :
    LeibnizO (ITree E R) × (R → PROP) → PROP :=
  fun ⟨t, Φ⟩ => wpiF H (Function.curry wpi) t Φ

def wpi {E R} (H : IHandler (PROP := PROP) E) (t : ITree E R) (Φ : R → PROP) : PROP :=
    bi_least_fixpoint (wpiF' H) (⟨t⟩, Φ)

theorem wpiF_mono [BI PROP] [BUpd PROP]
    (H : IHandler (PROP := PROP) E)
    (wp1 wp2 : LeibnizO (ITree E R) → (R → PROP) → PROP) :
    ⊢ □ (∀ t Φ, wp1 t Φ -∗ wp2 t Φ) -∗
      ∀ t Φ, wpiF H wp1 t Φ -∗ wpiF H wp2 t Φ := by
  iintro □Hwand %t %Φ Hwp
  unfold wpiF at *
  sorry

-- theorem wpi_unfold_mask H (t : ITree E R) Φ : wpi H t Φ ⊣⊢ wpiF H (fun t Φ => wpi H t.car Φ) ⟨t⟩ Φ := by
--   sorry

end wp_itree
