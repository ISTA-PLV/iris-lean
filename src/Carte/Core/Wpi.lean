import Carte.Core.Handler
import Carte.Core.ITree
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
theorem wpi_unfold_emp_mask {R} (t : ITree E R) Φ : wpi H t Φ ⊣⊢ wpiF H (wpi H) t Φ := by
  apply equiv_iff.mp
  apply least_fixpoint_unfold

end wp_itree_def

macro:20 "WPi " t:term:20 " @> " H:term:20 " {{ " Φ:term:20 " }}" : term => `(wpi $H $t $Φ)
macro:20 "WPi " t:term:20 " @> " H:term:20 " {{ " v:ident " , " Q:term:20 " }}" : term => `(wpi $H $t (fun $v => $Q))

section wp_itree_def

open OFE

variable {E R} {PROP : Type _} [BI PROP] [BIUpdate PROP]
  (H : IHandler (PROP := PROP) E) (t : ITree E R)

instance : NonExpansive (fun Φ => WPi t @> H {{ Φ }}) := by
  constructor
  intro n Φ₁ Φ₂ HΦ
  exact NonExpansive.ne (f := bi_least_fixpoint (wpiF' H)) ⟨rfl, HΦ⟩

theorem wpi_post_congr {Φ Ψ : R → PROP} (HΦ : Φ ≡ Ψ) :
    (WPi t @> H {{ Φ }}) ⊣⊢ (WPi t @> H {{ Ψ }}) :=
  equiv_iff.mp <| NonExpansive.eqv (f := fun Φ => WPi t @> H {{ Φ }}) HΦ

end wp_itree_def

-- Stepping Rules for WPi
section wp_itree_stepping

open ITree BIUpdate OFE

variable {E} {PROP : Type _} [BI PROP] [BIUpdate PROP] (H : IHandler (PROP := PROP) E)

-- Lean's `rw` does not work with BI equivalences, so we package this update-absorption step as a lemma.
theorem wpi_update_emp_mask {R} (Φ : R → PROP) (t : ITree E R) :
    (|==> wpi H t Φ) ⊣⊢ wpi H t Φ := by
  have hUnfold := by simpa [wpiF] using (equiv_iff.mpr <| wpi_unfold_emp_mask H t Φ)
  exact equiv_iff.mp <|
    (bupd_ne.eqv hUnfold).trans <|
    (equiv_iff.mpr <| bupd_idem).trans hUnfold.symm

theorem wpi_ret_emp_mask' {R} (Φ : R → PROP) (r : R) :
    (|==> Φ r) ⊣⊢ (WPi (ret r) @> H {{ Φ }}) :=
  (wpi_unfold_emp_mask H (ret r) Φ).symm

theorem wpi_ret_emp_mask {R} (Φ : R → PROP) (r : R) :
    ⊢ Φ r -∗ (WPi (ret r) @> H {{ Φ }}) := by
  iintro HΦ; iapply (wpi_ret_emp_mask' H Φ r).mp; imodintro; iexact HΦ

theorem wpi_tau_emp_mask {R} (Φ : R → PROP) (t : ITree E R) :
    (WPi (tau t) @> H {{ Φ }}) ⊣⊢ (WPi t @> H {{ Φ }}) :=
  (wpi_unfold_emp_mask H (tau t) Φ).trans <| wpi_update_emp_mask H Φ t

theorem wpi_vis_emp_mask' {R} (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    (|==> H.ihandle i
      (fun a => WPi k a @> H {{ Φ }})
      (fun a => iprop(|==> (WPi k a @> H {{ fun _ => iprop(False) }})))) ⊣⊢
    (WPi (vis i k) @> H {{ Φ }}) := by
  refine BiEntails.trans ?_ (wpi_unfold_emp_mask H (vis i k) Φ).symm
  simp [wpiF]

theorem wpi_vis_emp_mask {R} (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    ⊢ H.ihandle i
      (fun a => WPi k a @> H {{ Φ }})
      (fun a => iprop(|==> (WPi k a @> H {{ fun _ => iprop(False) }}))) -∗
    (WPi (vis i k) @> H {{ Φ }}) := by
  iintro Hwp; iapply (wpi_vis_emp_mask' H Φ i k).mp; imodintro; iexact Hwp

instance uncurry_G_ne {R} (G : ITree E R → (R → PROP) → PROP) :
    (∀ t, NonExpansive (G t)) →
    NonExpansive (fun ((t, Φ) : LeibnizO (ITree E R) × (R → PROP)) => G t.car Φ) := by
  intro Hne; constructor
  intro n ⟨t₁, Φ₁⟩ ⟨t₂, Φ₂⟩ ⟨Ht, HΦ⟩; simp at Ht HΦ
  cases t₁ with | mk t₁ =>
  cases t₂ with | mk t₂ =>
  cases Leibniz.eq_of_eqv (Discrete.discrete Ht)
  exact (Hne t₁).ne HΦ

end wp_itree_stepping

-- Induction principles for WPi
section wp_itree_induction

open ITree BIUpdate OFE

variable {E R} {PROP : Type _} [BI PROP] [BIUpdate PROP]
  (H : IHandler (PROP := PROP) E) (G : ITree E R → (R → PROP) → PROP)

theorem wpi_ind_emp_mask : (∀ t, NonExpansive (G t)) →
    ⊢ □ (∀ t Φ, wpiF H (fun t' Ψ => iprop(G t' Ψ ∧ (WPi t' @> H {{Ψ}}))) t Φ -∗ G t Φ) -∗
      ∀ t Φ, (WPi t @> H {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HPre %t %Φ
  let G' : LeibnizO (ITree E R) × (R → PROP) → PROP := fun ⟨t, Φ⟩ => G t.car Φ
  haveI _ := uncurry_G_ne G Hne
  ihave HPre' : □ (∀ y, wpiF' H (fun x => iprop(G' x ∧ bi_least_fixpoint (wpiF' H) x)) y -∗ G' y) $$ []
  · iintro !> %y
    cases y with | mk t' Ψ =>
      simp [G', wpiF', wpi] at ⊢
      iintro Hx
      iapply HPre $$ Hx
  simp [wpi, G'] at ⊢
  iapply (least_fixpoint_ind (wpiF' H) G') $$ HPre', %(⟨t⟩, Φ)

theorem wpi_iter_emp_mask : (∀ t, NonExpansive (G t)) →
    ⊢ □ (∀ t Φ, wpiF H G t Φ -∗ G t Φ) -∗
      ∀ t Φ, (WPi t @> H {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HPre %t %Φ
  let G' : LeibnizO (ITree E R) × (R → PROP) → PROP := fun ⟨t, Φ⟩ => G t.car Φ
  haveI _ := uncurry_G_ne G Hne
  ihave HPre' : □ (∀ y, wpiF' H G' y -∗ G' y) $$ []
  · iintro !> %y
    cases y with | mk t' Ψ =>
      simp [G', wpiF'] at ⊢
      iintro Hx
      iapply HPre $$ Hx
  simp [wpi, G'] at ⊢
  iapply least_fixpoint_iter <| wpiF' H $$ HPre', %(⟨t⟩, Φ)

theorem wpi_iter_emp_mask' : (∀ t, OFE.NonExpansive (G t)) →
    ⊢ □ (∀ Φ r, (|==> Φ r) -∗ G (ret r) Φ) -∗
      □ (∀ Φ t, (|==> G t Φ) -∗ G (tau t) Φ) -∗
      □ (∀ Φ i k, (|==> H.ihandle i (fun a => G (k a) Φ)
          (fun a => iprop(|==> G (k a) (fun _ => iprop(False))))) -∗
        G (vis i k) Φ) -∗
      ∀ t Φ, (WPi t @> H {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HRet #HTau #HVis; iapply wpi_iter_emp_mask H G Hne;
  iintro !> %t %Φ
  rcases ITree.match_itree t with
    ⟨r, rfl⟩ | ⟨t', rfl⟩ | ⟨i, k, rfl⟩ <;> simp [wpiF] <;> iintro Hwp
  · iapply HRet $$ Hwp
  · iapply HTau $$ Hwp
  · iapply HVis $$ Hwp

end wp_itree_induction

-- Structual rules for WPi
section wp_itree_structural

open ITree BIUpdate OFE

end wp_itree_structural


-- Derived rules for WPi
section wp_itree_derived

open ITree BIUpdate OFE

end wp_itree_derived
