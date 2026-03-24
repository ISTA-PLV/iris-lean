import Carte.Core.Handler
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

macro:20 "WPi " t:term:20 " @> " H:term:20 " {{ " Φ:term:20 " }}" : term => `(wpi $H $t $Φ)
macro:20 "WPi " t:term:20 " @> " H:term:20 " {{ " v:ident " , " Q:term:20 " }}" : term => `(wpi $H $t (fun $v => $Q))

section wp_itree

variable {E} {PROP : Type _} [BI PROP] [BIUpdate PROP] (H : IHandler (PROP := PROP) E)

/-- The mask-free unfolding lemma for [wpi]. -/
theorem wpi_unfold_emp_mask {R} (t : ITree E R) (Φ : R → PROP) :
    wpi H t Φ ⊣⊢ wpiF H (wpi H) t Φ :=
  wpi_unfold_mask (H := H) (t := t) (Φ := Φ)

instance wpi_ne_emp_mask {R} (t : ITree E R) :
    OFE.NonExpansive (fun Φ : R → PROP => WPi t @> H {{ Φ }}) := by
  constructor
  intro n Φ₁ Φ₂ HΦ
  exact OFE.NonExpansive.ne (f := bi_least_fixpoint (wpiF' H)) ⟨OFE.Dist.rfl, HΦ⟩

instance wpi_ne_emp_mask' {R} (Φ : R → PROP) :
    OFE.NonExpansive (fun t : LeibnizO (ITree E R) => wpi H t.car Φ) := by
  constructor
  intro n t₁ t₂ Ht
  exact OFE.NonExpansive.ne (f := bi_least_fixpoint (wpiF' H)) ⟨Ht, OFE.Dist.rfl⟩

theorem wpi_ret_emp_mask' {R} (Φ : R → PROP) (r : R) :
    (|==> Φ r) ⊣⊢ wpi H (ITree.ret r) Φ := by
  calc
    (|==> Φ r) ⊣⊢ wpiF H (wpi H) (ITree.ret r) Φ := by
      simp [wpiF]
    _ ⊣⊢ wpi H (ITree.ret r) Φ := (wpi_unfold_emp_mask (H := H) (t := ITree.ret r) (Φ := Φ)).symm

theorem wpi_ret_emp_mask {R} (Φ : R → PROP) (r : R) :
    ⊢ Φ r -∗ wpi H (ITree.ret r) Φ := by
  iintro HΦ
  iapply (wpi_ret_emp_mask' (H := H) (Φ := Φ) (r := r)).1
  imodintro
  iexact HΦ

theorem wpi_vis_emp_mask' {R} (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    (|==> H.ihandle i
      (fun a => wpi H (k a) Φ)
      (fun a => iprop(|==> wpi H (k a) (fun _ => iprop(False))))) ⊣⊢
    wpi H (ITree.vis i k) Φ := by
  calc
    (|==> H.ihandle i
      (fun a => wpi H (k a) Φ)
      (fun a => iprop(|==> wpi H (k a) (fun _ => iprop(False))))) ⊣⊢
        wpiF H (wpi H) (ITree.vis i k) Φ := by
          simp [wpiF]
    _ ⊣⊢ wpi H (ITree.vis i k) Φ := (wpi_unfold_emp_mask (H := H) (t := ITree.vis i k) (Φ := Φ)).symm

theorem wpi_vis_emp_mask {R} (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    ⊢ H.ihandle i
      (fun a => wpi H (k a) Φ)
      (fun a => iprop(|==> wpi H (k a) (fun _ => iprop(False)))) -∗
    wpi H (ITree.vis i k) Φ := by
  iintro Hwp
  iapply (wpi_vis_emp_mask' (H := H) (Φ := Φ) (i := i) (k := k)).1
  imodintro
  iexact Hwp

theorem wpi_update_emp_mask {R} (Φ : R → PROP) (t : ITree E R) :
    (|==> wpi H t Φ) ⊣⊢ wpi H t Φ := by
  let P : PROP := iprop(
    match t.unfold with
    | ITreeF.ret r => Φ r
    | ITreeF.tau t' => wpi H t' Φ
    | ITreeF.vis i k =>
        H.ihandle i
          (fun a => wpi H (k a) Φ)
          (fun a => iprop(|==> wpi H (k a) (fun _ => iprop(False)))))
  have hUnfold : wpi H t Φ ≡ BUpd.bupd P := by
    simpa [wpiF, P] using
      (equiv_iff.mpr <| wpi_unfold_emp_mask (H := H) (t := t) (Φ := Φ))
  have hBupd :
      BUpd.bupd (wpi H t Φ) ≡ BUpd.bupd (BUpd.bupd P) := by
    letI : OFE.NonExpansive (BUpd.bupd (PROP := PROP)) := BIUpdate.bupd_ne
    exact OFE.NonExpansive.eqv (f := BUpd.bupd (PROP := PROP)) hUnfold
  have hIdem : BUpd.bupd (BUpd.bupd P) ≡ BUpd.bupd P := by
    exact equiv_iff.mpr <| bupd_idem (P := P)
  exact equiv_iff.mp <| hBupd.trans <| hIdem.trans hUnfold.symm

theorem wpi_tau_emp_mask {R} (Φ : R → PROP) (t : ITree E R) :
    wpi H t Φ ⊣⊢ wpi H (ITree.tau t) Φ := by
  calc
    wpi H t Φ ⊣⊢ BUpd.bupd (wpi H t Φ) := (wpi_update_emp_mask (H := H) (t := t) (Φ := Φ)).symm
    _ ⊣⊢ wpiF H (wpi H) (ITree.tau t) Φ := by
      simp [wpiF]
    _ ⊣⊢ wpi H (ITree.tau t) Φ := (wpi_unfold_emp_mask (H := H) (t := ITree.tau t) (Φ := Φ)).symm

omit [BIUpdate PROP] in
theorem uncurry_G_ne {R} (G : ITree E R → (R → PROP) → PROP) :
    (∀ t, OFE.NonExpansive (G t)) →
    OFE.NonExpansive (fun p : LeibnizO (ITree E R) × (R → PROP) => G p.1.car p.2) := by
  intro Hne
  constructor
  intro n ⟨t₁, Φ₁⟩ ⟨t₂, Φ₂⟩ ⟨Ht, HΦ⟩
  cases t₁ with
  | mk t₁ =>
    cases t₂ with
    | mk t₂ =>
      have hEq : ({ car := t₁ } : LeibnizO (ITree E R)) = { car := t₂ } :=
        OFE.Leibniz.eq_of_eqv (OFE.Discrete.discrete Ht)
      cases hEq
      simpa using (Hne t₁).ne HΦ

theorem wpi_ind_emp_mask {R} (G : ITree E R → (R → PROP) → PROP) :
    (∀ t, OFE.NonExpansive (G t)) →
    ⊢ □ (∀ t Φ, wpiF H (fun t' Ψ => iprop(G t' Ψ ∧ wpi H t' Ψ)) t Φ -∗ G t Φ) -∗
      ∀ t Φ, wpi H t Φ -∗ G t Φ := by
  intro Hne
  let G' : LeibnizO (ITree E R) × (R → PROP) → PROP := fun ⟨t, Φ⟩ => G t.car Φ
  haveI : OFE.NonExpansive G' := uncurry_G_ne (G := G) Hne
  iintro #HPre %t %Φ
  ihave HPre' :
      □ (∀ y, wpiF' H (fun x => iprop(G' x ∧ bi_least_fixpoint (wpiF' H) x)) y -∗ G' y) $$ []
  ·
    iintro !> %y
    cases y with
    | mk t' Ψ =>
      simp [G', wpiF', wpi] at ⊢
      iintro Hx
      iapply HPre $$ Hx
  ihave HInd := (least_fixpoint_ind (F := wpiF' H) (Φ := G'))
  ispecialize HInd $$ HPre'
  ispecialize HInd $$ %((⟨t⟩, Φ))
  simp [wpi, G'] at ⊢
  iexact HInd

theorem wpi_iter_emp_mask {R} (G : ITree E R → (R → PROP) → PROP) :
    (∀ t, OFE.NonExpansive (G t)) →
    ⊢ □ (∀ t Φ, wpiF H G t Φ -∗ G t Φ) -∗
      ∀ t Φ, wpi H t Φ -∗ G t Φ := by
  intro Hne
  let G' : LeibnizO (ITree E R) × (R → PROP) → PROP := fun ⟨t, Φ⟩ => G t.car Φ
  haveI : OFE.NonExpansive G' := uncurry_G_ne (G := G) Hne
  iintro #HPre %t %Φ
  ihave HPre' : □ (∀ y, wpiF' H G' y -∗ G' y) $$ []
  ·
    iintro !> %y
    cases y with
    | mk t' Ψ =>
      simp [G', wpiF'] at ⊢
      iintro Hx
      iapply HPre $$ Hx
  ihave HIter := (least_fixpoint_iter (F := wpiF' H) (Φ := G'))
  ispecialize HIter $$ HPre'
  ispecialize HIter $$ %((⟨t⟩, Φ))
  simp [wpi, G'] at ⊢
  iexact HIter

theorem wpi_iter_emp_mask' {R} (G : ITree E R → (R → PROP) → PROP) :
    (∀ t, OFE.NonExpansive (G t)) →
    ⊢ □ (∀ Φ r, (|==> Φ r) -∗ G (ITree.ret r) Φ) -∗
      □ (∀ Φ t, (|==> G t Φ) -∗ G (ITree.tau t) Φ) -∗
      □ (∀ Φ (i : E.I) k,
        (|==> H.ihandle i
          (fun a => G (k a) Φ)
          (fun a => iprop(|==> G (k a) (fun _ => iprop(False))))) -∗
        G (ITree.vis i k) Φ) -∗
      ∀ t Φ, wpi H t Φ -∗ G t Φ := by
  iintro %Hne #HRet #HTau #HVis
  iapply (wpi_iter_emp_mask (H := H) (G := G) Hne)
  iintro !> %t %Φ
  cases h : t.unfold
  case ret r =>
    have ht : t = ITree.ret r := by
      calc
        t = ITree.fold (t.unfold) := by
          simpa using (ITree.unfold_fold t).symm
        _ = ITree.fold (ITreeF.ret r) := by rw [h]
        _ = ITree.ret r := rfl
    cases ht
    simp [wpiF]
    iintro Hwp
    iapply HRet $$ Hwp
  case tau t' =>
    have ht : t = ITree.tau t' := by
      calc
        t = ITree.fold (t.unfold) := by
          simpa using (ITree.unfold_fold t).symm
        _ = ITree.fold (ITreeF.tau t') := by rw [h]
        _ = ITree.tau t' := rfl
    cases ht
    simp [wpiF]
    iintro Hwp
    iapply HTau $$ Hwp
  case vis i k =>
    have ht : t = ITree.vis i k := by
      calc
        t = ITree.fold (t.unfold) := by
          simpa using (ITree.unfold_fold t).symm
        _ = ITree.fold (ITreeF.vis i k) := by rw [h]
        _ = ITree.vis i k := rfl
    cases ht
    simp [wpiF]
    iintro Hwp
    iapply HVis $$ Hwp

end wp_itree
