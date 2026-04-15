import Iris.ProofMode
import Iris.BI.Lib.Fixpoint
import Iris.BI.BigOp.BigSepList
import ITree.Definition

namespace Carte.Core

open Iris BI ITree Std OFE

def bi_close {PROP : Type _} [BI PROP] {α : Type _} (R : α → α → Prop) (P : α → PROP) : α → PROP :=
  λ a => iprop(∃ a', ⌜R a a'⌝ ∗ P a')

section bi_close

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {α : Type} (R : α → α → Prop)

theorem bi_close_mono (P1 P2 : α → PROP) (a : α) :
    bi_close R P1 a ⊢ (∀ y, P1 y -∗ P2 y) -∗ bi_close R P2 a := by
  iintro Hclose Hwand; simp [bi_close]
  icases Hclose with ⟨%a', %HR, HP1⟩
  iexists a'; isplitr
  · ipure_intro; exact HR
  · iapply Hwand $$ HP1

theorem bi_close_intro (P : α → PROP) (a : α) [Href : Reflexive R] :
    P a ⊢ bi_close R P a := by
  iintro HP; simp [bi_close]
  iexists a; isplitr
  · ipure_intro; exact Href.refl
  · iexact HP

theorem bi_close_respect (P : α → PROP) [Hsym : Symm R] [Htran : Trans R R R] :
    ∀ {x y : α}, R x y → bi_close R P x ⊣⊢ bi_close R P y := by
  intro x y Hxy
  isplit <;> (
    iintro Hclose; simp [bi_close]; icases Hclose with ⟨%a', %Hra, HP⟩;
    iexists a'; isplitr; ipure_intro
  )
  · exact Htran.trans (Hsym.symm x y Hxy) Hra
  · iexact HP
  · exact Htran.trans Hxy Hra
  · iexact HP

end bi_close

/-- [bi_mono0] : linear monotone closure of a predicate transformer. -/
def bi_mono0 {PROP : Type _} [BI PROP] {α : Type _} (P : (α → PROP) → PROP) : (α → PROP) → PROP :=
  λ Q => iprop(∃ Q' : α → PROP, P Q' ∗ ∀ x, Q' x -∗ Q x)

section bi_mono0

variable {PROP : Type _} [BI PROP] {α : Type _}

theorem bi_mono0_intro0 (P : (α → PROP) → PROP) (Q : α → PROP) :
    P Q ⊢ bi_mono0 P Q := by
  iintro HP; simp only [bi_mono0]
  iexists Q; isplitl [HP]
  · iexact HP
  · iintro %x HQ; iexact HQ

theorem bi_mono0_mono (P : (α → PROP) → PROP) (Q1 Q2 : α → PROP) :
    bi_mono0 P Q1 ⊢ (∀ x, Q1 x -∗ Q2 x) -∗ bi_mono0 P Q2 := by
  iintro Hm HQ; simp only [bi_mono0]
  icases Hm with ⟨%Q', HP, HQ1⟩
  iexists Q'; isplitl [HP]
  · iexact HP
  · iintro %x HQ'; iapply HQ; iapply HQ1; iapply HQ'

theorem bi_mono0_mono_l (P1 P2 : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 P1 Q ⊢ (∀ Q, P1 Q -∗ P2 Q) -∗ bi_mono0 P2 Q := by
  iintro Hm HP; simp only [bi_mono0]
  icases Hm with ⟨%Q', HP1, HQ1⟩
  iexists Q'; isplitl [HP HP1]
  · iapply HP $$ %Q' HP1
  · iexact HQ1

theorem bi_mono0_elim (P : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 P Q ⊢ (∀ Q Q', (∀ x, Q' x -∗ Q x) -∗ P Q' -∗ P Q) -∗ P Q := by
  iintro Hm HP; simp only [bi_mono0]
  icases Hm with ⟨%Q', HPQ', HQ1⟩
  iapply HP $$ %Q %Q' HQ1 HPQ'

theorem bi_mono0_dup (P : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 (bi_mono0 P) Q ⊢ bi_mono0 P Q := by
  iintro H; simp only [bi_mono0]
  icases H with ⟨%Q', Houter, HQw⟩
  icases Houter with ⟨%Q'', HP, HQw'⟩
  iexists Q''; isplitl [HP]
  · iexact HP
  · iintro %x HQ''; iapply HQw; iapply HQw' $$ HQ''

theorem bi_mono0_intro (P : (α → PROP) → PROP) (Q Q' : α → PROP) :
    P Q' ⊢ (∀ x, Q' x -∗ Q x) -∗ bi_mono0 P Q := by
  iintro HP HQ; simp only [bi_mono0]
  iexists Q'; isplitl [HP]
  · iexact HP
  · iexact HQ

end bi_mono0

/-- The functional whose least fixed point is `lfp_tp`. -/
def lfp_tpF {PROP : Type _} [BI PROP] {α : Type _}
    (F : (α → PROP) → (α → PROP))
    (rec_tp : LeibnizO (List ((α → PROP) → PROP)) → PROP) :
    LeibnizO (List ((α → PROP) → PROP)) → PROP :=
  λ Ms => iprop(
    ∀ (i : Nat) (M : (α → PROP) → PROP), ⌜Ms.car[i]? = some M⌝ -∗
      bi_mono0 M λ x => iprop(
        ∃ G, F G x ∗ ∀ Ms', ([∗list] M' ∈ Ms', M' G) -∗ rec_tp ⟨Ms' ++ Ms.car.eraseIdx i⟩
      )
  )

section lfp_tp

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {α : Type _}
  (F : (α → PROP) → (α → PROP))

instance lfp_tpF_ne : NonExpansive (lfp_tpF F) where
  ne {_ _ _} Hfg := by
    intro Ms; unfold lfp_tpF bi_mono0
    apply forall_ne; intro i; apply forall_ne; intro _
    apply wand_ne.ne; rfl; apply exists_ne; intro _
    apply sep_ne.ne; rfl; apply forall_ne; intro _
    apply wand_ne.ne; rfl; apply exists_ne; intro _
    apply sep_ne.ne; rfl; apply forall_ne; intro Ms'
    apply wand_ne.ne; rfl; exact Hfg ⟨Ms' ++ Ms.car.eraseIdx i⟩

theorem lfp_tpF_mono (tp1 tp2 : LeibnizO (List ((α → PROP) → PROP)) → PROP) :
    ⊢ □ (∀ Ms, tp1 Ms -∗ tp2 Ms) -∗
      ∀ Ms, lfp_tpF F tp1 Ms -∗ lfp_tpF F tp2 Ms := by
  iintro #Hwand %Ms Htp; unfold lfp_tpF
  iintro %i %M %Hi; ispecialize Htp $$ %i %M %Hi
  iapply bi_mono0_mono $$ Htp
  iintro %x ⟨%G, HF, HMS⟩; iexists G; isplitl [HF]
  · iexact HF
  · iintro %Ms HM'; iapply Hwand; iapply HMS $$ HM'

instance : BIMonoPred (lfp_tpF (PROP := PROP) F) where
  mono_pred := by
    iintro %Φ %Ψ %HneΦ %HneΨ #Hwand %Ms HΦ
    iapply lfp_tpF_mono F Φ Ψ $$ [] [HΦ]
    · iexact Hwand
    · iexact HΦ
  mono_pred_ne.ne n Φ Φ' Hdist := by
    cases Hdist; rfl

end lfp_tp

/-- The `lfp_tp` least-fixed-point predicate. -/
def lfp_tp {PROP : Type _} [BI PROP] {α : Type _}
    (F : (α → PROP) → (α → PROP))
    (Ms : List ((α → PROP) → PROP)) : PROP :=
  bi_least_fixpoint (lfp_tpF F) ⟨Ms⟩

section lfp_tp_lemmas

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {α : Type _}
  (F : (α → PROP) → (α → PROP))

theorem lfp_tp_unfold (Ms : List ((α → PROP) → PROP)) :
    lfp_tp F Ms ⊣⊢ lfp_tpF F (λ Ms => lfp_tp F Ms.car) ⟨Ms⟩ :=
  equiv_iff.mp <| least_fixpoint_unfold (lfp_tpF F)

theorem lfp_tp_nil : ⊢ (lfp_tp F [] : PROP) := by
  iapply (lfp_tp_unfold F []).mpr
  simp only [lfp_tpF]
  iintro %i %M %Hi; simp at Hi

theorem lfp_tp_ind (Φ : LeibnizO (List ((α → PROP) → PROP)) → PROP)
    [NonExpansive Φ] :
    ⊢ □ (∀ y, lfp_tpF F (λ x => iprop(Φ x ∧ lfp_tp F x.car)) y -∗ Φ y) -∗
      ∀ Ms, lfp_tp F Ms.car -∗ Φ Ms := by
  iintro Hwand %Ms Hlfp
  sorry
  -- iapply least_fixpoint_ind (lfp_tpF F)

theorem lfp_tpF_perm (Ms1 Ms2 : List ((α → PROP) → PROP))
    (wp1 wp2 : LeibnizO (List ((α → PROP) → PROP)) → PROP)
    (h : Ms1.Perm Ms2) :
    ⊢ lfp_tpF F wp1 ⟨Ms1⟩ -∗
      (∀ (Ns1 Ns2 : LeibnizO (List ((α → PROP) → PROP))),
        ⌜Ns1.car.Perm Ns2.car⌝ -∗ wp1 Ns1 -∗ wp2 Ns2) -∗
      lfp_tpF F wp2 ⟨Ms2⟩ := by
  sorry

theorem lfp_tpF_perm_close (Ms1 Ms2 : List ((α → PROP) → PROP))
    (wp : LeibnizO (List ((α → PROP) → PROP)) → PROP)
    (h : Ms1.Perm Ms2) :
    ⊢ lfp_tpF F wp ⟨Ms1⟩ -∗
      lfp_tpF F (bi_close (fun a b => a.car.Perm b.car) wp) ⟨Ms2⟩ := by
  sorry

theorem lfp_tp_perm (Ms1 Ms2 : List ((α → PROP) → PROP)) (h : Ms1.Perm Ms2) :
    ⊢ lfp_tp F Ms1 -∗ lfp_tp F Ms2 := by
  sorry

theorem lfp_tp_app (Ms1 Ms2 : List ((α → PROP) → PROP)) :
    ⊢ lfp_tp F Ms1 -∗ lfp_tp F Ms2 -∗ lfp_tp F (Ms1 ++ Ms2) := by
  sorry

theorem lfp_tp_cons (M : (α → PROP) → PROP) (Ms : List ((α → PROP) → PROP)) :
    ⊢ lfp_tp F [M] -∗ lfp_tp F Ms -∗ lfp_tp F (M :: Ms) := by
  sorry

theorem lfp_tp_singleton_mod_elim (M : (α → PROP) → PROP) :
    ⊢ M (λ x => lfp_tp F [λ P => P x]) -∗ lfp_tp F [M] := by
  sorry

end lfp_tp_lemmas

theorem lfp_tp_intro_of {PROP : Type _} [BI PROP] {α : Type _} [OFE α]
    (G : (α → PROP) → (α → PROP)) [BIMonoPred G] (x : α) :
    ⊢ bi_least_fixpoint G x -∗ lfp_tp G [λ P => P x] := by
  sorry


end Carte.Core
