import Carte.Core.Handler
import Carte.Core.Wpi
import Iris.ProofMode
import Iris.BI.Lib.Fixpoint
import Iris.BI.BigOp.BigSepList
import ITree.Definition
import ITree.Exec

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

section handler_adequacy

open ITree.Exec

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

/-- Logical adequacy interface for executable handlers with thread-pool side effects. -/
class EHandlerAdequate {E GE : Effect.{u} } {R σ : Type _}
    (H : IHandler (PROP := PROP) E) (EH : EHandler E GE R σ) where
  ehandler_inv : σ → List (((ITree GE R → PROP) → PROP)) → PROP
  ehandler_adequate :
    ∀ (G : ITree GE R → PROP) (e : E.I) (s : σ)
      (Ms : List (((ITree GE R → PROP) → PROP)))
      (C : ITree GE R → σ → Prop) (k : E.O e → ITree GE R),
      EH.handle e s k C →
      ⊢ H.ihandle e (fun a => G (k a)) (fun a => iprop(|={⊤,∅}=> G (k a))) -∗
          ehandler_inv s Ms -∗
          |={∅}=> ∃ t' s' M' Ms' Msn,
            ⌜C t' s'⌝ ∗
            ⌜(M' :: Ms').Perm (Msn ++ Ms)⌝ ∗
            ([∗list] M ∈ Msn, M G) ∗
            ehandler_inv s' Ms' ∗
            bi_close Eq (fun t'' => iprop(∀ P, M' P ={∅}=∗ P t'')) t'
  ehandler_inv_proper :
    ∀ {s s' Ms Ms'}, s = s' → Ms = Ms' →
      ehandler_inv s Ms ⊢ ehandler_inv s' Ms'

/-- Logical adequacy interface for simple executable handlers. -/
class SEHandlerAdequate {E : Effect.{u} } {σ : Type _}
    (H : IHandler (PROP := PROP) E) (EH : SEHandler E σ) where
  sehandler_inv : σ → PROP
  sehandler_adequate :
    ∀ (e : E.I) (s : σ) (C : E.O e → σ → Prop) (Φ1 Φ2 : E.O e → PROP),
      EH.handle e s C →
      ⊢ H.ihandle e Φ1 Φ2 -∗
          sehandler_inv s -∗
          |={∅}=> ∃ a s', ⌜C a s'⌝ ∗ sehandler_inv s' ∗ Φ1 a

end handler_adequacy

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
      (∀ Ms, lfp_tp F Ms.car -∗ Φ Ms) := by
  iintro #Hwand %Ms Hlfp
  iapply least_fixpoint_ind (lfp_tpF (PROP := PROP) F)
  · iintro !> %y Hlfp; iapply Hwand;
    iapply lfp_tpF_mono F $$ [] Hlfp
    iintro !> %Ms Hpre; iapply and_congr_r $$ Hpre
    simp [lfp_tp]
  · simp [lfp_tp]; iexact Hlfp

-- Helper function for [lfp_*_perm_*]
theorem perm_pick_erase {β : Type _} {Ms1 Ms2 : List β} {i : Nat} {M : β}
    (hperm : Ms1.Perm Ms2) (Hi : Ms2[i]? = some M) :
    ∃ j, Ms1[j]? = some M ∧ (Ms1.eraseIdx j).Perm (Ms2.eraseIdx i) := by
  induction hperm generalizing i M with
  | nil => simp at Hi
  | cons x hperm ih => cases i with
    | zero => simp at Hi; subst M; refine ⟨0, ?_, ?_⟩; simp; simpa
    | succ i =>
      simp at Hi; rcases ih Hi with ⟨j, Hj, Hperm⟩
      refine ⟨j + 1, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Hj
      · simpa [List.eraseIdx_cons_succ] using List.Perm.cons x Hperm
  | swap x y l => cases i with
    | zero => simp at Hi; subst M; refine ⟨1, ?_, ?_⟩; simp; simp
    | succ i => cases i with
      | zero => simp at Hi; subst M; refine ⟨0, ?_, ?_⟩; simp; simp
      | succ i =>
        simp at Hi; refine ⟨i + 2, ?_, ?_⟩
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hi
        · simpa [List.eraseIdx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using List.Perm.swap x y (l.eraseIdx i)
  | trans h₁ h₂ ih₁ ih₂ =>
      rcases ih₂ Hi with ⟨j₂, Hj₂, Hperm₂⟩
      rcases ih₁ Hj₂ with ⟨j₁, Hj₁, Hperm₁⟩
      exact ⟨j₁, Hj₁, List.Perm.trans Hperm₁ Hperm₂⟩

theorem lfp_tpF_perm (Ms1 Ms2 : List ((α → PROP) → PROP))
    (wp1 wp2 : LeibnizO (List ((α → PROP) → PROP)) → PROP)
    (h : Ms1.Perm Ms2) :
    lfp_tpF F wp1 ⟨Ms1⟩ ⊢
    (∀ (Ns1 Ns2 : LeibnizO (List ((α → PROP) → PROP))),
      ⌜Ns1.car.Perm Ns2.car⌝ -∗ wp1 Ns1 -∗ wp2 Ns2) -∗
    lfp_tpF F wp2 ⟨Ms2⟩ := by
  iintro Htp Hwp; unfold lfp_tpF; iintro %i %M %Hi
  rcases perm_pick_erase h Hi with ⟨j, Hj, Herase⟩
  ispecialize Htp $$ %j %M %Hj
  iapply bi_mono0_mono $$ Htp
  iintro %x Hstep; icases Hstep with ⟨%G, HFx, Hcont⟩
  iexists G; isplitl [HFx]; iexact HFx
  iintro %Ms' HM'; iapply Hwp $$ %⟨Ms' ++ Ms1.eraseIdx j⟩ %⟨Ms' ++ Ms2.eraseIdx i⟩
  · ipure_intro; simp; exact (List.perm_append_left_iff Ms').2 Herase
  · iapply Hcont $$ HM'

theorem lfp_tpF_perm_close (Ms1 Ms2 : List ((α → PROP) → PROP))
    (wp : LeibnizO (List ((α → PROP) → PROP)) → PROP)
    (h : Ms1.Perm Ms2) :
    lfp_tpF F wp ⟨Ms1⟩ ⊢
    lfp_tpF F (bi_close (λ a b => a.car.Perm b.car) wp) ⟨Ms2⟩ := by
  iintro Htp; iapply lfp_tpF_perm $$ Htp
  · exact h
  · iintro %Ns1 %Ns2 %Hperm Hwp; simp only [bi_close]
    iexists Ns1; isplitr
    · ipure_intro; exact Hperm.symm
    · iexact Hwp

theorem lfp_tp_perm (Ms1 Ms2 : List ((α → PROP) → PROP)) (h : Ms1.Perm Ms2) :
    ⊢ lfp_tp F Ms1 -∗ lfp_tp F Ms2 := by
  letI : NonExpansive λ (Ms : LeibnizO (List ((α → PROP) → PROP))) =>
    iprop(∀ Ms2, ⌜Ms.car.Perm Ms2⌝ -∗ lfp_tp F Ms2) := ⟨
      λ n lst1 lst2 Hlst => by
        refine forall_ne (λ lst => ?_)
        cases Hlst; rfl
    ⟩
  iintro Htp; irevert %Ms2 %h
  iapply lfp_tp_ind F λ Ms => iprop(∀ Ms2, ⌜Ms.car.Perm Ms2⌝ -∗ lfp_tp F Ms2) $$ [] Htp
  iintro !> %Ms1 Htp %Ms2 %Hperm; iapply lfp_tp_unfold
  iapply lfp_tpF_perm F Ms1.car _ _ _ Hperm $$ Htp
  iintro %Ns1 %Ns2 %Hperm Hw; icases Hw with ⟨H, -⟩
  iapply H; ipure_intro; exact Hperm

theorem lfp_tp_app (Ms1 Ms2 : List ((α → PROP) → PROP)) :
    ⊢ lfp_tp F Ms1 -∗ lfp_tp F Ms2 -∗ lfp_tp F (Ms1 ++ Ms2) := by
  letI : NonExpansive λ (Ms : LeibnizO (List ((α → PROP) → PROP))) =>
    iprop(∀ Ms2, lfp_tp F Ms2 -∗ lfp_tp F (Ms.car ++ Ms2)) := by
      sorry
  have Hwrap :
      ⊢ BI.forall (fun Ms1 : LeibnizO (List ((α → PROP) → PROP)) =>
            iprop(lfp_tp F Ms1.car -∗ BI.forall (fun Ms2 =>
              iprop(lfp_tp F Ms2 -∗ lfp_tp F (Ms1.car ++ Ms2))))) -∗
          BI.forall (fun Ms1 : List ((α → PROP) → PROP) =>
            iprop(lfp_tp F Ms1 -∗ BI.forall (fun Ms2 =>
              iprop(lfp_tp F Ms2 -∗ lfp_tp F (Ms1 ++ Ms2))))) := by
    iintro H %Ms1 Hx1 %Ms2 Hx2
    iapply H $$ %⟨Ms1⟩ Hx1 %Ms2 Hx2
  have Hwrap2 :
      ⊢ BI.forall (fun Ms2 : LeibnizO (List ((α → PROP) → PROP)) =>
            iprop(lfp_tp F Ms2.car -∗ BI.forall (fun Ms1 =>
              iprop(lfp_tpF F (fun x =>
                iprop((∀ Ms, lfp_tp F Ms -∗ lfp_tp F (x.car ++ Ms)) ∧ lfp_tp F x.car)) Ms1 -∗
                  lfp_tp F (Ms1.car ++ Ms2.car))))) -∗
          BI.forall (fun Ms2 : List ((α → PROP) → PROP) =>
            iprop(lfp_tp F Ms2 -∗ BI.forall (fun Ms1 =>
              iprop(lfp_tpF F (fun x =>
                iprop((∀ Ms, lfp_tp F Ms -∗ lfp_tp F (x.car ++ Ms)) ∧ lfp_tp F x.car)) Ms1 -∗
                  lfp_tp F (Ms1.car ++ Ms2))))) := by
    iintro H %Ms2 Hx2 %Ms1 Hx1
    iapply H $$ %⟨Ms2⟩ Hx2 %Ms1 Hx1
  iintro Hx1 Hx2; irevert %Ms1 Hx1 %Ms2 Hx2
  iapply Hwrap
  iapply lfp_tp_ind F λ Ms => iprop(∀ Ms2, lfp_tp F Ms2 -∗ lfp_tp F (Ms.car ++ Ms2))
  iintro !> %Ms1 Hx1 %Ms2 Hx2; irevert %Ms1 Hx1; irevert %Ms2 Hx2
  letI : NonExpansive λ (Ms : LeibnizO (List ((α → PROP) → PROP))) =>
      iprop(∀ Ms1, lfp_tpF F (λ x =>
        iprop((∀ Ms, lfp_tp F Ms -∗ lfp_tp F (x.car ++ Ms)) ∧ lfp_tp F x.car)) Ms1 -∗
          lfp_tp F (Ms1.car ++ Ms.car)) := ⟨
        λ n lst1 lst2 Hlst => by
          refine forall_ne (λ Ms1 => ?_)
          cases Hlst
          rfl
      ⟩
  iapply Hwrap2
  iapply lfp_tp_ind F λ Ms => iprop(∀ Ms1, lfp_tpF F (λ x =>
    iprop((∀ Ms, lfp_tp F Ms -∗ lfp_tp F (x.car ++ Ms)) ∧ lfp_tp F x.car)) Ms1 -∗
      lfp_tp F (Ms1.car ++ Ms.car))
  iintro !> %Ms2 Hx2 %Ms1 Hx1; iapply lfp_tp_unfold; unfold lfp_tpF at ⊢; simp
  iintro %i %M %Hi
  sorry

theorem lfp_tp_cons (M : (α → PROP) → PROP) (Ms : List ((α → PROP) → PROP)) :
    ⊢ lfp_tp F [M] -∗ lfp_tp F Ms -∗ lfp_tp F (M :: Ms) := by
  sorry

theorem lfp_tp_singleton_mod_elim (M : (α → PROP) → PROP) :
    ⊢ M (λ x => lfp_tp F [λ P => P x]) -∗ lfp_tp F [M] := by
  sorry

end lfp_tp_lemmas

theorem lfp_tp_intro_of {PROP : Type _} [BI PROP] [BIAffine PROP]
    {α : Type _} [OFE α] [OFE.Discrete α] [OFE.Leibniz α]
    (G : (α → PROP) → (α → PROP)) [HG : BIMonoPred G] (x : α) :
    ⊢ bi_least_fixpoint G x -∗ lfp_tp G [λ P => P x] := by
  letI : NonExpansive (fun (x : α) => lfp_tp G [λ P => P x] : α → PROP) := ⟨
    fun {n x1 x2} Hx => by
      have Heq : x1 = x2 := OFE.eq_of_eqv (OFE.Discrete.discrete Hx)
      subst Heq; rfl
  ⟩
  irevert %x; iapply least_fixpoint_iter
  · iintro !> %x HF
    iapply (lfp_tp_unfold G [λ P => P x]).mpr
    simp only [lfp_tpF]
    iintro %i %M %Hi
    cases i with
    | zero =>
      simp at Hi; subst Hi
      simp only [bi_mono0]
      iexists (G (fun y => lfp_tp G [λ P => P y]))
      isplitl [HF]
      · iexact HF
      · iintro %y HGy
        iexists (fun y => lfp_tp G [λ P => P y])
        isplitl [HGy]
        · iexact HGy
        · iintro %Ms' HMs'
          simp only [List.eraseIdx, List.append_nil]
          sorry
    | succ n => simp at Hi

/-! ## Constant-Φ weakest precondition -/

/-- The constant-Φ weakest precondition functional.
    Unlike `wpiF`, the postcondition Φ is fixed rather than varying. -/
def wpi_constF {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
    (H : IHandler (PROP := PROP) E) (Φ : R → PROP)
    (wpi : LeibnizO (ITree E R) → PROP) :
    LeibnizO (ITree E R) → PROP :=
  λ t => iprop(
    |={∅}=> match t.car.unfold with
    | ITreeF.ret r => Φ r
    | ITreeF.tau t' => wpi ⟨t'⟩
    | ITreeF.vis i k => H.ihandle i
        (λ a => wpi ⟨k a⟩)
        (λ a => iprop(|={⊤,∅}=> wpi ⟨k a⟩))
  )

section wp_itree_const

variable {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]

instance wpi_constF_ne (H : IHandler (PROP := PROP) E) (Φ : R → PROP) :
    NonExpansive (wpi_constF H Φ) where
  ne {_ wp1 wp2} Hwp := by
    intro t
    cases h : t.car.unfold <;> simp [wpi_constF, h]
    case tau t' => exact BIFUpdate.ne.ne <| Hwp ⟨t'⟩
    case vis i k =>
      apply BIFUpdate.ne.ne
      apply OFE.NonExpansive₂.ne (f := H.ihandle i)
      · intro a; apply Hwp ⟨k a⟩
      · intro a; apply BIFUpdate.ne.ne <| Hwp ⟨k a⟩

theorem wpi_constF_mono (H : IHandler (PROP := PROP) E) (Φ : R → PROP)
    (wp1 wp2 : LeibnizO (ITree E R) → PROP) :
    ⊢ □ (∀ t, wp1 t -∗ wp2 t) -∗
      ∀ t, wpi_constF H Φ wp1 t -∗ wpi_constF H Φ wp2 t := by
  iintro #Hwand %t Hwp; unfold wpi_constF
  cases t.car.unfold <;> simp
  case ret => iexact Hwp
  case tau t' => imod Hwp; imodintro; iapply Hwand $$ Hwp
  case vis i k =>
    imod Hwp; imodintro; iapply H.ihandle_mono
    · iintro %a Hk; iapply Hwand $$ Hk
    · iintro !> %a Hk; imod Hk; imodintro; iapply Hwand $$ Hk
    · iexact Hwp

instance wp_itree_const_mono (H : IHandler (PROP := PROP) E) (Φ : R → PROP) :
    BIMonoPred (wpi_constF H Φ) where
  mono_pred := by
    iintro %wp1 %wp2 %Hne1 %Hne2 #Hwand %t Hwp
    iapply wpi_constF_mono H Φ wp1 wp2 $$ [] Hwp
    iexact Hwand
  mono_pred_ne.ne n t1 t2 Hdist := by
    cases Hdist; rfl

/-- The constant-Φ weakest precondition, as the least fixpoint of `wpi_constF`. -/
def wpi_const (H : IHandler (PROP := PROP) E) (Φ : R → PROP) : ITree E R → PROP :=
  λ t => bi_least_fixpoint (wpi_constF H Φ) ⟨t⟩

theorem wpi_const_iter (H : IHandler (PROP := PROP) E) (Φ : R → PROP)
    (P : LeibnizO (ITree E R) → PROP) [NonExpansive P] :
    ⊢ □ (∀ y, wpi_constF H Φ P y -∗ P y) -∗
      ∀ t, bi_least_fixpoint (wpi_constF H Φ) t -∗ P t :=
  @least_fixpoint_iter _ _ _ _ (wpi_constF H Φ) P _

end wp_itree_const

/-! ## Thread-pool weakest precondition -/

/-- The thread-pool weakest precondition, built from `wpi_constF` and `lfp_tp`. -/
def wpi_tp {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
    (H : IHandler (PROP := PROP) E)
    (Ms : List (((LeibnizO (ITree E R) → PROP) → PROP)))
    (Φ : R → PROP) : PROP :=
  lfp_tp (wpi_constF H Φ) Ms

section wpi_tp_section

variable {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]

theorem wpi_tp_intro (t : ITree E R) (H : IHandler (PROP := PROP) E) (Φ : R → PROP) :
    (WPi t @> H {{ Φ }}) ⊢ wpi_tp H [λ P => P ⟨t⟩] Φ := by
  sorry

theorem wpi_tp_perm (H : IHandler (PROP := PROP) E) (Φ : R → PROP)
    (Ms1 Ms2 : List (((LeibnizO (ITree E R) → PROP) → PROP)))
    (h : Ms1.Perm Ms2) :
    wpi_tp H Ms1 Φ ⊣⊢ wpi_tp H Ms2 Φ := by
  simp only [wpi_tp]
  isplit <;> iintro Htp
  · iapply lfp_tp_perm (wpi_constF H Φ) Ms1 Ms2 h $$ Htp
  · iapply lfp_tp_perm (wpi_constF H Φ) Ms2 Ms1 h.symm $$ Htp

end wpi_tp_section

/-! ## Adequacy -/

section wpi_adequate

open ITree.Exec

variable {E : Effect.{u} } {R : Type u} {σ : Type _}
  {PROP : Type _} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]

theorem wpi_adequate_ind (Φ : R → PROP) (H : IHandler (PROP := PROP) E)
    (EH : EHandler E E R σ) [A : EHandlerAdequate (PROP := PROP) H EH]
    (t : ITree E R) (s : σ)
    (Ms : List (((LeibnizO (ITree E R) → PROP) → PROP)))
    (Mss : List (((ITree E R → PROP) → PROP)))
    (M : (LeibnizO (ITree E R) → PROP) → PROP)
    (C : ITree E R → σ → Prop)
    (Hexec : exec EH t s C)
    (HMs : Ms.Perm (M :: Mss.map (λ M' P => M' (λ t => P ⟨t⟩)))) :
    ⊢ wpi_tp H Ms Φ -∗
      A.ehandler_inv s Mss -∗
      (∀ P, M P ={∅}=∗ P ⟨t⟩) -∗
      |={∅}=> ∃ t' s' Ms' M',
        ⌜C t' s'⌝ ∗
        A.ehandler_inv s' Ms' ∗
        bi_close Eq (λ t'' => iprop(∀ P, M' P ={∅}=∗ P t'')) ⟨t'⟩ ∗
        wpi_tp H (M' :: Ms'.map (λ M'' P => M'' (λ t => P ⟨t⟩))) Φ := by
  sorry

theorem wpi_adequate (Φ : R → PROP) (H : IHandler (PROP := PROP) E)
    (EH : EHandler E E R σ) [A : EHandlerAdequate (PROP := PROP) H EH]
    (t : ITree E R) (s : σ)
    (C : ITree E R → σ → Prop) (m : CoPset)
    (Hexec : exec EH t s C) :
    ⊢ iprop(|={m,∅}=> wpi H t (λ v => iprop(|={∅,m}=> Φ v))) -∗
      A.ehandler_inv s [] -∗
      |={m, ∅}=> ∃ t' s' Ms' M',
      ⌜C t' s'⌝ ∗
      A.ehandler_inv s' Ms' ∗
      bi_close Eq (λ t'' => iprop(∀ P, M' P ={∅}=∗ P t'')) ⟨t'⟩ ∗
      wpi_tp H (M' :: Ms'.map (λ M'' P => M'' (λ t => P ⟨t⟩))) (λ v => iprop(|={∅,m}=> Φ v)) := by
  sorry

end wpi_adequate

end Carte.Core
