import Carte.Core.Handler
import Carte.Core.WpiMask
import ITree

namespace Carte.Event

open Iris BI ITree Effects

section exec

open ITree.Exec

abbrev haltEH := ITree.Effects.haltEH

-- The Coq `seHandlerAdequate` layer does not currently exist in this Lean port.

theorem exec_assume {E : Effect} {σ : Type _}
    (P : Prop) [Decidable P] (EH : EHandler E E { _x // P } σ)
    [haltE -< E] [InEH haltEH.toEHandler EH] (s : σ) (C : ITree E { _x // P } → σ → Prop) :
    P →
    (∀ HP : { _x // P }, C (ITree.ret HP) s) →
    exec EH (HaltE.assume P) s C := by
  intro hP hC
  unfold HaltE.assume
  simp [hP]
  apply exec.stop
  exact hC ⟨⟨⟩, hP⟩

end exec

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def haltH : IHandler (PROP := PROP) haltE where
  ihandle := fun _ _ _ => iprop(|={∅, ⊤}=> True)
  ihandle_mono := by
    iintro %i %Φ %Φ' %s %s' HΦwand #Hswand HH
    iexact HH

instance haltH_sequential : Sequential (PROP := PROP) haltH := by
  constructor
  iintro %i %Φ %s HH
  simpa [haltH] using HH

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler (PROP := PROP) E} [haltE -< E] [Hin : InH haltH H]

theorem wpi_halt {R} (Φ : R → PROP) :
    ⊢ (WPi HaltE.halt @> H; ⊤ {{ Φ }}) := by
  unfold HaltE.halt
  iapply wpi_bind
  iapply wpi_trigger (H' := haltH) (M := ⊤) (i := PUnit.unit)
  iapply fupd_mask_intro
  · exact Std.LawfulSet.empty_subset
  · iintro Hclose
    simp [haltH]
    imod Hclose
    ipure_intro
    trivial

theorem wpi_assume (P : Prop) [Decidable P] (Φ : { _x // P } → PROP) :
    (∀ HP, Φ HP) ⊢
    (WPi HaltE.assume P @> H; ⊤ {{ Φ }}) := by
  by_cases hP : P
  · unfold HaltE.assume
    simp [hP]
    iintro HΦ
    iapply wpi_ret
    iapply forall_elim ⟨⟨⟩, hP⟩
    iexact HΦ
  · unfold HaltE.assume
    simp [hP]
    iintro _
    iapply wpi_halt

end wpi_rules

end Carte.Event
