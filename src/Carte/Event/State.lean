import Carte.Core.Handler
import Carte.Core.WpiMask
import ITree

namespace Carte.Event

open Iris BI ITree Effects

class stateInterp (PROP : Type _) [BI PROP] (S : Type _) where
  state_interp : S → PROP

export stateInterp (state_interp)

def get_state {S : Type _} {E : Effect} [stateE S -< E] : ITree E S :=
  ITree.trigger (stateE S) id

def set_state {S : Type _} {E : Effect} [stateE S -< E] (s' : S) : ITree E PUnit :=
  ITree.trigger (stateE S) (fun _ => s') >>= fun _ => ITree.ITree.ret PUnit.unit

section exec

open ITree.Exec

abbrev stateEH := ITree.Effects.stateEH

-- The Coq `seHandlerAdequate` layer does not currently exist in this Lean port.

end exec

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def stateH (S : Type _) [stateInterp PROP S] : IHandler (PROP := PROP) (stateE S) where
  ihandle := fun i Φ _ => iprop(∀ s, state_interp s ={∅}=∗ state_interp (i s) ∗ Φ s)
  ihandle_mono := by
    iintro %i %Φ %Φ' %s %s' HΦwand #Hswand HH
    iintro %st Hst
    ihave Hstep := HH $$ Hst
    imod Hstep
    imodintro
    icases Hstep with ⟨Hst, HΦ⟩
    isplitl [Hst]
    · iexact Hst
    · iapply HΦwand $$ HΦ

instance stateH_sequential (S : Type _) [stateInterp PROP S] :
    Sequential (PROP := PROP) (stateH (PROP := PROP) S) := by
  constructor
  iintro %i %Φ %s HH
  simpa [stateH] using HH

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {S : Type _} [stateInterp PROP S]
  {E : Effect} {H : IHandler (PROP := PROP) E}
  [stateE S -< E] [Hin : InH (stateH (PROP := PROP) S) H]

def get_state_pre (Φ : S → PROP) : PROP :=
  BIBase.forall (PROP := PROP) fun s : S =>
    BIBase.wand
      (@state_interp PROP _ S _ s)
      (Iris.FUpd.fupd (PROP := PROP) ∅ ∅ <|
        BIBase.sep (@state_interp PROP _ S _ s) (Φ s))

def set_state_pre (s' : S) (Φ : PUnit → PROP) : PROP :=
  BIBase.forall (PROP := PROP) fun s : S =>
    BIBase.wand
      (@state_interp PROP _ S _ s)
      (Iris.FUpd.fupd (PROP := PROP) ∅ ∅ <|
        BIBase.sep (@state_interp PROP _ S _ s') (Φ PUnit.unit))

theorem wpi_get_state (M : CoPset) (Φ : S → PROP) :
    get_state_pre (PROP := PROP) (S := S) Φ ⊢
    wpi_mask (H := H) M (get_state (S := S)) Φ := by
  sorry

theorem wpi_set_state (s' : S) (M : CoPset) (Φ : PUnit → PROP) :
    set_state_pre (PROP := PROP) (S := S) s' Φ ⊢
    wpi_mask (H := H) M (set_state (S := S) s') Φ := by
  sorry

end wpi_rules

end Carte.Event
