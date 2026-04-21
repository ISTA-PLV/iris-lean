import Carte.Core.Handler
import Carte.Core.WpiMask
import ITree

namespace Carte.Event

open Iris BI ITree Effects

section handler

variable {PROP : Type _} [BI PROP]

def demonicH {A : Type _} : IHandler (PROP := PROP) (demonicE A) where
  ihandle := fun i Φ _ => iprop(∀ a : {x // i.1 x}, Φ a)
  ihandle_mono := by
    iintro %i %Φ %Φ' %s %s' HΦwand #Hswand H
    iintro %a
    iapply HΦwand
    iapply H

instance demonicH_sequential {A : Type _} :
    Sequential (PROP := PROP) (demonicH (PROP := PROP) (A := A)) := by
  constructor
  iintro %i %Φ %s H
  simp [demonicH] at H ⊢
  exact H

end handler

def demonic_choice (A : Type _) {E : Effect} [demonicE A -< E] [Inhabited A] : ITree E A :=
  ITree.trigger (demonicE A) ((fun _ => True), inferInstance, inferInstance) >>=
    fun x => ITree.ITree.ret x.1

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler (PROP := PROP) E} {A : Type _}
  [sub : demonicE A -< E] [Hin : InH (demonicH (PROP := PROP) (A := A)) H]

theorem wpi_demonic_vis {R} (p : A → Prop) [DecidablePred p] [Inhabited {x // p x}]
    (k : {x // p x} → ITree E R) (M : CoPset) (Φ : R → PROP) :
    (∀ a, WPi k a @> H; M {{ Φ }}) ⊢
    (WPi (ITree.trigger (demonicE A) (p, inferInstance, inferInstance) >>= k) @> H; M {{ Φ }}) := by
  iintro Hwp
  iapply wpi_bind
  iapply wpi_trigger (H' := demonicH (PROP := PROP) (A := A))
  iapply fupd_mask_intro
  · exact Std.LawfulSet.empty_subset
  · iintro Hclose
    simp [demonicH]
    iintro %a
    imod Hclose
    imodintro
    iapply Hwp

theorem wpi_demonic [Inhabited A] (M : CoPset) (Φ : A → PROP) :
    (∀ a, Φ a) ⊢
    (WPi demonic_choice A @> H; M {{ Φ }}) := by
  iintro HΦ
  unfold demonic_choice
  change (WPi
    (ITree.trigger (demonicE A) ((fun _ => True), inferInstance, inferInstance) >>=
      fun x => ITree.ITree.ret x.1) @> H; M {{ Φ }})
  iapply (wpi_demonic_vis (H := H) (A := A) (p := fun _ => True)
    (k := fun x => ITree.ITree.ret x.1) (M := M) (Φ := Φ))
  iintro %a
  iapply wpi_ret
  iapply HΦ

end wpi_rules

section exec

open ITree.Exec

abbrev demonicEH := ITree.Effects.demonicEH

-- The Coq `seHandlerAdequate` layer does not currently exist in this Lean port.

end exec

end Carte.Event
