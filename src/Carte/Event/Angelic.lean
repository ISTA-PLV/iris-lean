import Carte.Core.Handler
import Carte.Core.WpiMask

import ITree

namespace Carte.Event

open Iris BI ITree Effects

section handler

variable {PROP : Type _} [BI PROP]

def angelicH (α : Type _) : IHandler (PROP := PROP) (angelicE α) where
  ihandle := λ p Φ _ => iprop(∃ a : {x // p x}, Φ a)
  ihandle_mono := by
    iintro %p %Φ %Φ' %s %s' HΦwand #Hswand H
    icases H with ⟨%a, HΦ⟩
    iexists a
    iapply HΦwand $$ HΦ

instance angelicH_sequential {α : Type _} :
    Sequential (PROP := PROP) (angelicH (PROP := PROP) α) := by
  constructor
  iintro %p %Φ %s H
  simp [angelicH]

end handler

section wpi_rules

open ITree

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler (PROP := PROP) E} {α : Type _}
  [sub : angelicE α -< E] [Hin : InH (angelicH (PROP := PROP) α) H]

-- Strong angelic rule: any concrete witness [a] satisfying [p] is enough to establish
-- the WP of the triggered angelic choice followed by [k].
theorem wpi_angelic_vis {R} (p : α → Prop) (k : {x // p x} → ITree E R)
    (a : {x // p x}) (M : CoPset) (Φ : R → PROP) :
    (WPi k a @> H; M {{ Φ }}) ⊢
    (WPi (ITree.trigger (angelicE α) p >>= k) @> H; M {{ Φ }}) := by
  iintro Hwp; iapply wpi_bind
  iapply wpi_trigger <| angelicH (PROP := PROP) α
  simp [angelicH]; iapply fupd_mask_intro
  · exact Std.LawfulSet.empty_subset
  · iintro Hemp; iexists a; imod Hemp; imodintro; iexact Hwp

-- set_option pp.all true in
-- TODO: Find the reason for iapply failed
theorem wpi_angelic (M : CoPset) (p : α → Prop) (a : {x // p x}) (Ψ : {x // p x} → PROP) :
    Ψ a ⊢ (WPi (choose_angelic p) @> H; M {{ Ψ }}) := by
  iintro HΨ; simp [choose_angelic]
  rw [← ITree.bind_ret (trigger (E₂ := E) (angelicE α) p)]
  sorry
  -- iapply wpi_angelic_vis (H := H) p (λ x => ITree.ret x) a M Ψ
  -- iapply wpi_ret
  -- iexact HΨ

end wpi_rules

section exec

open ITree.Exec

abbrev angelicEH := ITree.Effects.angelicEH

-- The Coq `seHandlerAdequate` layer does not currently exist in this Lean port.

end exec

end Carte.Event
