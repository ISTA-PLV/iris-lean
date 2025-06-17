/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode
import Iris.Lithium.Base
import Iris.Lithium.Lithium
import Iris.Lithium.Islaris.Isla
import Iris.Lithium.Islaris.Automation
import Iris.Lithium.Islaris.Instructions.Example.A0
import Iris.Lithium.Islaris.Instructions.Example.A4
import Iris.Lithium.Islaris.Instructions.Example.A8
import Iris.Lithium.Islaris.Instructions.Example.A10
import Iris.Lithium.Islaris.Instructions.Example.A14

namespace Islaris
open Lean Iris BI ProofMode Elab Meta Lithium
open Instructions.Example Aarch64

variable [BI.{u} PROP]

abbrev testStateSpec : Spec :=
  Spec.cons (.writeMem (0x101f1000#64) (0#64)) $
  Spec.cons (.instrTrap (0x000000001030000c#64)) $
  Spec.nil


set_option profiler true in
-- set_option trace.profiler true in
set_option Elab.async false in
#time example :
  ⊢ (do
    inhale (PROP:=PROP) (atom_with_ref (instr 0x0000000010300000#64) (some a0))
    inhale (atom_with_ref (instr 0x0000000010300004#64) (some a4))
    inhale (atom_with_ref (instr 0x0000000010300008#64) (some a8))
    inhale (atom_with_ref (instr 0x000000001030000c#64) none)
    inhale (atom_with_ref (instr 0x0000000010300010#64) (some a10))
    inhale (atom_with_ref (instr 0x0000000010300014#64) (some a14))

    inhale (do
      atom_with_ref (regCol sysRegs) ()
      atom_with_ref (reg "_PC") (.base <| .bits 0x0000000010300000#64)
      atom_with_ref (reg "R30") (.poison)
      atom_with_ref (reg "R1") (.poison)
      atom_with_ref (reg "R0") (.poison)
      atom_with_ref (reg "R27") (.base <| .bits 0x101f1000#64)
      atom_with_ref (reg "R28") (.poison)
      atom_with_ref (mmio 0x101f1000#64 8) ()
      atom_with_ref specTrace testStateSpec
    )
    asmOk .nil
    ).go := by
  istart
  simp only [irun_preprocess]
  irun
