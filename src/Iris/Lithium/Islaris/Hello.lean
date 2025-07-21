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
import Iris.Lithium.Islaris.Instructions.Hello.A0
import Iris.Lithium.Islaris.Instructions.Hello.A4
import Iris.Lithium.Islaris.Instructions.Hello.A8
import Iris.Lithium.Islaris.Instructions.Hello.Ac
import Iris.Lithium.Islaris.Instructions.Hello.A10
import Iris.Lithium.Islaris.Instructions.Hello.A14
import Iris.Lithium.Islaris.Instructions.Hello.A18
import Iris.Lithium.Islaris.Instructions.Hello.A1C

namespace Islaris
open Lean Iris BI ProofMode Elab Meta Lithium
open Instructions.Hello Aarch64

variable [BI.{u} PROP]

abbrev helloWorldString : List (BitVec 8) :=
  [ 0x48#8, 0x65#8, 0x6c#8, 0x6c#8,  0x6f#8, 0x2c#8, 0x20#8, 0x57#8,  0x6f#8, 0x72#8, 0x6c#8, 0x64#8, 0x21#8, 0x0a#8, 0x00#8]

abbrev helloWorldStringPrinted : List (BitVec 8) :=
  helloWorldString.take (helloWorldString.length - 1)

abbrev helloSpecTrace : Spec :=
  Spec.app (helloWorldStringPrinted.map (λ b : BitVec 8 => .writeMem 0x101f1000#64 b)) $
  Spec.cons (.instrTrap (0x0000000010300020#64)) $
  Spec.nil

def helloWorldPrintedTrace (i : BitVec 64) : List Label :=
  (helloWorldStringPrinted.drop i.toNat).map (λ b : BitVec 8 => .writeMem 0x101f1000#64 b)

@[irun]
theorem specConsOk_helloWorldPrintedTrace_writeMem a v i P:
  specConsOkR (PROP:=PROP) (Label.writeMem a v) (Spec.app (helloWorldPrintedTrace i) P) :- do
    let v ← bitvecCastOk v.toBitVec 8
    exhale (prop (i.toNat < helloWorldStringPrinted.length ∧
                  a = 0x101f1000#64 ∧ v = helloWorldString[i.toNat]!))
    return (Spec.app (helloWorldPrintedTrace (i+1)) P) := by mysorry

@[irun]
theorem specConsOk_helloWorldPrintedTrace_instr a i P:
  specConsOkR (PROP:=PROP) (Label.instrTrap a) (Spec.app (helloWorldPrintedTrace i) P) :- do
    exhale (prop (i.toNat ≥ helloWorldStringPrinted.length))
    let s ← specConsOk (Label.instrTrap a) P
    return s := by mysorry


abbrev helloLoopSpec (i : BitVec 64) : PROP :=
  exhaleR (prop (i + 1 < helloWorldString.length)) λ _ =>
  exhaleR (atom_with_ref (regCol sysRegs) ()) λ _ =>
  exhaleR (atom_with_ref (array 0x0000000010300690#64 8 helloWorldString.length) (helloWorldString)) λ _ =>
  exhaleR (atom_with_ref (reg "R2") (.base <| .bits 0x101f1000#64)) λ _ =>
  exhaleR (atom_with_ref (reg "R1") (.base <| .bits (0x0000000010300690#64 + i))) λ _ =>
  exhaleR (atom_with_ref (reg "R0") (.base <| .bits (helloWorldString[i.toNat]!.zeroExtend 64))) λ _ =>
  exhaleR (atom_with_ref (specTrace) (
    Spec.app (helloWorldPrintedTrace i) $
    Spec.cons (.instrTrap (0x0000000010300020#64)) $
    Spec.nil)) λ _ =>
  doneR

@[irun]
theorem cancel_array_memPtsto_solve a a' n len vs :
  a ≤ a' ∧ a' ≤ a + BitVec.ofNat 64 len * BitVec.ofNat 64 n →
  cancelR (PROP:=PROP) (array a n len # vs) (memPtsto a') :- .pure (.array a n len vs) := by mysorry


@[irun]
theorem inhale_persLi_instrPre a G (hmono : ∀ _ _, ⊢ _) E :
  inhaleR (PROP:=PROP)
    (persLi (Li.mk (λ _ : Empty → PROP => instrPre'R true a G) hmono)) E ⊣
    inhaleR (pers (atom_with_ref (instrPreA a) G)) E
 := by mysorry

set_option Elab.async false in
#time example i :
  (BitVec.ofNat 64 i) + 1 < 15 →
  271582864#64 ≤
    BitVec.zeroExtend (8 + (4 + (51 + 1 - 0)))
      (0#4 ++ BitVec.extractLsb' 0 (51 + 1 - 0) (271582864#64 + BitVec.ofNat 64 i + 1#64)) ∧
  BitVec.zeroExtend (8 + (4 + (51 + 1 - 0)))
      (0#4 ++ BitVec.extractLsb' 0 (51 + 1 - 0) (271582864#64 + BitVec.ofNat 64 i + 1#64)) ≤
    271582864#64 + BitVec.ofNat 64 helloWorldString.length * 8#64 := by
    intros
    simp
    bv_decide

@[simp]
theorem zeroExtend_append_extractLsb x :
  x < 0x10000000000000#64 →
  (BitVec.setWidth 64
          (0#4 ++ BitVec.extractLsb' 0 52 x)) = x := by
  bv_decide

@[simp, irun_solve]
theorem hello_simp_find_array1 i :
--  (BitVec.ofNat 64 i) + 1 < 15 →
  271582864#64 ≤ BitVec.setWidth 64 (0#4 ++ BitVec.extractLsb' 0 52 (271582864#64 + BitVec.ofNat 64 i + 1#64)) ∧
    BitVec.setWidth 64 (0#4 ++ BitVec.extractLsb' 0 52 (271582864#64 + BitVec.ofNat 64 i + 1#64)) ≤ 271582984#64 := by
  sorry
  -- bv_decide

-- set_option pp.all true in
example i :
  271582864#64 ≤
    BitVec.zeroExtend (8 + (4 + (51 + 1 - 0)))
      (0#4 ++ BitVec.extractLsb' 0 (51 + 1 - 0) (271582864#64 + BitVec.ofNat 64 i + 1#64)) ∧
  BitVec.zeroExtend (8 + (4 + (51 + 1 - 0)))
      (0#4 ++ BitVec.extractLsb' 0 (51 + 1 - 0) (271582864#64 + BitVec.ofNat 64 i + 1#64)) ≤
    271582864#64 + BitVec.ofNat 64 helloWorldString.length * 8#64 := by
    simp [*, irun_solve]

macro_rules
 | `(tactic|irunsolve) => `(tactic|trivial)

-- set_option profiler true in
set_option trace.profiler true in
set_option Elab.async false in
#time
theorem hello_loop (i : BitVec 64) :
  ⊢ (do
    inhale (PROP:=PROP) (atom (mmio 0x101f1000#64 0x10))
    inhale (atom_with_ref (instr 0x0000000010300014#64) (some a14))
    inhale (atom_with_ref (instr 0x0000000010300018#64) (some a18))
    inhale (atom_with_ref (instr 0x000000001030001c#64) (some a1c))
    inhale (atom_with_ref (instr 0x0000000010300020#64) none)
    inhale (persLi (instrPre (0x0000000010300014#64) (fromEmpty λ _ => helloLoopSpec (i+1))))
    instrBody (0x0000000010300014#64) (fromEmpty λ _ => helloLoopSpec i)
  ).go := by
  istart
  simp only [irun_preprocess]
  -- set_option trace.profiler true in
  irun
  have h : 271582864#64 ≤
    BitVec.zeroExtend (8 + (4 + (51 + 1 - 0))) (0#4 ++ BitVec.extractLsb' 0 (51 + 1 - 0) (271582864#64 + i + 1#64)) ∧
  BitVec.zeroExtend (8 + (4 + (51 + 1 - 0))) (0#4 ++ BitVec.extractLsb' 0 (51 + 1 - 0) (271582864#64 + i + 1#64)) ≤
    271582864#64 + BitVec.ofNat 64 helloWorldString.length * 8#64 := by
    rename PUnit => x
    clear x
    simp
    bv_decide
  -- have h : 271582864#64 ≤
  --   BitVec.zeroExtend (8 + (4 + (51 + 1 - 0)))
  --     (0#4 ++ BitVec.extractLsb' 0 (51 + 1 - 0) (271582864#64 + BitVec.ofNat 64 i + 1#64)) ∧
  -- BitVec.zeroExtend (8 + (4 + (51 + 1 - 0)))
  --     (0#4 ++ BitVec.extractLsb' 0 (51 + 1 - 0) (271582864#64 + BitVec.ofNat 64 i + 1#64)) ≤
  --   271582864#64 + BitVec.ofNat 64 helloWorldString.length * 8#64 := by simp
  -- set_option trace.profiler true in
  irun
  all_goals mysorry
/-
  · simp_all
    rename PUnit => x
    clear x
    constructor
    · sorry
    · bv_decide
  · simp
    rename PUnit => x
    clear x
    bv_decide
  · simp at *
  · simp at *
    rename PUnit => x
    clear x
    sorry
  · simp at *
    sorry
  · simp at *
    rename PUnit => x
    clear x
    bv_decide
  · simp at *
    sorry
  · simp at *
    sorry
-/
  -- mysorry
