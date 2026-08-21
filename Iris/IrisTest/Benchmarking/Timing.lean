module

public import Lean

namespace IrisTest.Benchmarking
open Lean Elab Tactic Meta Command

public meta section

private def msOf (ns : Nat) : Float :=
  Float.ofNat ns / 1000000.0

private def fmt3 (x : Float) : String :=
  let scaled := (x * 1000.0).round.toUInt64.toNat
  let whole  := scaled / 1000
  let frac   := scaled % 1000
  s!"{whole}.{(toString frac)}"

private def median (xs : Array Nat) : Nat :=
  if xs.isEmpty then 0 else
    let s := xs.qsort (· < ·)
    s[s.size / 2]!

elab "itime " tac:tacticSeq : tactic => do
  let h0 ← IO.getNumHeartbeats
  let t0 ← IO.monoNanosNow
  evalTactic tac
  let t1 ← IO.monoNanosNow
  let h1 ← IO.getNumHeartbeats
  logInfo m!"BENCH tag=itime ms={fmt3 (msOf (t1 - t0))} heartbeats={h1 - h0}"

elab "itimeN " n:num tac:tacticSeq : tactic => do
  let reps := max 1 n.getNat
  let mut samples : Array Nat := #[]
  let mut hb : Nat := 0
  for i in [0:reps] do
    let st ← saveState
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoNanosNow
    evalTactic tac
    let t1 ← IO.monoNanosNow
    let h1 ← IO.getNumHeartbeats
    samples := samples.push (t1 - t0)
    if i == 0 then hb := h1 - h0
    st.restore
  evalTactic tac
  let lo := samples.foldl min samples[0]!
  let hi := samples.foldl max 0
  logInfo m!"BENCH tag=itime reps={reps} min_ms={fmt3 (msOf lo)} \
med_ms={fmt3 (msOf (median samples))} max_ms={fmt3 (msOf hi)} heartbeats={hb}"
