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
  logInfo m!"itime: ms={fmt3 (msOf (t1 - t0))} heartbeats={h1 - h0}"

elab "itimeN " n:num tac:tacticSeq : tactic => do
  let reps := max 1 n.getNat
  let mut samples : Array Nat := #[]
  let mut hbs : Array Nat := #[]
  for _ in [0:reps] do
    let st ← saveState
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoNanosNow
    evalTactic tac
    let t1 ← IO.monoNanosNow
    let h1 ← IO.getNumHeartbeats
    samples := samples.push (t1 - t0)
    hbs := hbs.push (h1 - h0)
    st.restore
  evalTactic tac
  let msList := ", ".intercalate (samples.toList.map (fun s => fmt3 (msOf s)))
  let hbList := ", ".intercalate (hbs.toList.map toString)
  logInfo m!"itime: repeats={reps} ms=[{msList}]"
