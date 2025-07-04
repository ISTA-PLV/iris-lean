/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode
import Iris.Lithium.Base

namespace Iris.Lithium
open Lean Elab Tactic Meta Iris.BI Iris.ProofMode

register_simp_attr irun_simp
register_simp_attr irun_solve
register_simp_attr irun_preprocess

structure IRunConfig where
  debug := false
  test := false

declare_config_elab elabIRunConfig IRunConfig


def IRunTacticType : Type := IrisGoalShallow → IRunConfig → TacticM (Option (Expr × List MVarId × List MVarId))

def IRunTacticType.run (tac : IRunTacticType) : IrisGoalShallow → IRunConfig → TacticM (Option (Expr × List MVarId × List MVarId)) := tac


structure IRunTactic where
  tac : IRunTacticType
  name : Name

structure IRunEntry where
  tac : Name ⊕ IRunTactic
  prio : Nat
  name : Name
instance : BEq IRunEntry where
  beq _ _ := false
instance : Inhabited IRunEntry where
  default := ⟨.inl default, 0, default⟩

structure IRunTacticSerialized where
  name : Name
deriving Repr

structure IRunEntrySerialized where
  tac : Name ⊕ IRunTacticSerialized
  prio : Nat
  name : Name
deriving Repr
instance : BEq IRunEntrySerialized where
  beq _ _ := false
instance : Inhabited IRunEntrySerialized where
  default := ⟨.inl default, 0, default⟩

def IRunEntry.serialize (e : IRunEntry) : IRunEntrySerialized := {
  tac := match e.tac with
         | .inl n => .inl n
         | .inr n => .inr ⟨n.name⟩
  prio := e.prio
  name := e.name
}

def IRunEntrySerialized.deserialize (e : IRunEntrySerialized) (compile : Bool) : CoreM IRunEntry := do
  -- IO.println s!"deserializing {repr e}"
  let tac  ← match e.tac with
    | .inl n => .pure (.inl n)
    | .inr n => unsafe do
      let mut name := n.name
      let ty := (← getConstInfo n.name).type
      if ty != .const ``IRunTacticType [] then
        throwError "The tactic should have type IRunTacticType."
      if compile then
        -- is this the compilation the right thing to do?
        let d ← getConstInfoDefn n.name
        name := d.name ++ `_replay
        let decl := (.defnDecl {d with name := name})
        try
          withOptions (λ opt => Elab.async.set opt false) <|
            addAndCompile decl
        catch e =>
          IO.println s!"error while compiling {n.name}: {← e.toMessageData.toString}"
      let tac ← evalConst IRunTacticType name
      return (.inr ⟨tac, n.name⟩ : Name ⊕ IRunTactic)
  return {tac, prio := e.prio, name := e.name}

/-- Environment extension for `irun` -/
initialize irunExt :
    ScopedEnvExtension (IRunEntrySerialized × Array DiscrTree.Key) (IRunEntry × Array DiscrTree.Key) (DiscrTree IRunEntry) ←
  registerScopedEnvExtension {
    mkInitial := .pure {}
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    ofOLeanEntry := fun _ (n, ks) => ImportM.runCoreM do return (← n.deserialize (compile:=false), ks)
    toOLeanEntry := fun (n, ks) => (n.serialize, ks)
  }

initialize registerTraceClass `IRun.step

def unpackEntails : Expr → Option (Expr × Expr)
  | .app (.app (.app (.app (.const ``Entails _) _) _) G') G => some (G', G)
  | _ => none

def irun_default_prio : Nat := (eval_prio default)

syntax (name := irun) "irun" (":" prio)? ("?")?  : attr

initialize registerBuiltinAttribute {
  name := `irun
  descr := "irun lemma"
  add := fun decl stx kind => MetaM.run' do
    -- TODO: use evalPrio?
    let prio := if stx[1][1].isMissing then some irun_default_prio else stx[1][1].isNatLit?
    let .some prio := prio | throwError "unknown prio: {stx[1][1]}"
    let declInfo ← getConstInfo decl
    let declTy := declInfo.type
    let (e, ty) ← forallTelescope declTy λ args ty => do
      -- we set iota to false since to reduces pattern matches on tuples to projections, which can cause weird effects
      let (res, _) ← simpWithExt `irun_preprocess ty (config := {iota := false})
      let ty := res.expr
      return (← mkLambdaFVars args (← res.mkCast (mkAppN (← mkConstWithLevelParams decl) args)), ← mkForallFVars args ty)
    if !stx[2][0].isMissing then
      logInfo m!"{ty}"
    let newName : Name := .str declInfo.name "irun"
    let newDecl := (.defnDecl {name := newName, levelParams := declInfo.levelParams, type := ty, value := e, hints := .opaque, safety := .safe })
    addDecl newDecl
    let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing ty
    match unpackEntails targetTy with
    | some (_, G) =>
      let key ← DiscrTree.mkPath G
      -- logInfo m!"Goal: {G}, key: {key}"
      irunExt.add (⟨.inl newName, prio, decl⟩, key) kind
    | _ => throwError "@[irun] unexpected type"
}

syntax (name := irun_tac) "irun_tac" (":" prio)? (ppSpace term),* : attr

initialize registerBuiltinAttribute {
  name := `irun_tac
  descr := "irun tactic"
  -- we ignore TC failures for BI, they should just create metavariables
  add := fun decl stx kind => MetaM.run' do Elab.Term.TermElabM.run' (ctx := {ignoreTCFailures := true}) do
    let prio := if stx[1][1].isMissing then some irun_default_prio else stx[1][1].isNatLit?
    let .some prio := prio | throwError "unknown prio: {stx[1][1]}"

    let pats ← stx[2].getSepArgs.mapM λ stx => do
      let stx ← `(iprop($(TSyntax.mk stx)))
      Term.elabTerm stx none

    let tac ← (IRunEntrySerialized.mk (.inr ⟨decl⟩) prio decl).deserialize (compile:=true)
    for pat in pats do
      let key ← DiscrTree.mkPath pat
      irunExt.add (tac, key) kind
}
