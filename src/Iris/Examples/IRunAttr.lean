/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Lean
import Qq
import Iris.BI
import Iris.ProofMode

open Lean Elab Tactic Meta Qq Iris.BI

namespace Iris.ProofMode

def dsimpWithExt (ext_name : Name) (e : Expr) : MetaM (Expr × Simp.Stats) := do
  let ext ← Lean.Meta.getSimpExtension? ext_name
  let theorems ← ext.get!.getTheorems
  let simpctx := ← Simp.mkContext (simpTheorems := #[theorems])
 --let { ctx:=simpctx, .. } ← mkSimpContext .missing (eraseLocal := false) (kind := .dsimp) (simpTheorems := pure theorems)
  -- TODO: use simpprocs as well?
  Meta.dsimp e simpctx {}

def simpWithExt (ext_name : Name) (e : Expr) (config := ({} : Simp.Config)) : MetaM (Simp.Result × Simp.Stats) := do
  let ext ← Lean.Meta.getSimpExtension? ext_name
  let theorems ← ext.get!.getTheorems
  let simpctx := ← Simp.mkContext (config:=config) (simpTheorems := #[theorems])
  Meta.simp e simpctx {}

register_simp_attr irun_simp
register_simp_attr irun_solve
register_simp_attr irun_preprocess

structure IrisGoalShallow where
  u : Level
  prop : Expr
  bi : Expr
  hyp : Expr
  goal : Expr

def IrisGoalShallow.toExpr (g : IrisGoalShallow) : Expr :=
  mkApp4 (.const ``Entails' [g.u]) g.prop g.bi g.hyp g.goal

def parseIrisGoalShallow? (expr : Expr) : Option IrisGoalShallow := do
  let_expr Entails' prop bi hyp goal := expr | none
  -- dbgTrace s!"{repr (expr.getAppFn')}" λ _ =>
  let u := expr.getAppFn'.constLevels![0]!
  some { u, prop, bi, hyp, goal }

partial def parseHypsFromShallow? (u : Level) (prop : Expr) (bi : Expr) (expr : Expr) :
    Option ((s : Expr) × @Hyps u prop bi s) := @parseHyps? u prop bi expr


structure IRunConfig where
  debug := false

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

def IRunEntrySerialized.deserialize (e : IRunEntrySerialized) : CoreM IRunEntry := do
--  IO.println s!"deserializing {repr e}"
  let tac  ← match e.tac with
           | .inl n => .pure (.inl n)
           | .inr n => unsafe do
             let ty := (← getConstInfo n.name).type
             if ty != .const ``IRunTacticType [] then
               throwError "The tactic should have type IRunTacticType."
             -- is this the compilation the right thing to do?
             let .defnInfo d ← getConstInfo n.name | throwError "The tactic should be a definition."
             let decl := (.defnDecl d)
             try
               compileDecl decl
             catch e =>
               IO.println (s!"error while compiling {n.name}: {← e.toMessageData.toString}")
             let tac ← evalConst IRunTacticType n.name
             return (.inr ⟨tac, n.name⟩ : Name ⊕ IRunTactic)
  return {tac, prio := e.prio, name := e.name}

/-- Environment extension for `irun` -/
initialize irunExt :
    ScopedEnvExtension (IRunEntrySerialized × Array DiscrTree.Key) (IRunEntry × Array DiscrTree.Key) (DiscrTree IRunEntry) ←
  registerScopedEnvExtension {
    mkInitial := .pure {}
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    ofOLeanEntry := fun _ (n, ks) => ImportM.runCoreM do return (← n.deserialize, ks)
    toOLeanEntry := fun (n, ks) => (n.serialize, ks)
  }

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

-- TODO: Is this unsafe a problem? Can we get around it?
initialize unsafe registerBuiltinAttribute {
  name := `irun_tac
  descr := "irun tactic"
  -- we ignore TC failures for BI, they should just create metavariables
  add := fun decl stx kind => MetaM.run' do Elab.Term.TermElabM.run' (ctx := {ignoreTCFailures := true}) do
    let prio := if stx[1][1].isMissing then some irun_default_prio else stx[1][1].isNatLit?
    let .some prio := prio | throwError "unknown prio: {stx[1][1]}"

    let pats ← stx[2].getSepArgs.mapM λ stx => do
      let stx ← `(iprop($(TSyntax.mk stx)))
      Term.elabTerm stx none

    let tac ← (IRunEntrySerialized.mk (.inr ⟨decl⟩) prio decl).deserialize
    for pat in pats do
      let key ← DiscrTree.mkPath pat
      irunExt.add (tac, key) kind
}
