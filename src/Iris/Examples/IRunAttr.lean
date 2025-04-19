/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Lean
import Qq
import Iris.BI

open Lean Elab Tactic Meta Qq Iris.BI

namespace Iris.ProofMode

def dsimpWithExt (ext_name : Name) (e : Expr) : MetaM (Expr × Simp.Stats) := do
  let ext ← Lean.Meta.getSimpExtension? ext_name
  let theorems ← ext.get!.getTheorems
  let simpctx := ← Simp.mkContext (simpTheorems := #[theorems])
 --let { ctx:=simpctx, .. } ← mkSimpContext .missing (eraseLocal := false) (kind := .dsimp) (simpTheorems := pure theorems)
  -- TODO: use simpprocs as well?
  Meta.dsimp e simpctx {}

def simpWithExt (ext_name : Name) (e : Expr) : MetaM (Simp.Result × Simp.Stats) := do
  let ext ← Lean.Meta.getSimpExtension? ext_name
  let theorems ← ext.get!.getTheorems
  let simpctx := ← Simp.mkContext (simpTheorems := #[theorems])
  Meta.simp e simpctx {}

register_simp_attr irun_simp
register_simp_attr irun_preprocess

def IRunTacticType : Type := MVarId → TacticM (Option (List MVarId × List MVarId))

def IRunTacticType.run (tac : IRunTacticType) : MVarId → TacticM (Option (List MVarId × List MVarId)) := tac

structure IRunTactic where
  name : Name
  tac : IRunTacticType

structure IRunEntry where
  tac : Name ⊕ IRunTactic
  prio : Nat
instance : BEq IRunEntry where
  beq _ _ := false
instance : Inhabited IRunEntry where
  default := ⟨.inl default, 0⟩

/-- Environment extension for `irun` -/
initialize irunExt :
    SimpleScopedEnvExtension (IRunEntry × Array DiscrTree.Key) (DiscrTree IRunEntry) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

def unpackEntails : Expr → Option (Expr × Expr)
  | .app (.app (.app (.app (.const ``Entails _) _) _) G') G => some (G', G)
  | _ => none

def irun_default_prio : Nat := 10

syntax (name := irun) "irun" ("?")? (num)?  : attr

initialize registerBuiltinAttribute {
  name := `irun
  descr := "irun lemma"
  add := fun decl stx kind => MetaM.run' do
    let prio := if stx[2][0].isMissing then some irun_default_prio else stx[1][0].isNatLit?
    let .some prio := prio | throwError "unknown prio: {stx[1][0]}"
    let declInfo ← getConstInfo decl
    let declTy := declInfo.type
    let (e, ty) ← forallTelescope declTy λ args ty => do
      let (res, _) ← simpWithExt `irun_preprocess ty
      let ty := res.expr
      return (← mkLambdaFVars args (← res.mkCast (mkAppN (← mkConstWithLevelParams decl) args)), ← mkForallFVars args ty)
    if !stx[1][0].isMissing then
      logInfo m!"{ty}"
    let newName : Name := .str declInfo.name "irun"
    let newDecl := (.defnDecl {name := newName, levelParams := declInfo.levelParams, type := ty, value := e, hints := .opaque, safety := .safe })
    addDecl newDecl
    let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing ty
    match unpackEntails targetTy with
    | some (_, G) =>
      -- IO.println s!"{G}"
      let key ← DiscrTree.mkPath G
      irunExt.add (⟨.inl newName, prio⟩, key) kind
    | _ => throwError "@[irun] unexpected type"
}

syntax (name := irun_tac) "irun_tac" (num "|")? (ppSpace term),* : attr

-- TODO: Is this unsafe a problem? Can we get around it?
initialize unsafe registerBuiltinAttribute {
  name := `irun_tac
  descr := "irun tactic"
  -- we ignore TC failures for BI, they should just create metavariables
  add := fun decl stx kind => MetaM.run' do Elab.Term.TermElabM.run' (ctx := {ignoreTCFailures := true}) do
    let prio := if stx[1][0].isMissing then some irun_default_prio else stx[1][0].isNatLit?
    let .some prio := prio | throwError "unknown prio: {stx[1][0]}"

    let pats ← stx[2].getSepArgs.mapM λ stx => do
      let stx ← `(iprop($(TSyntax.mk stx)))
      Term.elabTerm stx none

    let ty := (← getConstInfo decl).type
    if ty != .const ``IRunTacticType [] then
      throwError "The tactic should have type IRunTacticType."
    -- is this the compilation the right thing to do?
    let .defnInfo d ← getConstInfo decl | throwError "The tactic should be a definition."
    compileDecl (.defnDecl d)
    let tac ← evalConst IRunTacticType decl
    for pat in pats do
      let key ← DiscrTree.mkPath pat
      irunExt.add (⟨.inr ⟨decl, tac⟩, prio⟩, key) kind
}
