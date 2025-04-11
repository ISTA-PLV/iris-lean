/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Lean
import Qq
import Iris.BI

open Lean Elab Tactic Meta Qq Iris.BI

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

#check Syntax

def irun_default_prio : Nat := 10

initialize registerBuiltinAttribute {
  name := `irun
  descr := "irun lemma"
  add := fun decl stx kind => MetaM.run' do
    let prio := if stx[1][0].isMissing then some irun_default_prio else stx[1][0].isNatLit?
    let .some prio := prio | throwError "unknown prio: {stx[1][0]}"
    let declTy := (← getConstInfo decl).type
    let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    match unpackEntails targetTy with
    | some (_, G) =>
      -- IO.println s!"{G}"
      let key ← DiscrTree.mkPath G
      irunExt.add (⟨.inl decl, prio⟩, key) kind
    | _ => throwError "@[irun] unexpected type"
}

syntax (name := irun_tac) "irun_tac" (num "|")? (ppSpace term),* : attr

-- TODO: Is this unsafe a problem? Can we get around it?
initialize unsafe registerBuiltinAttribute {
  name := `irun_tac
  descr := "irun tactic"
  -- we ignore TC failures for BI, they should just create metavariables
  add := fun decl stx kind => MetaM.run' do Elab.Term.TermElabM.run' (ctx := {ignoreTCFailures := true}) do
    -- IO.println s!"{stx}"
    let prio := if stx[1][0].isMissing then some irun_default_prio else stx[1][0].isNatLit?
    let .some prio := prio | throwError "unknown prio: {stx[1][0]}"
    -- IO.println s!"prio: {prio}"

    -- TODO: for some reason this is not necessary anymore
    -- todo can we somehow disable typeclass search during elaboration?
    -- elaborate the patterns. We create a dummy [BiBase] to make elaboration succeed
    -- let propId ← mkFreshFVarId
    -- let biId ← mkFreshFVarId
    -- let ctx ← getLCtx
    -- let ctx := ctx.mkLocalDecl propId .anonymous (.sort 0)
    -- let ctx := ctx.mkLocalDecl biId .anonymous (mkApp (mkConst ``BIBase) (.fvar propId))
      -- withLCtx ctx (← getLocalInstances) do
      -- withNewLocalInstance ``BIBase (.fvar biId) do
    let pats ←
        stx[2].getSepArgs.mapM λ stx => do
          let stx ← `(iprop($(TSyntax.mk stx)))
          Term.elabTerm stx none
    -- IO.println s!"{pats}"

    let ty := (← getConstInfo decl).type
    if ty != .const ``IRunTacticType [] then
      throwError "The tactic should have type IRunTacticType"
    -- is this the compilation the right thing to do?
    let .defnInfo d ← getConstInfo decl | throwError "The tactic should be a definition"
    compileDecl (.defnDecl d)
    let tac ← evalConst IRunTacticType decl
    for pat in pats do
      let key ← DiscrTree.mkPath pat
      irunExt.add (⟨.inr ⟨decl, tac⟩, prio⟩, key) kind
}
