/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode
import Iris.Examples.IRunAttr

/-
next steps:
- rename tactics and everything to a consistent name
- add support for ⌜P⌝ -∗ G
- add support for ⌜P⌝ ∗ G
- add support for lif where one cannot prove either side
- add syntax for Lithium goals
- look into performance
- figure out how to avoid dsimp in wpsubst
- define wp
- add more lithium connectives
- prove sorrys
- do more examples
- define a notation for the language
-/

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem irun_apply.{u} {PROP : Type u} [BI PROP] {P Q Q' : PROP}
  (h1 : Q' ⊢ Q)
  (h2 : P ⊢ Q')
 : P ⊢ Q := h2.trans h1

--def profileitM (_ : Type) (_ : String) (_ : Options) (act : TacticM α) : TacticM α := act
partial def irunCore (nsteps : Option Nat) : TacticM Unit := do profileitM Exception "irun" (← getOptions) do
  -- TODO: keep track of [IrisGoal]s instead of just MVars such that tactics can avoid reparsing
  let mut goals ← getGoals
  let mut n := 0
  let mut shelved := []
  repeat
    if nsteps == some n then
      break
    let mut goal::goals' := goals | break
    if ← goal.isAssigned then
      goals := goals'
      continue
    let mut progress_match := false

    -- reduce matches, very cheap
    -- TODO: make this an option?
    if true then
      repeat do
        let g ← instantiateMVars <| ← goal.getType
        let some #[prop, bi, P, G] := g.appM? ``Entails' | throwError "not in proof mode"
        if G.isHeadBetaTarget then
          let G' := G.headBeta
          let g' := mkApp4 (.const ``Entails' [g.getAppFn.constLevels![0]!])
            prop bi P G'
          goal.setType g'
          progress_match := true
          continue
        if (← isMatcherApp G) then
          let some G' ← reduceRecMatcher? G | throwError s!"Cannot reduce matcher at step {n}"
          let g' := mkApp4 (.const ``Entails' [g.getAppFn.constLevels![0]!])
            prop bi P G'
          goal := ← goal.replaceTargetDefEq g'
          progress_match := true
          continue
        break

    -- call dsimp on the goal, very expensive
    -- TODO: make this an option?
    if false then
      let g ← instantiateMVars <| ← goal.getType
      let ⟨g_new, _⟩ ← goal.withContext (dsimpWithExt `irun_simp g)
      goal := ← goal.replaceTargetDefEq g_new

    -- find a tactic or lemma to apply to the goal
    let (progress, goals'', shelved') ← goal.withContext do
      let mut g ← instantiateMVars <| ← goal.getType
      let some { u, prop, bi, e, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
      -- logInfo m!"IN LOOP: {G}"
      let tree := irunExt.getState (← getEnv)
      let G ← instantiateExprMVars G
      if G.isMVar then throwError "irun failed: goal has free metavars"
      let tacs ← tree.getMatch G
      let tacs := tacs.insertionSort λ a b => a.prio < b.prio
      for tac in tacs do
        -- logInfo m!"trying {tac.name}"
        match tac.tac with
        | .inl decl =>
          let info ← getConstInfo decl
          -- TODO: create new mvar level to prevent instantiating mvars in the goal, see https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Difference.20between.20DiscrTree.2EgetMatch.20and.20DiscrTree.2EgetUnify/near/513194806 ?
          let pf := mkConst decl (← mkFreshLevelMVarsFor info)
          let (args, _, targetTy) ← forallMetaTelescopeReducing (← inferType pf)
          let .some (Gnew, Gdecl) := (unpackEntails targetTy) | throwError "theorem is not entails, this should not happen"
          let .true ← isDefEq G Gdecl | continue

          for mvar in args do
            let mvarId := mvar.mvarId!
            if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
              -- TODO: try to solve all unsolved args using a tactic
              throwError s!"[irun] argument with type `{← mvarId.getType}` of lemma {tac.name} not instantiated by unification"

          let m ← mkFreshExprSyntheticOpaqueMVar <|
            IrisGoal.toExpr { prop, bi, hyps := hyps, goal := Gnew }
          let pf := mkApp7 (.const ``irun_apply [u]) prop bi e G Gnew (mkAppN pf args) m
          goal.assign pf
          return (true, m.mvarId!::goals', shelved)
        | .inr tac =>
          let .some (goals_new, shelved_new) ← tac.tac.run goal | continue
          return (true, goals_new++goals', shelved++shelved_new)
      return (false, goal::goals', shelved)
    if !progress && !progress_match then
      break
    n := n+1
    goals := goals''
    shelved := shelved'

  if !(nsteps == .none || nsteps == .some n) then
    logInfo s!"Did {n} steps"
  setGoals (goals ++ shelved)

elab "irun" : tactic => do
  irunCore none

elab "irun" colGt nsteps:num : tactic => do
  irunCore (some nsteps.getNat)

elab "irun" colGt "∞" : tactic => do
  -- this number is sufficiently close to infinity for our purposes
  irunCore (some 100000)
