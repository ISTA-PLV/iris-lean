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

syntax "irunsolve" : tactic
--macro_rules
--  | `(tactic|irunsolve) => `(tactic|trivial)
macro_rules
  | `(tactic|irunsolve) => `(tactic|solve| simp [*, irun_solve])

theorem irun_apply.{u} {PROP : Type u} [BI PROP] {P Q Q' : PROP}
  (h1 : Q' ⊢ Q)
  (h2 : P ⊢ Q')
 : P ⊢ Q := h2.trans h1

def irunSearch (config : IRunConfig) (goal : IrisGoalShallow) (tree : DiscrTree IRunEntry) : TacticM (Option (Expr × List MVarId × List MVarId)) := do
  let { u, prop, bi, hyp, goal:=G } := goal
  if config.debug then logInfo m!"Goal: {G}"
  -- logInfo m!"IN LOOP: {G}"
  let G ← instantiateExprMVars G
  if G.isMVar then throwError "irun failed: goal has free metavars"
  let tacs ← tree.getMatch G
  let tacs := tacs.insertionSort λ a b => a.prio > b.prio
  for tac in tacs do
    if config.debug then logInfo m!"trying {tac.name}"
    match tac.tac with
    | .inl decl =>
      let info ← getConstInfo decl
      -- TODO: create new mvar level to prevent instantiating mvars in the goal, see https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Difference.20between.20DiscrTree.2EgetMatch.20and.20DiscrTree.2EgetUnify/near/513194806 ?
      let pf := mkConst decl (← mkFreshLevelMVarsFor info)
      let (args, _, targetTy) ← forallMetaTelescopeReducing (← inferType pf)
      let .some (Gnew, Gdecl) := unpackEntails targetTy | throwError "theorem is not entails, this should not happen"
      let .true ← withReducible <| isDefEq G Gdecl | continue

      let mut do_cont := false
      for mvar in args do
        let mvarId := mvar.mvarId!
        if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
          try
            let [] ← evalTacticAtRaw (← `(tactic|irunsolve)) mvarId | throwError "solver failed"
          catch e =>
            if config.debug then
              logInfo m!"[irun] error '{e.toMessageData}' when solving uninstantiated argument `{← instantiateMVars <| ← mvarId.getType}` of lemma {tac.name}"
            do_cont := true
            break
      if do_cont then continue

      if config.debug then logInfo m!"successfully applied {tac.name}"
      let m ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoalShallow.toExpr { u, prop, bi, hyp, goal := Gnew }
      let pf := mkApp7 (.const ``irun_apply [u]) prop bi hyp G Gnew (mkAppN pf args) m
      return some (pf, [m.mvarId!], [])
    | .inr tac =>
      let some res ← tac.tac.run goal config | continue
      if config.debug then logInfo m!"successfully applied {tac.name}"
      return some res
  return none


--def profileitM (_ : Type) (_ : String) (_ : Options) (act : TacticM α) : TacticM α := act
partial def irunCore (config : IRunConfig) (nsteps : Option Nat) : TacticM Unit := do profileitM Exception "irun" (← getOptions) do
  -- TODO: keep track of [IrisGoal]s instead of just MVars such that tactics can avoid reparsing
  let mut (goals, shelved) ← (← getGoals).partitionM λ m => do
    -- if config.debug then logInfo m!"goal: {repr (← m.getType).getAppFn'}"
    -- we need to use the ' variant since some tactics insert random mdata (e.g., no implicit lambda) into the goal
    return (← m.getType).isAppOfArity' ``Entails' 4
  -- if config.debug then
  --    logInfo m!"goals: {goals}"
  --    logInfo m!"shelved: {shelved}"
  let mut n := 0
  let tree := irunExt.getState (← getEnv)
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

      -- TODO: do we want this?
      let g ← instantiateMVars <| ← goal.getType
      let some ig := parseIrisGoalShallow? g | throwError "not in proof mode"
      let G' ← whnfR ig.goal
      let g' := {ig with goal:=G'}.toExpr
      -- TODO: alternatively, we can do goal.setType g'. Does this make a difference?
      progress_match := ig.goal != G'
      if progress_match then
        goal := ← goal.replaceTargetDefEq g'
      if config.debug then logInfo m!"progress: {progress_match}, G: {ig.goal}, G': {G'}"
/-
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
-/

    -- call dsimp on the goal, very expensive
    -- TODO: make this an option?
    if false then
      let g ← instantiateMVars <| ← goal.getType
      let ⟨g_new, _⟩ ← goal.withContext (dsimpWithExt `irun_simp g)
      goal := ← goal.replaceTargetDefEq g_new

    -- find a tactic or lemma to apply to the goal
    let res ← goal.withContext do
      let mut g ← instantiateMVars <| ← goal.getType
      let some ig := parseIrisGoalShallow? g | throwError "not in proof mode"
      irunSearch config ig tree

    match res with
    | some (pf, goals_new, shelved_new) =>
      goal.assign pf
      goals := goals_new ++ goals'
      shelved := shelved ++ shelved_new
    | none =>
      goals := goal :: goals'

    if res.isNone && !progress_match then
      if config.debug then logInfo m!"no progress, exiting"
      break
    n := n+1

  if !(nsteps == .none || nsteps == .some n) then
    logInfo s!"Did {n} steps"
  setGoals (goals ++ shelved)

elab "irun" cfg:Parser.Tactic.optConfig : tactic => do
  irunCore (← elabIRunConfig cfg) none

elab "irun" cfg:Parser.Tactic.optConfig colGt nsteps:num : tactic => do
  irunCore (← elabIRunConfig cfg) (some nsteps.getNat)

elab "irun" cfg:Parser.Tactic.optConfig colGt "∞" : tactic => do
  -- this number is sufficiently close to infinity for our purposes
  irunCore (← elabIRunConfig cfg) (some 100000)
