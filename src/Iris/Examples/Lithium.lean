/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
--import Lean.Parser.Do
--import Lean.Elab.Do
import Iris.BI
import Iris.ProofMode
import Iris.Examples.IRunAttr
import Iris.Examples.IRun
import Iris.Examples.Exp

-- this avoids the warnings from sorry
axiom exfalso (P : Prop) : P
syntax "mysorry" : tactic
macro_rules
--| `(tactic|mysorry) => `(tactic|sorry)
| `(tactic|mysorry) => `(tactic|apply exfalso)

syntax:min term " ≫ " term:min1 : term
syntax:min term " ≫= " term:min1 : term

macro_rules
  | `($a ≫= $args) => `(.bind $a $args)
  | `($a ≫ $args) => `(.bind $a λ _ => $args)

/-
Next steps:
- add support for all
- add support for inhale (atom A) by rewriting to a ← all; inhale (atom_with_ref A a)
- add support for inhale (prop P)
- add support for exhale (prop P)
- add support for exhale (atom_with_ref A a) by rewriting to a' ← exhale (atom A); exhale (prop (a = a'))
- add support for lif where one cannot prove either side
- add subsumption for when atoms do not match up directly as in cancelation
- look into function specifications
- define wp
- add more lithium connectives
- prove sorrys
- do more examples
- define a notation for the language
- look into namespaces and using export
-/

attribute [irun_preprocess] Pure.pure Bind.bind

namespace Iris.Lithium
open Lean BI Std

variable [BI.{u} PROP] {α : Type v} {β : Type w}

structure Atom (α : Type v) where
  ref : α → PROP

structure InEx (α : Type v) where
  body : α → PROP

structure Li (α : Type v) where
  run : (α → PROP) → PROP
  mono' E1 E2 : ⊢ run E1 -∗ (∀ a, E1 a -∗ E2 a) -∗ run E2
attribute [irun_preprocess] Li.run

section InEx

def InEx.pure (a : α) : @InEx PROP α :=
  InEx.mk λ b => iprop(⌜a = b⌝)

def InEx.bind (L1 : @InEx PROP α) (L2 : α → @InEx PROP β) :
  @InEx PROP β :=
  InEx.mk λ b => iprop(∃ a, L1.body a ∗ (L2 a).body b)

instance : Monad (@InEx PROP) where
  pure := .pure
  bind := .bind

def atom (A : @Atom PROP α) : @InEx PROP α := InEx.mk A.ref
def atom_with_ref (A : @Atom PROP α) (a : α) : @InEx PROP Unit := .mk λ _ => iprop(A.ref a)
def prop (P : Prop) : @InEx PROP Unit := .mk λ _ => iprop(⌜P⌝)

end InEx

@[irun_preprocess]
def Li.pure (a : α) : @Li PROP _ α := {
  run E := E a
  mono' E1 E2 := by
    dsimp
    iintro HE Hwand
    ispecialize Hwand HE
    iassumption
}

@[irun_preprocess]
def Li.bind (G1 : @Li PROP _ α) (G2 : α → @Li PROP _ β) :
  @Li PROP _ β := {
  run E := G1.run (λ a => (G2 a).run E)
  mono' E1 E2 := by
    dsimp
    iintro HE Hwand
    mysorry
}

instance : Monad (@Li PROP _) where
  pure := .pure
  bind := .bind

def empty : PEmpty → PROP := λ e => nomatch e

@[irun_preprocess]
def Li.go (G : @Li PROP _ PEmpty) : PROP := G.run empty

def exhaleR (L : @InEx PROP α) (E : α → PROP) : PROP :=
  iprop(∃ a, L.body a ∗ E a)

@[irun_preprocess]
def exhale (L : @InEx PROP α) : @Li PROP _ α := {
  run := exhaleR L
  mono' E1 E2 := by
    dsimp [exhaleR]
    iintro ⟨a, HL, HE⟩ Hwand
    iexists a
    isplit l [HL]
    iassumption
    ispecialize Hwand HE
    iassumption
}

def inhaleR (L : @InEx PROP α) (E : α → PROP) : PROP :=
  iprop(∀ a, L.body a -∗ E a)

@[irun_preprocess]
def inhale (L : @InEx PROP α) : @Li PROP _ α := {
  run := inhaleR L
  mono' E1 E2 := by
    dsimp [inhaleR]
    iintro HE Hwand a HL
    ispecialize HE HL
    ispecialize Hwand HE
    iassumption
}

def allR (α : Type v) (E : α → PROP) : PROP :=
  iprop(∀ a, E a)

@[irun_preprocess]
def all (α : Type v) : @Li PROP _ α := {
  run := allR α
  mono' E1 E2 := by
    dsimp [allR]
    iintro HE Hwand a
    ispecialize HE a
    ispecialize Hwand HE
    iassumption
}

def doneR : PROP := iprop(True)

@[irun_preprocess]
def done : @Li PROP _ α := {
  run E := doneR
  mono' E1 E2 := by
    dsimp [doneR]
    iintro HE Hwand
    iassumption
}

def lifR (P : Prop) (E1 E2 : PROP) : PROP :=
  iprop((⌜P⌝ -∗ E1) ∧ (⌜¬P⌝ -∗ E2))

@[irun_preprocess]
def lif (P : Prop) (G1 G2 : @Li PROP _ α) : @Li PROP _ α := {
  run E := lifR P (G1.run E) (G2.run E)
  mono' E1 E2 := by
    dsimp
    iintro HE Hwand
    mysorry
}

def dsimpR {α : Type _} [BI PROP] (_ : Lean.Name) (a : α) (E : α → PROP) : PROP := E a

@[irun_preprocess]
def dsimp {α : Type _} [BI PROP] (n : Lean.Name) (a : α) : @Li PROP _ α := {
  run := dsimpR n a
  mono' E1 E2 := by
    simp [dsimpR]
    mysorry
}

-- TODO: add R variant
def dualizing (G : @Li PROP _ PEmpty) : @Li PROP _ Unit := {
  run E := iprop(G.run empty -∗ E ⟨⟩)
  mono' E1 E2 := by
    dsimp
    iintro HE Hwand HG
    ispecialize HE HG
    ispecialize Hwand HE
    iassumption
}

---- TODO: What are good precedences?
--notation:35 G:36 " ⇓ " E:35 => run G E
--notation:35 G:36 " ⇓ " "!" => run G empty

--def entails (G1 G2 : @Li PROP _ α) : Prop :=
--  ∀ E, G1.run E ⊢ G2.run E

--notation:25 G1:29 ":-" G2:25 => (entails G2 G1)
--set_option quotPrecheck false in -- TODO: Why is this necessary?
--notation:25 G1:29 ":-" G2:25 => (∀ E, (G2 ⇓ E ⊢ G1 ⇓ E))
notation:25 P:29 "⊣" Q:25 => (Q ⊢ P)
set_option quotPrecheck false in -- TODO: Why is this necessary?
notation:25 P:29 ":-" Q:25 => (∀ E, Li.run Q E ⊢ P E)

--notation:25 G1:29 ":-" G2:25 => (run! G2 ⊢ run! G1)

-- @[irun]
-- theorem run_bind (G1 : @Li PROP _ α) (G2 : α → Li β)
--   (E : β → PROP) :
--    G1.bind G2 ⇓ E ⊣ (G1 ⇓ λ b => G2 b ⇓ E) := by
--     simp [Li.bind, Li.run, Li.run]

-- @[irun]
-- theorem run_pure (a : α) (E : α → PROP) :
--    .pure a ⇓ E ⊣ E a := by
--     simp [Li.pure, Li.run, Li.run]

attribute [irun_preprocess] Li.run

@[irun]
theorem exhale_bind (L1 : @InEx PROP α) (L2 : α → InEx β) :
  exhaleR (L1.bind L2) :-
    ((exhale L1).bind λ a => exhale (L2 a)) := by
    dsimp [exhaleR, InEx.bind]
    mysorry

@[irun]
theorem inhale_bind (L1 : @InEx PROP α) (L2 : α → InEx β) E :
  inhaleR (L1.bind L2) E ⊣
   inhaleR L1 λ a => inhaleR (L2 a) E := by
    dsimp [inhaleR, InEx.bind]
    mysorry

@[irun]
theorem exhale_pure (a : α) E :
  exhaleR (PROP:=PROP) (.pure a) E ⊣ E a := by
    dsimp [exhaleR, InEx.pure]
    mysorry

@[irun]
theorem inhale_pure (a : α) E :
  inhaleR (PROP:=PROP) (.pure a) E ⊣ E a := by
    dsimp [inhaleR, InEx.pure]
    mysorry


--set_option pp.universes true

def test_inex (A : @Atom PROP Nat) : @InEx PROP Bool :=
  atom A ≫= λ n =>
  atom_with_ref A n ≫
  .pure (n == 1)

/-
section test
open Elab Term Lean.Parser.Term Parser

syntax (name := gdo) "gdo" doSeq:term

private def liftMethodDelimiter (k : SyntaxNodeKind) : Bool :=
  k == ``Lithium.gdo ||
  k == ``Parser.Term.do ||
  k == ``Parser.Term.doSeqIndent ||
  k == ``Parser.Term.doSeqBracketed ||
  k == ``Parser.Term.termReturn ||
  k == ``Parser.Term.termUnless ||
  k == ``Parser.Term.termTry ||
  k == ``Parser.Term.termFor

private def getDoSeqElems (doSeq : Syntax) : List Syntax :=
  if doSeq.getKind == ``Parser.Term.doSeqBracketed then
    doSeq[1].getArgs.toList.map fun arg => arg[0]
  else if doSeq.getKind == ``Parser.Term.doSeqIndent then
    doSeq[0].getArgs.toList.map fun arg => arg[0]
  else
    []

private def getDoSeq (doStx : Syntax) : Syntax :=
  doStx[1]


/-- Given `stx` which is a `letPatDecl`, `letEqnsDecl`, or `letIdDecl`, return true if it has binders. -/
private def letDeclArgHasBinders (letDeclArg : Syntax) : Bool :=
  let k := letDeclArg.getKind
  if k == ``Parser.Term.letPatDecl then
    false
  else if k == ``Parser.Term.letEqnsDecl then
    true
  else if k == ``Parser.Term.letIdDecl then
    -- letIdLhs := binderIdent >> checkWsBefore "expected space before binders" >> many (ppSpace >> letIdBinder)) >> optType
    let binders := letDeclArg[1]
    binders.getNumArgs > 0
  else
    false

/-- Return `true` if the given `letDecl` contains binders. -/
private def letDeclHasBinders (letDecl : Syntax) : Bool :=
  letDeclArgHasBinders letDecl[0]

private def liftMethodForbiddenBinder (stx : Syntax) : Bool :=
  let k := stx.getKind
  -- TODO: make this extensible in the future.
  if k == ``Parser.Term.fun || k == ``Parser.Term.matchAlts ||
     k == ``Parser.Term.doLetRec || k == ``Parser.Term.letrec then
     -- It is never ok to lift over this kind of binder
    true
  -- The following kinds of `let`-expressions require extra checks to decide whether they contain binders or not
  else if k == ``Parser.Term.let then
    letDeclHasBinders stx[1]
  else if k == ``Parser.Term.doLet then
    letDeclHasBinders stx[2]
  else if k == ``Parser.Term.doLetArrow then
    letDeclArgHasBinders stx[2]
  else
    false

private partial def hasLiftMethod : Syntax → Bool
  | Syntax.node _ k args =>
    if liftMethodDelimiter k then false
    -- NOTE: We don't check for lifts in quotations here, which doesn't break anything but merely makes this rare case a
    -- bit slower
    else if k == ``Parser.Term.liftMethod then true
    -- For `pure` if-then-else, we only lift `(<- ...)` occurring in the condition.
    else if k == ``termDepIfThenElse || k == ``termIfThenElse then args.size >= 2 && hasLiftMethod args[1]!
    else args.any hasLiftMethod
  | _ => false

variable (baseId : Name) in
private partial def expandLiftMethodAux (inQuot : Bool) (inBinder : Bool) : Syntax → StateT (List Syntax) TermElabM Syntax
  | stx@(Syntax.node i k args) =>
    if k == choiceKind then do
      -- choice node: check that lifts are consistent
      let alts ← stx.getArgs.mapM (expandLiftMethodAux inQuot inBinder · |>.run [])
      let (_, lifts) := alts[0]!
      unless alts.all (·.2 == lifts) do
        throwErrorAt stx "cannot lift `(<- ...)` over inconsistent syntax variants, consider lifting out the binding manually"
      modify (· ++ lifts)
      return .node i k (alts.map (·.1))
    else if liftMethodDelimiter k then
      return stx
    -- For `pure` if-then-else, we only lift `(<- ...)` occurring in the condition.
    else if h : args.size >= 2 ∧ (k == ``termDepIfThenElse || k == ``termIfThenElse) then do
      let inAntiquot := stx.isAntiquot && !stx.isEscapedAntiquot
      let arg1 ← expandLiftMethodAux (inQuot && !inAntiquot || stx.isQuot) inBinder args[1]
      let args := args.set! 1 arg1
      return Syntax.node i k args
    else if k == ``Parser.Term.liftMethod && !inQuot then withFreshMacroScope do
      if inBinder then
        throwErrorAt stx "cannot lift `(<- ...)` over a binder, this error usually happens when you are trying to lift a method nested in a `fun`, `let`, or `match`-alternative, and it can often be fixed by adding a missing `do`"
      let term := args[1]!
      let term ← expandLiftMethodAux inQuot inBinder term
      -- keep name deterministic across choice branches
      let id ← mkIdentFromRef (.num baseId (← get).length)
      let auxDoElem : Syntax ← `(doElem| let $id:ident ← $term:term)
      modify fun s => s ++ [auxDoElem]
      return id
    else do
      let inAntiquot := stx.isAntiquot && !stx.isEscapedAntiquot
      let inBinder   := inBinder || (!inQuot && liftMethodForbiddenBinder stx)
      let args ← args.mapM (expandLiftMethodAux (inQuot && !inAntiquot || stx.isQuot) inBinder)
      return Syntax.node i k args
  | stx => return stx

#check Lean.Elab.Term.Do.ToCodeBlock.expandLiftMethod

def expandLiftMethod (doElem : Syntax) : TermElabM (List Syntax × Syntax) := do
  if !hasLiftMethod doElem then
    return ([], doElem)
  else
    let baseId ← withFreshMacroScope (MonadQuotation.addMacroScope `__do_lift)
    let (doElem, doElemsNew) ← (expandLiftMethodAux baseId false false doElem).run []
    return (doElemsNew, doElem)

@[term_elab «gdo»] def elabGDo : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  let bindInfo ← extractBind expectedType?
  let m ← Term.exprToSyntax bindInfo.m
  let returnType ← Term.exprToSyntax bindInfo.returnType
  let codeBlock ← Do.ToCodeBlock.run stx m returnType
  let stxNew ← liftMacroM <| Do.ToTerm.run codeBlock.code m returnType
  trace[Elab.gdo] stxNew
  withMacroExpansion stx stxNew <| elabTermEnsuringType stxNew bindInfo.expectedType
  --withMacroExpansion stx stxNew <| elabTermEnsuringType stxNew bindInfo.expectedType
end test
-/

def test_lithium (A : @Atom PROP Nat) : @Li PROP _ Bool := do
  let b ← exhale do
    let n ← atom A
    return (n == 1)
  inhale do
    let n ← atom A
    prop (b = (n == 1))
    return true

def test_lithium2 (A : @Atom PROP Nat) : @Li PROP _ Bool := do
  (exhale <|
    atom A ≫= λ n =>
    .pure (n == 1)) ≫= λ b =>
  inhale <|
    atom A ≫= λ n =>
    prop (b = (n == 1)) ≫
    .pure true

end Iris.Lithium

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std Lithium

theorem inhale_atom_with_ref_tac {α : Type _} [BI PROP] {P : PROP} (A : Atom α) (a : α) (E : Unit → PROP)
  (_h : P ∗ A.ref a ⊢ E ())
 : P ⊢ (inhaleR (atom_with_ref A a)) E := by
    simp [inhaleR, atom_with_ref]
    mysorry

@[irun_tac (inhaleR (atom_with_ref _ _)) _]
def irunInhaleAtomWithRef : IRunTacticType := fun goal => do profileitM Exception "irunInhaleAtomWithRef" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop, bi, e, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let_expr inhaleR _ _ _ L E := G | return none
  let_expr atom_with_ref _ α A a := L | return none
  let us := L.getAppFn.constLevels!
  let ident ← `(binderIdent| _)
  let goals ← IO.mkRef #[]
  let Q := Expr.beta E #[mkConst ``Unit.unit]
  let A' := mkApp4 (.const ``Atom.ref us) prop α A a
  let pf ← iCasesCore bi hyps Q q(false) A' A' ⟨⟩ (.one ident) fun hyps => do
    let m ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps, goal:=Q }
    goals.modify (·.push m.mvarId!)
    return m
  let pf := mkApp8 (.const ``inhale_atom_with_ref_tac us) prop α bi e A a E pf
  goal.assign pf
  return .some ((← goals.get).toList, [])

theorem cancel {α : Type _} [BI PROP] {p : Bool} {P P' : PROP} (A : Atom α) (a : α) {E}
  (_hP : P ⊣⊢ P' ∗ □?p A.ref a)
  (_h : P' ⊢ E a)
 : P ⊢ exhaleR (atom A) E := by
   mysorry

@[match_pattern] def mkApp11 (f a b c d e₁ e₂ e₃ e₄ e₅ e₆ e₇ : Expr) := mkApp7 (mkApp4 f a b c d) e₁ e₂ e₃ e₄ e₅ e₆ e₇

@[irun_tac exhaleR (atom _) _]
def irunExhaleAtom : IRunTacticType := fun goal => do profileitM Exception "irunExhaleAtom" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop, bi, e, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let_expr exhaleR _ _ _ L E := G | return none
  let_expr atom _ α A := L | return none
  let us := L.getAppFn.constLevels!
  let some ⟨a, P', hyps, _out, _ty, b, _, pf⟩ ←
    hyps.removeG false fun _ _ _ ty => do
      -- logInfo m!"ty: ${ty}, A: ${A}"
      let_expr Atom.ref _ _ A' a := ty | return none
      if ← isDefEq A' A then return some a else return none
    | return none
  let m ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps := hyps, goal := Expr.beta E #[a] }
  let pf := mkApp11 (.const ``cancel us) prop α bi b e P' A a E pf m
  goal.assign pf
  return .some ([m.mvarId!], [])

theorem done_tac [BI PROP] (P : PROP)
 : P ⊢ doneR := pure_intro .intro

@[irun_tac doneR]
def irunDone : IRunTacticType := fun goal => do profileitM Exception "irunDone" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop:=prop, bi:=bi, hyps:=_, e, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let .true := G.isAppOfArity ``doneR 2 | return none
  let pf := mkApp3 (.const ``done_tac G.getAppFn.constLevels!) prop bi e
  goal.assign pf
  return .some ([], [])


theorem lif_true [BI PROP] {cond} {P : PROP} (E1 E2 : PROP)
  (_h1 : cond)
  (_h2 : P ⊢ E1)
 : P ⊢ lifR cond E1 E2 :=
   by mysorry

theorem lif_false [BI PROP] {cond} {P : PROP} (E1 E2 : PROP)
  (_h1 : ¬ cond)
  (_h2 : P ⊢ E2)
 : P ⊢ lifR cond E1 E2 :=
   by mysorry

syntax "istepsolve" : tactic
macro_rules
  | `(tactic|istepsolve) => `(tactic|trivial)
--macro_rules
--  | `(tactic|istepsolve) => `(tactic|solve| simp)

@[irun_tac lifR _ _ _]
def irunLif : IRunTacticType := fun goal => do profileitM Exception "irunLif" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some { prop, bi, e, hyps, goal:=G } := parseIrisGoal? g | throwError "not in proof mode"
  let ~q(lifR $cond $E1 $E2) := G | return none

  let mcond : Q($cond) ← mkFreshExprSyntheticOpaqueMVar cond
  try
    let _ ← evalTacticAtRaw (← `(tactic|istepsolve)) mcond.mvarId!
    let m : Q($e ⊢ $E1) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps, goal := E1 }
    let pf := q(lif_true $E1 $E2 $mcond $m)
    goal.assign pf
    return .some ([m.mvarId!], [])
  catch _ => pure ()

  let mnegcond : Q(¬$cond) ← mkFreshExprSyntheticOpaqueMVar q(¬ $cond)
  try
    let _ ← evalTacticAt (← `(tactic|istepsolve)) mnegcond.mvarId!
    let m : Q($e ⊢ $E2) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps, goal := E2 }
    let pf := q(lif_false $E1 $E2 $mnegcond $m)
    goal.assign pf
    return .some ([m.mvarId!], [])
  catch _ => pure ()

  throwError "Cannot solve either side of lif"

@[irun_tac dsimpR _ _ _]
def irunSimp : IRunTacticType := fun goal => do profileitM Exception "irunSimp" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some ig := parseIrisGoal? g | throwError "not in proof mode"
  let { prop:=_, bi:=_, e:=_, hyps:=_, goal:=G } := ig

  let_expr dsimpR _ _ _ n e E := G | return none
  let n : Name ← reduceEval n
  let ⟨e_new, _⟩ ← goal.withContext (dsimpWithExt n e)
  let g' := {ig with goal := Expr.beta E #[e_new]}.toExpr
  let goal' := ← goal.replaceTargetDefEq g'
  return .some ([goal'], [])

section test
variable [BI.{u} PROP]

example (P : Nat → Atom Unit) (Q : Atom Unit) :
  ⊢ (do
      inhale (PROP:=PROP) (atom_with_ref Q ())
      inhale (atom_with_ref (P 1) ())
      inhale (atom_with_ref (P 2) ())
      exhale do
        atom (P 1)
        atom (P 2)
      exhale (atom Q)
      done).go := by
     istart
     simp [irun_preprocess]
     irun ∞


example (P G : Atom Unit) :
  ⊢ (do
      inhale (PROP := PROP) do
        atom_with_ref P ()
        atom_with_ref G ()
      exhale do
        atom G
      done).go := by
    istart
    simp [irun_preprocess]
    irun 1
    irun 1
    irun 1
    irun 1
    irun 1

--set_option profiler true in
--set_option profiler.threshold 1 in
set_option maxRecDepth 30000 in
#time example (P : Nat → @Atom PROP Unit) :
  ⊢ (List.foldl (λ G n => inhaleR (atom_with_ref (P n) ()) λ _ => G)
    (List.foldl (λ G n => exhaleR (atom (P n)) λ _ => G)
      (doneR) (
    -- List.reverse makes cancellation basically instant
    -- List.reverse
    (List.range 2)))
    (List.range 2))
:=
  by
    -- set_option trace.profiler true in
    dsimp [List.foldl, List.range, List.range.loop, List.reverse]
    istart
    --set_option trace.profiler true in
    -- set_option trace.profiler.threshold 1 in
    irun ∞

end test

end Iris.ProofMode

namespace Iris.Examples
open Lang Lithium

variable [BI.{u} PROP]

/- Proof automation begins here -/

def expr_okR := @wp PROP _

@[irun_preprocess]
def expr_ok (e : Exp) : @Li PROP _ Val := {
  run := expr_okR e
  mono' := wp_wand e
}

def nat_okR (v : Val) (E : Nat → PROP) : PROP :=
  iprop(∃ n, ⌜v = .nat n⌝ ∗ E n)

-- TODO: Make this an atom?
@[irun_preprocess]
def nat_ok (v : Val) : @Li PROP _ Nat := {
  run := nat_okR v
  mono' E1 E2 := by mysorry
}

def recv_okR (v : Val) (E : String → String → Exp → PROP) : PROP :=
  iprop(∃ f x e, ⌜v = .recv f x e⌝ ∗ E f x e)

@[irun_preprocess]
def recv_ok (v : Val) : @Li PROP _ (String × String × Exp) := {
  run E := recv_okR v λ f x e => E (f, x, e)
  mono' E1 E2 := by mysorry
}

def subst_okR (x : String) (v : Val) (e : Exp) (E : Exp → PROP) : PROP :=
  E (subst x v e)

@[irun_preprocess]
def subst_ok (x : String) (v : Val) (e : Exp) : @Li PROP _ Exp := {
  run := subst_okR x v e
  mono' E1 E2 := by
    simp [subst_okR]
    mysorry
}

@[irun]
theorem nat_okR_nat (n : Nat) (E : Nat → PROP) :
  nat_okR (.nat n) E ⊣ E n := by
  dsimp [nat_okR]
  iintro HP
  iexists _
  isplit
  · ipure_intro
    rfl
  · iassumption

@[irun]
theorem recv_okR_rec f x e (E : String → String → Exp -> PROP) :
  recv_okR (.recv f x e) E ⊣ E f x e := by
  dsimp [recv_okR]
  iintro HP
  iexists _
  iexists _
  iexists _
  isplit
  · ipure_intro
    rfl
  · iassumption

@[irun]
theorem expr_okR_val v (E : Val -> PROP) :
  expr_okR (.val v) E ⊣ E v := by mysorry

@[irun]
theorem expr_okR_plus e1 e2 :
  expr_okR (PROP:=PROP) (Exp.binop e1 .plus e2) :- do
   let n1 ← nat_ok (← expr_ok e1)
   let n2 ← nat_ok (← expr_ok e2)
   let n ← dsimp `irun_simp (n1 + n2)
   return (Val.nat n) := by mysorry

@[irun]
theorem expr_okR_minus e1 e2 :
  expr_okR (PROP:=PROP) (Exp.binop e1 .minus e2) :- do
   let n1 ← nat_ok (← expr_ok e1)
   let n2 ← nat_ok (← expr_ok e2)
   let n ← dsimp `irun_simp (n1 - n2)
   return (Val.nat n) := by mysorry

@[irun]
theorem expr_okR_eq e1 e2 :
  expr_okR (PROP:=PROP) (Exp.binop e1 .eq e2) :- do
   let n1 ← nat_ok (← expr_ok e1)
   let n2 ← nat_ok (← expr_ok e2)
   let n ← dsimp `irun_simp (if n1 == n2 then 1 else 0)
   return (Val.nat n)
   := by mysorry

@[irun]
theorem expr_okR_rec f x e (E : Val -> PROP) :
  expr_okR (.rece f x e) E ⊣ E (.recv f x e) := by mysorry

@[irun]
theorem expr_okR_app e1 e2 :
  expr_okR (PROP:=PROP) (.app e1 e2) :- do
   let v2 ← expr_ok e2
   let ⟨f, x, e'⟩ ← recv_ok (← expr_ok e1)
   let v ← expr_ok (← subst_ok f (.recv f x e') (← subst_ok x v2 e'))
   return v
  := by mysorry

@[irun]
theorem expr_okR_if e1 e2 e3 :
  expr_okR (.ife e1 e2 e3) :- (do
    let n1 ← nat_ok (← expr_ok (PROP:=PROP) e1)
    lif (n1 ≠ 0) (expr_ok e2) (expr_ok e3))
   := by mysorry


section
open Lean Elab Tactic Meta Qq BI Std ProofMode

@[irun_tac subst_okR _ _ _ _]
def irunSubst : IRunTacticType := fun goal => do profileitM Exception "irunSubst" (← getOptions) do
  let g ← instantiateMVars <| ← goal.getType
  let some ig := parseIrisGoal? g | throwError "not in proof mode"
  let { prop:=_, bi:=_, e:=_, hyps:=_, goal:=G } := ig

  let_expr subst_okR _ x v e E := G | return none
  let .lit (.strVal x) := x | return none
  let e := Reify.reify e
  let e' := (Reify.subst x v e).unreify
  let g' := {ig with goal := Expr.beta E #[e']}.toExpr
--  let ⟨g', _⟩ ← goal.withContext (dsimpWithExt `irun_simp g')
  let goal' := ← goal.replaceTargetDefEq g'
  return .some ([goal'], [])

end

example (P : Val -> @Atom PROP Unit) :
  ⊢ (do
      inhale (atom_with_ref (P (.nat 10)) ())
      let v ← expr_ok (.binop (.val (.nat 5)) .plus (.val (.nat 5)))
      exhale (atom (P v))
      done).go := by
  istart
  simp [irun_preprocess]
  irun 1
  irun 1
  irun 1
  irun 1
  irun 1
  irun 1
  irun 1
  irun 1
  irun 1


attribute [irun_simp] Nat.add_one_sub_one

-- time: ~1700ms
set_option profiler true in
--set_option profiler.threshold 1 in
#time example (P : Val -> @Atom PROP Unit) :
   ⊢ (do
        inhale (atom_with_ref (P (.nat 0)) ())
        let v ← expr_ok (.app (.val rec_fn) (.val (.nat 200)))
        exhale (atom (P v))
        done).go := by
  istart
  unfold rec_fn
  simp [irun_preprocess]
  --set_option trace.profiler true in
  --set_option trace.profiler.threshold 1 in
  --set_option diagnostics true in
  --set_option profiler true in
  irun ∞


def fn_spec (v : Val) : @Atom PROP (Val → @Li PROP _ (Val → @Li PROP _ PEmpty)) := Atom.mk λ G =>
  iprop(∀ E va,
  (Li.bind (G va) λ L' =>
   Li.bind (all Val) λ vr =>
   Li.bind (dualizing (L' vr)) λ _ =>
   Li.pure vr).run E
  -∗
  wp (.app (.val v) (.val va)) E)

def fn_spec_inex (v : Val) : @Atom PROP ((α : Type _) × (Val → @InEx PROP α) × (Val → α → @InEx PROP Unit)) :=
  Atom.mk λ ⟨_, Lpre, Lpost⟩ =>
    (fn_spec v).ref (λ va => exhale (Lpre va) >>= λ a => .pure λ vr => Li.bind (exhale (Lpost vr a)) λ _ => done)


end Iris.Examples
