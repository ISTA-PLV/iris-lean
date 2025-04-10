import Iris.BI
import Iris.ProofMode
import Iris.Examples.IStepAttr

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

--def profileitM (_ : Type) (_ : String) (_ : Options) (act : TacticM α) : TacticM α := act
partial def repCore (f : MVarId → TacticM (List MVarId)) (goals : List MVarId) (nsteps : Option Nat) : TacticM (Nat × List MVarId) :=
  go 0 goals
where
  go : Nat → List MVarId → TacticM (Nat × List MVarId)
  | n, [] => return (n, [])
  | n, goal::goals => do
    if nsteps = some n then
      return (n, goal::goals)
    if ← goal.isAssigned then
      go n goals
    else
      match ← observing? (f goal) with
      | some goals' => go (n+1) (goals' ++ goals)
      | none => return (n, goal::goals)

elab "rep" colGt tac:tactic : tactic => do
  let (n, goals) ← repCore (evalTacticAtRaw tac) (← getGoals) none
  IO.println s!"Did {n} steps"
  setGoals goals

elab "rep" colGt nsteps:num colGt tac:tactic : tactic => do
  let (n, goals) ← repCore (evalTacticAtRaw tac) (← getGoals) (some nsteps.getNat)
  IO.println s!"Did {n} steps"
  setGoals goals



theorem cancel [BI PROP] {p : Bool} {P P' A Q' : PROP}
  (hP : P ⊣⊢ P' ∗ □?p A)
  (h : P' ⊢ Q')
 : P ⊢ A ∗ Q' :=
   hP.1.trans <| sep_comm.1.trans <| sep_mono intuitionisticallyIf_elim h

variable {prop : Q(Type u)} (bi : Q(BI $prop)) (Q : Q($prop)) in
def cancelFast {e} (hyps : Hyps bi e)
  : MetaM (Q($e ⊢ $Q) × Expr) := do
  let ~q(iprop($A ∗ $Q')) := Q | throwError "Goal is not of the shape A ∗ G"
  let some ⟨_inst, P', hyps, out, ty, b, _, pf⟩ ←
    hyps.removeG false fun _ _ _ ty => do
      -- logInfo m!"ty: ${ty}, A: ${A}"
      if ← isDefEq ty A then return some ty else return none
    | throwError "no hyp"
  have : $ty =Q $A := ⟨⟩
  have : $out =Q iprop(□?$b $ty) := ⟨⟩
  let m : Q($P' ⊢ $Q') ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps := hyps, goal := Q' }
  return (q(cancel $pf $m), m)

elab "icancel" : tactic => do profileitM Exception "icancel" (← getOptions) do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop:=_, bi, e:=_, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let (pf, m) ← cancelFast bi goal hyps
  mvar.assign pf
  replaceMainGoal [m.mvarId!]

theorem intro_tac [BI PROP] {P A Q : PROP}
  (h : P ∗ A ⊢ Q)
 : P ⊢ A -∗ Q := wand_intro h

variable {prop : Q(Type u)} (bi : Q(BI $prop)) (Q : Q($prop)) in
def introFast {P} (hyps : Hyps bi P)
  (k : ∀ {P}, Hyps bi P → (Q : Q($prop)) → MetaM Q($P ⊢ $Q))
 : MetaM (Q($P ⊢ $Q)) := do
  let ~q(iprop($A -∗ $Q')) := Q | throwError "Goal is not of the shape A -∗ G"
  let ident ← `(binderIdent| _ )
  if A.isAppOfArity ``intuitionistically 3 then
    let ~q(iprop(□ $A')) := A | failure
    let pf ← iCasesCore bi hyps Q' q(true) A A' ⟨⟩ (.one ident) fun hyps => k hyps Q'
    return q(intro_tac (Q := $Q') $pf)
  else
    let pf ← iCasesCore bi hyps Q' q(false) A A ⟨⟩ (.one ident) fun hyps => k hyps Q'
    return q(intro_tac (Q := $Q') $pf)


elab "ifastintro" : tactic => do profileitM Exception "ifastintro" (← getOptions) do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, e := _, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let goals ← IO.mkRef #[]
  let pf ← introFast bi goal hyps fun hyps Q => do
    let m : Expr ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps, goal:=Q }
    goals.modify (·.push m.mvarId!)
    pure m

  mvar.assign pf
  replaceMainGoal (← goals.get).toList

theorem true_tac [BI PROP] {P : PROP}
 : P ⊢ True := pure_intro .intro

variable {prop : Q(Type u)} (bi : Q(BI $prop)) (Q : Q($prop)) in
def trueFast {P} (_ : Hyps bi P)
 : MetaM (Q($P ⊢ $Q)) := do
  let ~q(iprop(True)) := Q | throwError "Goal is not of the shape True"
  return q(true_tac)

elab "itrue" : tactic => do profileitM Exception "itrue" (← getOptions) do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop:=_, bi, e := _, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let pf ← trueFast bi goal hyps
  mvar.assign pf

theorem apply_bi [BI PROP] {P Q Q' : PROP}
  (h1 : Q' ⊢ Q)
  (h2 : P ⊢ Q')
 : P ⊢ Q := h2.trans h1

variable {prop : Q(Type u)} (bi : Q(BI $prop)) (Q : Q($prop)) in
def applyTac {e} {A B : Q($prop)} (hyps : Hyps bi e) (P : Q($A ⊢ $B))
 : MetaM (Q($e ⊢ $Q) × Expr) := do
  -- we need to instantiate mvars, so we use isDefEq
  let ⟨_⟩ ← assertDefEqQ Q B
  let m : Q($e ⊢ $A) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps := hyps, goal := A }
  return (q(apply_bi $P $m), m)

elab "iapply" colGt thm:term : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop:=prop, bi, e:=_, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let A : Q($prop) ← mkFreshExprMVar prop
  let B : Q($prop) ← mkFreshExprMVar prop
  let thm ← elabTerm thm none
  let typ ← inferType thm
  let ⟨args, _, conclusion⟩ ← forallMetaTelescope typ
  let .true ← isDefEq conclusion q($A ⊢ $B) | throwError "failed to match conclusion"
  let some thm ← checkTypeQ (mkAppN thm args) q($A ⊢ $B) | throwError "check type failed"


  let (pf, m) ← applyTac bi goal hyps thm
  mvar.assign pf
  -- report new goals, see https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html#deconstructing-expressions
  let newGoals ← args.filterMapM λ mvar => do
    let mvarId := mvar.mvarId!
    if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
      return some mvarId
    else
      return none

  let newGoals := newGoals.push m.mvarId!
  replaceMainGoal newGoals.toList

variable {prop : Q(Type u)} (bi : Q(BI $prop)) (Q : Q($prop)) in
partial def iAutoApplyCore {e} (hyps : Hyps bi e) (tree : DiscrTree Name) :
    MetaM (Q($e ⊢ $Q) × Expr) := do
  let Q ← instantiateExprMVars Q
  if Q.isMVar then throwError "iAutoApplyCore failed: goal has free metavars"

  -- check all top level matches, accept the first one that unifies
  let ((G' : Q($prop)), (pf : Q($G' ⊢ $Q))) ← (do
    for decl in ← tree.getMatch Q do
      try
        let info ← getConstInfo decl
        let pf := mkConst decl (← mkFreshLevelMVarsFor info)
        let (args, _, targetTy) ← forallMetaTelescopeReducing (← inferType pf)
        let .some (G', G) := (unpackEntails targetTy) | failure
        -- IO.println s!"---------------"
        -- IO.println s!"Q: {Q}"
        -- IO.println s!"G: {G}"
        -- IO.println s!"pf: {←instantiateMVars (mkAppN pf args)}"
        -- IO.println s!"isDefEq"
        let .true ← isDefEq Q G | failure
        -- IO.println s!"Q: {←instantiateMVars Q}"
        -- IO.println s!"G: {←instantiateMVars G}"
        -- IO.println s!"pf: {←instantiateMVars (mkAppN pf args)}"
        -- TODO: check that all args are instantiated
        return (G', mkAppN pf args)
      catch _ => pure () -- try the next lemma
    throwError "iautoapply failed: no lemma available")

  let m : Q($e ⊢ $G') ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps := hyps, goal := G' }
  return (q(apply_bi $pf $m), m)

elab "iautoapply" : tactic => do profileitM Exception "iautoapply" (← getOptions) do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop:=_, bi, e:=_, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let tree := istepExt.getState (← getEnv)

  let (pf, m) ← iAutoApplyCore bi goal hyps tree
  mvar.assign pf
  replaceMainGoal [m.mvarId!]

def lif [BI PROP] (cond : Prop) (P1 P2 : PROP) : PROP :=
  iprop((⌜cond⌝ -∗ P1) ∧ (⌜¬cond⌝ -∗ P2))

theorem lif_true [BI PROP] {cond} {P P1 P2 : PROP}
  (h1 : cond)
  (h2 : P ⊢ P1)
 : P ⊢ lif cond P1 P2 :=
   sorry

theorem lif_false [BI PROP] {cond} {P P1 P2 : PROP}
  (h1 : ¬ cond)
  (h2 : P ⊢ P2)
 : P ⊢ lif cond P1 P2 :=
   sorry

variable {prop : Q(Type u)} (bi : Q(BI $prop)) (Q : Q($prop)) in
def iLifCore {e} (hyps : Hyps bi e)
  : TacticM (Q($e ⊢ $Q) × Expr) := do
  let ~q(iprop(lif $cond $P1 $P2)) := Q | throwError "Goal is not of the shape lif cond P1 P2"

  let mcond : Q($cond) ← mkFreshExprSyntheticOpaqueMVar cond
  try
    let _ ← evalTacticAt (← `(tactic|solve | simp)) mcond.mvarId!
    let m : Q($e ⊢ $P1) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps, goal := P1 }
    return (q(lif_true $mcond $m), m)
  catch _ => pure ()

  let mnegcond : Q(¬$cond) ← mkFreshExprSyntheticOpaqueMVar q(¬ $cond)
  try
    let _ ← evalTacticAt (← `(tactic|solve | simp)) mnegcond.mvarId!
    let m : Q($e ⊢ $P2) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps, goal := P2 }
    return (q(lif_false $mnegcond $m), m)
  catch _ => pure ()

  throwError "Cannot solve either side of lif"

elab "ilif" : tactic => do profileitM Exception "ilif" (← getOptions) do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop:=_, bi, e:=_, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let (pf, m) ← iLifCore bi goal hyps
  mvar.assign pf
  replaceMainGoal [m.mvarId!]

syntax "istep" : tactic

macro_rules
  | `(tactic|istep) => `(tactic|icancel)
macro_rules
  | `(tactic|istep) => `(tactic|ifastintro)
macro_rules
  | `(tactic|istep) => `(tactic|itrue)
macro_rules
  | `(tactic|istep) => `(tactic|iautoapply)
macro_rules
  | `(tactic|istep) => `(tactic|ilif)

end Iris.ProofMode

namespace Iris.Examples
open Iris.BI

section lang
variable {u} [BI.{u} PROP]
def Loc : Type := Nat

inductive Binop where
| plus | minus | eq

mutual
inductive Val where
| nat : Nat -> Val
| loc : Loc -> Val
| recv : String -> String -> Expr -> Val
inductive Expr where
| val : Val -> Expr
| var : String -> Expr
| binop : Expr -> Binop -> Expr -> Expr
| rece : String -> String -> Expr -> Expr
| app : Expr -> Expr -> Expr
| ife : Expr -> Expr -> Expr -> Expr
end

def subst (x : String) (v : Val) (e : Expr) : Expr :=
  match e with
  | .val _ => e
  | .var y => if x = y then .val v else e
  | .binop e1 o e2 => .binop (subst x v e1) o (subst x v e2)
  | .rece f y e' => .rece f y (if x = f || x = y then e' else subst x v e')
  | .app e1 e2 => .app (subst x v e1) (subst x v e2)
  | .ife e1 e2 e3 => .ife (subst x v e1) (subst x v e2)  (subst x v e3)

def wp [BI PROP] (e : Expr) (P : Val -> PROP) : PROP := by sorry
def wpnat (v : Val) (P : Nat -> PROP) : PROP := iprop(∃ n, ⌜v = .nat n⌝ ∗ P n)
def wprecv (v : Val) (P : String -> String -> Expr -> PROP) : PROP := iprop(∃ f x e, ⌜v = .recv f x e⌝ ∗ P f x e)
def wpsubst (x : String) (v : Val) (e : Expr) (P : Expr -> PROP) : PROP := P (subst x v e)

@[istep]
theorem wpnat_nat (n : Nat) (P : Nat -> PROP) : P n ⊢ wpnat (.nat n) P := by
  unfold wpnat
  iintro HP
  iexists _
  isplit
  · ipure_intro
    rfl
  · iassumption

@[istep]
theorem wprecv_rec f x e (P : String -> String -> Expr -> PROP) : P f x e ⊢ wprecv (.recv f x e) P := by
  unfold wprecv
  iintro HP
  iexists _
  iexists _
  iexists _
  isplit
  · ipure_intro
    rfl
  · iassumption

@[istep]
 theorem wp_val v (P : Val -> PROP) :
  P v ⊢ wp (.val v) P := by sorry

@[istep]
theorem wp_plus e1 e2 (P : Val -> PROP) :
  (wp e1 λ v1 =>
   wp e2 λ v2 =>
   wpnat v1 λ n1 =>
   wpnat v2 λ n2 =>
   P (.nat (n1 + n2))) ⊢ wp (Expr.binop e1 .plus e2) P := by sorry

@[istep]
theorem wp_minus e1 e2 (P : Val -> PROP) :
  (wp e1 λ v1 =>
   wp e2 λ v2 =>
   wpnat v1 λ n1 =>
   wpnat v2 λ n2 =>
   P (.nat (n1 - n2))) ⊢ wp (Expr.binop e1 .minus e2) P := by sorry

@[istep]
theorem wp_eq e1 e2 (P : Val -> PROP) :
  (wp e1 λ v1 =>
   wp e2 λ v2 =>
   wpnat v1 λ n1 =>
   wpnat v2 λ n2 =>
   P (.nat (if n1 = n2 then 1 else 0))) ⊢ wp (Expr.binop e1 .eq e2) P := by sorry

@[istep]
theorem wp_rec (P : Val -> PROP) :
  (P (.recv f x e)) ⊢ wp (.rece f x e) P := by sorry

@[istep]
theorem wp_app e1 e2 (P : Val -> PROP) :
  (wp e2 λ v2 =>
   wp e1 λ v1 =>
   wprecv v1 λ f x e' =>
   wpsubst x v2 e' λ e =>
   wpsubst f (.recv f x e') e λ e =>
   wp e P) ⊢ wp (.app e1 e2) P := by sorry

@[istep]
theorem wp_if e1 e2 e3 (P : Val -> PROP) :
  (wp e1 λ v1 =>
   wpnat v1 λ n1 =>
   ProofMode.lif (n1 ≠ 0) (wp e2 P) (wp e3 P)) ⊢
  wp (.ife e1 e2 e3) P := by sorry


section
open Lean Elab Tactic Meta Qq BI Std ProofMode
elab "isubst" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop:=_, bi:=_, e:=_, hyps:=_, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let .true := goal.isAppOfArity ``wpsubst 5 | throwError "Goal is not 'wp_subst'"
  -- TODO: Do something smarter here?
  evalTactic (← `(tactic | dsimp [wpsubst, subst]))
end

macro_rules
  | `(tactic|istep) => `(tactic|isubst)

end lang

theorem exfalso {P : Prop} : P  :=
  by sorry

section
variable {u} [BI.{u} PROP]

theorem proof_cancel (P : Nat → PROP) (Q : PROP) :
  ⊢ Q -∗ P 1 -∗ P 2 -∗ P 1 ∗ P 2 ∗ Q
:= by
  iintro HQ
  repeat ifastintro
  icancel
  icancel
  iexact HQ


theorem proof_intro_custom (P G : PROP) :
  ⊢ P -∗ G -∗ G ∗ True := by
    istart
    ifastintro
    ifastintro
    icancel
    itrue

theorem proof_intro_custom_auto (P G : PROP) :
  ⊢ P -∗ G -∗ G ∗ True := by
    istart
    rep istep

theorem proof_intro_pers_auto (P G : PROP) :
  ⊢ P -∗ □ G -∗ G ∗ G ∗ True := by
    istart
    rep istep

--set_option profiler true in
#time theorem proof_intro_2 [BIAffine PROP] (P : Nat → PROP) :
  ⊢ List.foldl (λ G n => iprop((P n) -∗ G)) (P 119) (List.range 120)
:=
  -- set_option trace.profiler true in by
   by
     dsimp [List.foldl, List.range, List.range.loop] <;> (repeat iintro _) <;> iassumption


-- TODO: why does ilif sometimes take more than 1ms here if there a no lif in the goal?
--set_option profiler true in
--set_option profiler.threshold 1 in
set_option maxRecDepth 30000 in
#time theorem proof_cancel_2 (P : Nat → PROP) :
  ⊢ List.foldl (λ G n => iprop((P n) -∗ G))
    (List.foldl (λ G n => iprop(P n ∗ G)) iprop(True) (
    -- List.reverse makes cancellation basically instant
    -- List.reverse
    (List.range 100)))
    (List.range 100)
:=
  by
    dsimp [List.foldl, List.range, List.range.loop, List.reverse]
    istart
    -- set_option trace.profiler true in
    -- set_option trace.profiler.threshold 1 in
    rep istep
    -- set_option trace.profiler true in
    --  repeat' ifastintro
    -- set_option trace.profiler true in
    --   repeat' icancel
    -- itrue
    -- set_option trace.profiler true in
    -- set_option trace.profiler.output "out2.json" in
    -- set_option trace.profiler.output.pp true in
    -- repeat' icancel
    -- set_option trace.profiler true in
    -- set_option trace.profiler.output true in
    -- sleep 120
    -- iexact HQ

theorem wp_test (P : Val -> PROP) :
  P (.nat 10) ⊢ wp (Expr.binop (.val (.nat 5)) .plus (.val (.nat 5))) (λ v => iprop(P v ∗ True)) := by
  istart
  istep
  istep
  istep
  istep
  istep
  istep
  istep
  istep

def rec_fn : Val :=
  .recv "f" "x" (.ife (.binop (.var "x") .eq (.val (.nat 0))) (.val (.nat 0)) (.app (.var "f") (.binop (.var "x") .minus (.val (.nat 1)))))

--set_option profiler true in
--set_option profiler.threshold 1 in
#time theorem wp_test2 (P : Val -> PROP) :
  P (.nat 0) ⊢ wp (.app (.val rec_fn) (.val (.nat 20))) (λ v => iprop(P v ∗ True)) := by
  istart
  unfold rec_fn
  --isubst <;> iautoapply
  --set_option trace.profiler true in
  --set_option trace.profiler.threshold 1 in
  --set_option diagnostics true in
  --set_option profiler true in
  rep istep
  -- rep 300 istep
  --repeat' istep

end

end Iris.Examples
