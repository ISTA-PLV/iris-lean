/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Lean
import Iris.BI
import Iris.ProofMode

namespace Iris.ProofMode
open Lean Elab.Tactic Meta Qq BI

structure PartitionHyps {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop)) where
  (espatial : Q($prop)) (hypsspatial : Hyps bi espatial)
  (eintuit : Q($prop)) (hypsintuit : Hyps bi eintuit)
  (pf : Q($e ⊣⊢ $espatial ∗ □ $eintuit))
  deriving Inhabited

-- TODO: use the following similar to Hyps.split?
inductive PartitionHypsCore {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop)) where
  | none
  | spatial
  | intuit
  | main (_ : PartitionHyps bi e)

theorem partition_mk_emp [BI PROP] :
    emp (PROP:=PROP) ⊣⊢ emp ∗ □ emp :=
  sorry

theorem partition_mk_intuit [BI PROP] {P : PROP} :
    □ P ⊣⊢ emp ∗ □ □ P :=
  sorry

theorem partition_mk_spatial [BI PROP] {P : PROP} :
    P ⊣⊢ P ∗ □ emp :=
  sorry

theorem partition_mk_merge [BI PROP] {P Ps Pi Q Qs Qi : PROP}
  (hP : P ⊣⊢ Ps ∗ □ Pi)
  (hQ : Q ⊣⊢ Qs ∗ □ Qi) :
    P ∗ Q ⊣⊢ (Ps ∗ Qs) ∗ □ (Pi ∗ Qi) :=
  sorry

variable  {prop : Q(Type u)} (bi : Q(BI $prop)) in
def Hyps.partition : ∀ {e}, Hyps bi e → PartitionHyps bi e
  | _, .emp _ => ⟨_, .mkEmp bi, _, .mkEmp bi, q(partition_mk_emp)⟩
  | e, h@(.hyp _ _ _ p ty _) =>
   match matchBool p with
   | .inl _ =>
        have : $e =Q iprop(□ $ty) := ⟨⟩
        ⟨_, .mkEmp bi, _, h, q(partition_mk_intuit)⟩
   | .inr _ =>
        ⟨_, h, _, .mkEmp bi, q(partition_mk_spatial)⟩
  | _, .sep _ _ _ _ lhs rhs =>
    let ⟨_, spatl, _, intuitl, pfl⟩ := lhs.partition
    let ⟨_, spatr, _, intuitr, pfr⟩ := rhs.partition
    ⟨_, .mkSep spatl spatr, _, .mkSep intuitl intuitr, q(partition_mk_merge $pfl $pfr)⟩
end Iris.ProofMode


namespace Iris.Lithium

open Lean Qq Tactic Meta Iris.BI Iris.ProofMode

@[match_pattern] def mkApp11 (f a b c d e₁ e₂ e₃ e₄ e₅ e₆ e₇ : Expr) := mkApp7 (mkApp4 f a b c d) e₁ e₂ e₃ e₄ e₅ e₆ e₇

-- this avoids the warnings from sorry
axiom exfalso (P : Prop) : P
syntax "mysorry" : tactic
macro_rules
--| `(tactic|mysorry) => `(tactic|sorry)
| `(tactic|mysorry) => `(tactic|apply exfalso)


section simp
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

end simp


section IrisGoalShallow

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

end IrisGoalShallow
