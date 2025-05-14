/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode

namespace Iris.Examples.Lang

inductive Binder where
| anon : Binder
| str : String → Binder
deriving DecidableEq, Inhabited, Repr

instance : Coe String Binder where
  coe := Binder.str

def Loc : Type := Nat
deriving DecidableEq

inductive Binop where
| plus | minus | eq | pair
deriving DecidableEq

mutual
inductive Val where
| nat : Nat -> Val
| loc : Loc -> Val
| pair : Val -> Val -> Val
| recv : Binder -> Binder -> Exp -> Val
deriving DecidableEq
inductive Exp where
| val : Val -> Exp
| var : String -> Exp
| binop : Exp -> Binop -> Exp -> Exp
| fst : Exp -> Exp
| snd : Exp -> Exp
| rece : Binder -> Binder -> Exp -> Exp
| lete : Binder -> Exp -> Exp -> Exp
| app : Exp -> Exp -> Exp
| ife : Exp -> Exp -> Exp -> Exp
| alloc : Exp
| load : Exp -> Exp
| store : Exp -> Exp -> Exp
deriving DecidableEq
end

def subst (x : String) (v : Val) : Exp → Exp
  | .val v => .val v
  | .var y => if x == y then .val v else .var y
  | .binop e1 o e2 => .binop (subst x v e1) o (subst x v e2)
  | .fst e1 => .fst (subst x v e1)
  | .snd e1 => .snd (subst x v e1)
  | .rece f y e' => .rece f y (if .str x == f || .str x == y then e' else subst x v e')
  | .lete y e1 e2 => .lete y (subst x v e1) (if .str x == y then e2 else subst x v e2)
  | .app e1 e2 => .app (subst x v e1) (subst x v e2)
  | .ife e1 e2 e3 => .ife (subst x v e1) (subst x v e2)  (subst x v e3)
  | .alloc => .alloc
  | .load e1 => .load (subst x v e1)
  | .store e1 e2 => .store (subst x v e1) (subst x v e2)

def subst' (x : Binder) (v : Val) (e : Exp) : Exp :=
  match x with
  | .anon => e
  | .str x => subst x v e


section wp
open BI

variable {u} [BI.{u} PROP]
def wp [BI PROP] (e : Exp) (P : Val -> PROP) : PROP := by sorry

theorem wp_wand e (P1 P2 : Val -> PROP) :
  ⊢ wp e P1 -∗ (∀ v, P1 v -∗ P2 v) -∗ wp e P2
  := by sorry

end wp

namespace Reify
open Lean
inductive Exp where
| val : Expr -> Exp -- we do not need to reify values
| var : String -> Exp
| binop : Exp -> Expr -> Exp -> Exp
| fst : Exp -> Exp
| snd : Exp -> Exp
| rece : Binder -> Binder -> Exp -> Exp
| lete : Binder -> Exp -> Exp -> Exp
| app : Exp -> Exp -> Exp
| ife : Exp -> Exp -> Exp -> Exp
| alloc : Exp
| load : Exp -> Exp
| store : Exp -> Exp -> Exp
| unk : Expr -> Exp
deriving Inhabited, Repr

def Binder.unreify (b : Binder) : Expr :=
  match b with
  | Binder.anon => mkConst ``Binder.anon
  | Binder.str s => mkApp (mkConst ``Binder.str) (mkStrLit s)

-- should this be ToExpr?
def Exp.unreify : Exp → Expr
  | .val v => mkApp (mkConst ``Lang.Exp.val) v
  | .var v => mkApp (mkConst ``Lang.Exp.var) (mkStrLit v)
  | .binop e1 o e2 => mkApp3 (mkConst ``Lang.Exp.binop) (unreify e1) o (unreify e2)
  | .fst e1 => mkApp (mkConst ``Lang.Exp.fst) (unreify e1)
  | .snd e1 => mkApp (mkConst ``Lang.Exp.snd) (unreify e1)
  | .rece f x e => mkApp3 (mkConst ``Lang.Exp.rece) (Binder.unreify f) (Binder.unreify x) (unreify e)
  | .lete x e1 e2 => mkApp3 (mkConst ``Lang.Exp.lete) (Binder.unreify x) (unreify e1) (unreify e2)
  | .app e1 e2 => mkApp2 (mkConst ``Lang.Exp.app) (unreify e1) (unreify e2)
  | .ife e1 e2 e3 => mkApp3 (mkConst ``Lang.Exp.ife) (unreify e1) (unreify e2) (unreify e3)
  | .alloc => mkConst ``Lang.Exp.alloc
  | .load e1 => mkApp (mkConst ``Lang.Exp.load) (unreify e1)
  | .store e1 e2 => mkApp2 (mkConst ``Lang.Exp.store) (unreify e1) (unreify e2)
  | .unk e => e

def Binder.reify (e : Expr) : Option Binder :=
  match_expr e with
  | Binder.anon => some (.anon)
  | Binder.str s =>
    match s with
    | .lit (.strVal v) => some (.str v)
    | _ => none
  | _ => none

partial def reify (e : Expr) : Exp :=
  match_expr e with
  | Lang.Exp.val v => .val v
  | Lang.Exp.var v =>
    match v with
    | .lit (.strVal v) => .var v
    | _ => .unk e
  | Lang.Exp.binop e1 o e2 => .binop (reify e1) o (reify e2)
  | Lang.Exp.fst e1 => .fst (reify e1)
  | Lang.Exp.snd e1 => .snd (reify e1)
  | Lang.Exp.rece f x e' =>
    match Binder.reify f, Binder.reify x with
    | some f, some x => .rece f x (reify e')
    | _, _ => .unk e
  | Lang.Exp.lete x e1 e2 =>
    match Binder.reify x with
    | some x => .lete x (reify e1) (reify e2)
    | _ => .unk e
  | Lang.Exp.app e1 e2 => .app (reify e1) (reify e2)
  | Lang.Exp.ife e1 e2 e3 => .ife (reify e1) (reify e2) (reify e3)
  | Lang.Exp.alloc => .alloc
  | Lang.Exp.load e1 => .load (reify e1)
  | Lang.Exp.store e1 e2 => .store (reify e1) (reify e2)
  | _ => .unk e

def subst (x : String) (v : Expr) (e : Exp) : Exp :=
  match e with
  | .val _ => e
  | .var y => if x == y then .val v else e
  | .binop e1 o e2 => .binop (subst x v e1) o (subst x v e2)
  | .fst e1 => .fst (subst x v e1)
  | .snd e1 => .snd (subst x v e1)
  | .rece f y e' => .rece f y (if .str x == f || .str x == y then e' else subst x v e')
  | .lete y e1 e2 => .lete y (subst x v e1) (if .str x == y then e2 else subst x v e2)
  | .app e1 e2 => .app (subst x v e1) (subst x v e2)
  | .ife e1 e2 e3 => .ife (subst x v e1) (subst x v e2)  (subst x v e3)
  | .alloc => .alloc
  | .load e1 => .load (subst x v e1)
  | .store e1 e2 => .store (subst x v e1) (subst x v e2)
  | .unk e => .unk (mkApp3 (mkConst ``Lang.subst) (mkStrLit x) v e)

def subst' (x : Binder) (v : Expr) (e : Exp) : Exp :=
  match x with
  | .anon => e
  | .str x => subst x v e

end Reify

def rec_fn : Val :=
  .recv "f" "x" (.ife (.binop (.var "x") .eq (.val (.nat 0))) (.val (.nat 0)) (.app (.var "f") (.binop (.var "x") .minus (.val (.nat 1)))))
