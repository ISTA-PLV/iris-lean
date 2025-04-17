/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode

namespace Iris.Examples.Lang
open BI

variable {u} [BI.{u} PROP]

def Loc : Type := Nat

inductive Binop where
| plus | minus | eq

mutual
inductive Val where
| nat : Nat -> Val
| loc : Loc -> Val
| recv : String -> String -> Exp -> Val
inductive Exp where
| val : Val -> Exp
| var : String -> Exp
| binop : Exp -> Binop -> Exp -> Exp
| rece : String -> String -> Exp -> Exp
| app : Exp -> Exp -> Exp
| ife : Exp -> Exp -> Exp -> Exp
end

def subst (x : String) (v : Val) : Exp → Exp
  | .val v => .val v
  | .var y => if x == y then .val v else .var y
  | .binop e1 o e2 => .binop (subst x v e1) o (subst x v e2)
  | .rece f y e' => .rece f y (if x == f || x == y then e' else subst x v e')
  | .app e1 e2 => .app (subst x v e1) (subst x v e2)
  | .ife e1 e2 e3 => .ife (subst x v e1) (subst x v e2)  (subst x v e3)

def wp [BI PROP] (e : Exp) (P : Val -> PROP) : PROP := by sorry

namespace Reify
open Lean
inductive Exp where
| val : Expr -> Exp -- we do not need to reify values
| var : String -> Exp
| binop : Exp -> Expr -> Exp -> Exp
| rece : String -> String -> Exp -> Exp
| app : Exp -> Exp -> Exp
| ife : Exp -> Exp -> Exp -> Exp
| unk : Expr -> Exp
deriving Inhabited, Repr

-- should this be ToExpr?
def Exp.unreify : Exp → Expr
  | .val v => mkApp (mkConst ``Lang.Exp.val) v
  | .var v => mkApp (mkConst ``Lang.Exp.var) (mkStrLit v)
  | .binop e1 o e2 => mkApp3 (mkConst ``Lang.Exp.binop) (unreify e1) o (unreify e2)
  | .rece f x e => mkApp3 (mkConst ``Lang.Exp.rece) (mkStrLit f) (mkStrLit x) (unreify e)
  | .app e1 e2 => mkApp2 (mkConst ``Lang.Exp.app) (unreify e1) (unreify e2)
  | .ife e1 e2 e3 => mkApp3 (mkConst ``Lang.Exp.ife) (unreify e1) (unreify e2) (unreify e3)
  | .unk e => e

partial def reify (e : Expr) : Exp :=
  match_expr e with
  | Lang.Exp.val v => .val v
  | Lang.Exp.var v =>
    match v with
    | .lit (.strVal v) => .var v
    | _ => .unk e
  | Lang.Exp.binop e1 o e2 => .binop (reify e1) o (reify e2)
  | Lang.Exp.rece f x e' =>
    match f, x with
    | .lit (.strVal f), .lit (.strVal x) => .rece f x (reify e')
    | _, _ => .unk e'
  | Lang.Exp.app e1 e2 => .app (reify e1) (reify e2)
  | Lang.Exp.ife e1 e2 e3 => .ife (reify e1) (reify e2) (reify e3)
  | _ => .unk e

def subst (x : String) (v : Expr) (e : Exp) : Exp :=
  match e with
  | .val _ => e
  | .var y => if x == y then .val v else e
  | .binop e1 o e2 => .binop (subst x v e1) o (subst x v e2)
  | .rece f y e' => .rece f y (if x == f || x == y then e' else subst x v e')
  | .app e1 e2 => .app (subst x v e1) (subst x v e2)
  | .ife e1 e2 e3 => .ife (subst x v e1) (subst x v e2)  (subst x v e3)
  | .unk e => .unk (mkApp3 (mkConst ``Lang.subst) (mkStrLit x) v e)

end Reify

def rec_fn : Val :=
  .recv "f" "x" (.ife (.binop (.var "x") .eq (.val (.nat 0))) (.val (.nat 0)) (.app (.var "f") (.binop (.var "x") .minus (.val (.nat 1)))))
