/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode
import Iris.Lithium.Base
import Iris.Lithium.Islaris.Base

namespace Islaris
open Lean Elab Meta

structure BitVecN where
  fromBitVec ::
  size : Nat
  toBitVec : BitVec size
deriving Inhabited, DecidableEq, Repr, ToExpr

instance : CoeOut (BitVec n) BitVecN where
   coe := BitVecN.fromBitVec n

-- TODO: Is this a good idea?
delab_rule BitVecN.fromBitVec
| `($_ $_ $b) => `($b)

abbrev VarName := Nat
abbrev SailName := String

inductive Accessor where
| field (_ : SailName)
deriving Inhabited, DecidableEq, Repr, ToExpr

inductive BvArith where
| bvnand
| bvnor
| bvxnor
| bvsub
| bvudiv
| bvudivi
| bvsdiv
| bvsdivi
| bvurem
| bvsrem
| bvsmod
| bvshl
| bvlshr
| bvashr
deriving Inhabited, DecidableEq, Repr, ToExpr

inductive BvComp where
| bvult
| bvslt
| bvule
| bvsle
| bvuge
| bvsge
| bvugt
| bvsgt
deriving Inhabited, DecidableEq, Repr, ToExpr

inductive BvManyArith where
| bvand
| bvor
| bvxor
| bvadd
| bvmul
deriving Inhabited, DecidableEq, Repr, ToExpr

abbrev AccessorList := List Accessor

inductive Unop where
| not
| bvnot
| bvredand
| bvredor
| bvneg
| extract (_ : Nat) (_ : Nat)
| zeroExtend (_ : Nat)
| signExtend (_ : Nat)
deriving Inhabited, DecidableEq, Repr, ToExpr

inductive Binop where
| eq
| bvArith (_ : BvArith)
| bvComp (_ : BvComp)
deriving Inhabited, DecidableEq, Repr, ToExpr

inductive Manyop where
| and
| or
| bvManyArith (_ : BvManyArith)
| concat
deriving Inhabited, DecidableEq, Repr, ToExpr

inductive BaseVal where
| symbolic (_ : VarName)
| bool (_ : Bool)
| bits (_ : BitVecN)
| enum (_ : SailName)
deriving Inhabited, DecidableEq, Repr, ToExpr

inductive AssumeVal where
| var (_ : SailName) (_ : AccessorList)
| bool (_ : Bool)
| bits (_ : BitVecN)
| enum (_ : SailName)
deriving Inhabited, DecidableEq, Repr, ToExpr

inductive Ty where
| bool
| bitVec (_ : Nat)
| enum (_ : SailName)
| array (_ : Ty) (_ : Ty)
deriving Inhabited, DecidableEq, Repr, ToExpr

inductive Exp where
| val (_ : BaseVal)
| unop (_ : Unop) (_ : Exp)
| binop (_ : Binop) (_ : Exp) (_ : Exp)
| manyop (_ : Manyop) (_ : List Exp)
| ite (_ : Exp) (_ : Exp) (_ : Exp)
deriving Inhabited, Repr, ToExpr

inductive Valu where
| base (_ : BaseVal)
| i (_ : Int) (_ : Int)
| string (_ : String)
| unit
| vector (_ : List Valu)
| list (_ : List Valu)
| struct (_: List (SailName × Valu))
| constructor (_ : SailName) (_ : Valu)
| poison
deriving Inhabited, Repr, ToExpr

inductive AExp where
| val (_ : AssumeVal)
| unop (_ : Unop) (_ : AExp)
| binop (_ : Binop) (_ : AExp) (_ : AExp)
| manyop (_ : Manyop) (_ : List AExp)
| ite (_ : AExp) (_ : AExp) (_ : AExp)
deriving Inhabited, Repr, ToExpr

inductive Smt where
| declareConst (_ : VarName) (_ : Ty)
| defineConst (_ : VarName) (_ : Exp)
| assert (_ : Exp)
| defineEnum (_ : SailName) (_ : Nat) (_ : List SailName)
deriving Inhabited, Repr, ToExpr

abbrev ArgList := List Valu

abbrev TagValue := Option Valu

inductive Segment where
| segment (_ : SailName) (_ : Nat) (_ : VarName) -- The segment's original name, its size in bits, the SMT variable

inductive Event where
 | smt (_ : Smt)
 | branch (_ : Int) (_ : String) -- (*r Sail trace fork *)
 | readReg (_ : SailName) (_ : AccessorList) (_ : Valu) -- (*r read value `valu` from register `name` *)
 | writeReg (_ : SailName) (_ : AccessorList) (_ : Valu) -- (*r write value `valu` to register `name` *)
 | readMem (_ : Valu) (rkind : Valu) (addr : Valu) (numBytes : Nat) (_ : TagValue) -- (*r read value `valu` from memory address `addr`, with read kind `rkind`, byte width `byte\_width`, and `tag\_value` is the optional capability tag *)
 | writeMem (_ : Valu) (wkind : Valu) (addr : Valu) (data : Valu) (numBytes : Nat) (_ : TagValue) -- (*r write value `valu` to memory address `addr`, with write kind `wkind`, byte width `num\_bytes`, `tag\_value` is the optional capability tag, and success flag `vvar` *)
 | branchAddress (addr : Valu) -- (*r announce branch address `addr`, to induce ctrl dependency in the concurrency model *)
 | barrier (bkind : Valu) -- (*r memory barrier of kind `bkind` *)
 | cacheOp (ckind : Valu) (addr : Valu) -- (*r cache maintenance effect of kind `ckind`, at address `addr`, for data-cache clean etc. *)
 | markReg (_ : SailName) (_ : String) -- (*r instrumentation to tell concurrency model to ignore certain dependencies (TODO: support marking multiple registers). Currently the str is ignore-edge or ignore-write *)
 | cycle -- (*r instruction boundary *)
 | instr (opcode : Valu) -- (*r records the instruction `opcode` that was fetched *)
 | sleeping (_ : VarName) -- (*r Arm sleeping predicate *)
 | wakeRequest -- (*r Arm wake request *)
 | sleepRequest -- (*r Arm sleep request *)
 | call (_ : SailName) -- (*r Calls an abstract function *)
 | return (_ : SailName) -- (*r Returns from an abstract function *)
 | assumeReg (_ : SailName) (_ : AccessorList) (_ : Valu) -- (*r Notes a register assumption that Isla has been configured to use *)
 | assume (_ : AExp) -- (*r Notes a constraint that Isla has been configured to assume *)
 | funAssume (_ : SailName) (_ : Valu) (_ : ArgList) -- (*r Notes that the user has supplied a precondition for a particular function *)
 | useFunAssume (_ : SailName) (_ : Valu) (_ : ArgList) -- (*r A use of a pre-declared function assumption *)
 | abstractCall (_ : SailName) (_ : Valu) (_ : ArgList) -- (*r A function call that Isla has abstract *)
 | abstractPrimop (_ : SailName) (_ : Valu) (_ : ArgList) -- (*r A primitive operation that Isla treats as abstract *).
deriving Inhabited, Repr, ToExpr

-- The following definitions are part of isla-lang, but not used by islaris
inductive InstructionSegments where
| segments (_ : List Segment)

abbrev trc := List Event

mutual
inductive MaybeFork where
| cases (_ : String) (_ : List TreeTrc)
| end
inductive TreeTrc where
| treeTrace (_ : List Event) (_ : MaybeFork)
end

abbrev trcs := List (List Event)

inductive WholeTree where
| bareTree (_ : TreeTrc)
| treeWithSegments (_ : InstructionSegments) (_ : TreeTrc)

-- end of isla-lang here

inductive IslaTrace where
| nil
| cons (e : Event) (t : IslaTrace)
| cases (ts : List IslaTrace)
deriving Inhabited, Repr, ToExpr


section substitution

def substBaseVal (v : BaseVal) (x : VarName) : BaseVal → BaseVal
| .symbolic v' => if v' = x then v else .symbolic v'
| v => v

def substExp (v : BaseVal) (x : VarName) : Exp → Exp
| .val v' => .val (substBaseVal v x v')
| .unop op e => .unop op (substExp v x e)
| .binop op e1 e2 => .binop op (substExp v x e1) (substExp v x e2)
| .manyop op es => .manyop op (es.map (substExp v x))
| .ite e1 e2 e3 => .ite (substExp v x e1) (substExp v x e2) (substExp v x e3)

def substSmt (v : BaseVal) (x : VarName) : Smt → Smt
| .declareConst va ty => .declareConst va ty
| .defineConst va e => .defineConst va (substExp v x e)
| .assert e => .assert (substExp v x e)
| .defineEnum n i ns => .defineEnum n i ns

mutual
def substValu (v : BaseVal) (x : VarName) : Valu → Valu
| .base v' => .base (substBaseVal v x v')
| .i n m => .i n m
| .string s => .string s
| .unit => .unit
| .vector vs => .vector (vs.map (substValu v x))
| .list vs => .list (vs.map (substValu v x))
| .struct vs => .struct (vs.map (substStructElem v x))
| .constructor n v' => .constructor n (substValu v x v')
| .poison => .poison
def substStructElem (v : BaseVal) (x : VarName) : (String × Valu) → (String × Valu)
| (s1, s2) => (s1, substValu v x s2)
end

def substEvent (v : BaseVal) (x : VarName) : Event → Event
| .smt s => .smt (substSmt v x s)
| .branch i s => .branch i s
| .readReg n ac v' => .readReg n ac (substValu v x v')
| .writeReg n ac v' => .writeReg n ac (substValu v x v')
| .readMem v' rkind addr nb tag => .readMem (substValu v x v') (substValu v x rkind) (substValu v x addr) nb (tag.map (substValu v x))
| .writeMem v' wkind addr data nb tag => .writeMem (substValu v x v') (substValu v x wkind) (substValu v x addr) (substValu v x data) nb (tag.map (substValu v x))
| .branchAddress addr => .branchAddress (substValu v x addr)
| .barrier bkind => .barrier (substValu v x bkind)
| .cacheOp ckind addr => .cacheOp (substValu v x ckind) (substValu v x addr)
| .markReg n s => .markReg n s
| .cycle => .cycle
| .instr opcode => .instr (substValu v x opcode)
| .sleeping v' => .sleeping v'
| .wakeRequest => .wakeRequest
| .sleepRequest => .sleepRequest
| .call n => .call n
| .return n => .return n
| .assumeReg n ac v' => .assumeReg n ac  (substValu v x v')
| .assume e => .assume e
| .funAssume n v' a => .funAssume n (substValu v x v') a
| .useFunAssume n v' a => .useFunAssume n (substValu v x v') a
| .abstractCall n v' a => .abstractCall n (substValu v x v') a
| .abstractPrimop n v' a => .abstractPrimop n (substValu v x v') a


def substTrace (v : BaseVal) (x : VarName) : IslaTrace → IslaTrace
  | .nil => .nil
  | .cons e t' => .cons (substEvent v x e) (substTrace v x t')
  | .cases ts => .cases (ts.map (substTrace v x))

end substitution




declare_syntax_cat isla_name
syntax "isla_name(" isla_name ")" : term
syntax "|" ident "|" : isla_name

macro_rules
| `(isla_name(| $i:ident |)) => `($(Syntax.mkStrLit i.getId.toString):str)

#check isla_name(|x|)

declare_syntax_cat isla_var
syntax "isla_var(" isla_var ")" : term
syntax ident : isla_var

macro_rules
| `(isla_var( $v:ident )) => do
    let v := v.getId.toString
    if !v.startsWith "v" then Macro.throwUnsupported
    let .some n := (v.drop 1).toNat? | Macro.throwUnsupported
    return Syntax.mkNatLit n

open Parser

declare_syntax_cat isla_bv
syntax "isla_bv(" isla_bv ")" : term
-- this should parse "(_ bv2 4)"
syntax "(" "_" ident num ")" : isla_bv
syntax "(" "_" &"bv" "-" num num ")" : isla_bv
syntax "#" ident  : isla_bv

macro_rules
-- TODO: These should maybe return _I instead of bv? I do not understand that part of isla lang
| `(isla_bv((_ $n:ident $w:num) )) => do
    let w := Syntax.mkNatLit w.getNat
-- see https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/parsing.20keyword.20followed.20by.20number.20without.20whitespace/with/518267698
    let s := n.getId.toString
    if !s.startsWith "bv" then Macro.throwUnsupported
    let s' := s.drop 2
    let .some n := s'.toNat? | Macro.throwUnsupported
    let n := Syntax.mkNatLit n
    `(BitVecN.fromBitVec _ (BitVec.ofNat $w $n))
| `(isla_bv((_ bv-$n:num $w:num) )) => do
    let w := Syntax.mkNatLit w.getNat
    let n := Syntax.mkNatLit n.getNat
    `(BitVecN.fromBitVec _ (BitVec.ofInt $w (- $n)))
| `(isla_bv(# $i)) => do
    let s := i.getId.toString
    let bits ← if s.startsWith "x" then
        .pure 4
      else if s.startsWith "b" then
        .pure 1
      else Macro.throwUnsupported
    let w := Syntax.mkNatLit ((s.length - 1) * bits) -- -1 to drop x
    let .some n := Syntax.decodeNatLitVal? ("0" ++ s) | Macro.throwUnsupported
    let n := Syntax.mkNatLit n
    `(BitVecN.fromBitVec _ (BitVec.ofNat $w $n))

#check isla_bv(#x0000000000000000)

declare_syntax_cat isla_ty
syntax "isla_ty(" isla_ty ")" : term

syntax ident : isla_ty
syntax "(" "_" &"BitVec" num ")" : isla_ty
syntax isla_name : isla_ty
syntax "(" &"Array" isla_ty isla_ty ")" : isla_ty

macro_rules
| `(isla_ty(Bool)) => `(Ty.bool)
| `(isla_ty((_ BitVec $n))) => `(Ty.bitVec $(Syntax.mkNatLit n.getNat))
| `(isla_ty($n:isla_name)) => `(Ty.enum isla_name($n))
| `(isla_ty((Array $ty1 $ty2))) => `(Ty.array isla_ty($ty1) isla_ty($ty2))

declare_syntax_cat isla_base_val
syntax "isla_base_val(" isla_base_val ")" : term

syntax isla_var : isla_base_val
syntax isla_bv : isla_base_val
syntax isla_name : isla_base_val

macro_rules
| `(isla_base_val(false)) => `(BaseVal.bool false)
| `(isla_base_val(true)) => `(BaseVal.bool true)
| `(isla_base_val($i:isla_var)) => `(BaseVal.symbolic isla_var($i))
| `(isla_base_val($i:isla_bv)) => `(BaseVal.bits isla_bv($i))
| `(isla_base_val($i:isla_name)) => `(BaseVal.enum isla_name($i))

#check isla_base_val(v2)
#check isla_base_val(false)

declare_syntax_cat isla_accessor
syntax "isla_accessor(" isla_accessor ")" : term

syntax "(" "_" ppSpace &"field" ppSpace isla_name ")" : isla_accessor

macro_rules
| `(isla_accessor((_ field $n))) => `(Accessor.field isla_name($n))

declare_syntax_cat isla_accessor_list
syntax "isla_accessor_list(" isla_accessor_list ")" : term

syntax ident : isla_accessor_list
syntax "(" isla_accessor* ")" : isla_accessor_list

macro_rules
| `(isla_accessor_list(nil)) => `([])
| `(isla_accessor_list(( $ac:isla_accessor* ))) => `([ $[isla_accessor($ac)],* ])

declare_syntax_cat isla_assume_val
syntax "isla_assume_val(" isla_assume_val ")" : term

syntax "(" isla_name isla_accessor_list ")" : isla_assume_val
syntax ident : isla_assume_val
syntax isla_bv : isla_assume_val
syntax isla_name : isla_assume_val

macro_rules
| `(isla_assume_val(($i:isla_name $ac))) => `(AssumeVal.var isla_name($i) isla_accessor_list($ac))
| `(isla_assume_val(false)) => `(AssumeVal.bool false)
| `(isla_assume_val(true)) => `(AssumeVal.bool true)
| `(isla_assume_val($i:isla_bv)) => `(AssumeVal.bits isla_bv($i))
| `(isla_assume_val($i:isla_name)) => `(AssumeVal.enum isla_name($i))

declare_syntax_cat isla_exp
syntax "isla_exp(" isla_exp ")" : term

syntax isla_base_val : isla_exp
syntax "(" ident isla_exp* ")" : isla_exp
syntax "(" "=" isla_exp* ")" : isla_exp
syntax "(" "(" "_" ident num ")" isla_exp ")" : isla_exp
syntax "(" "(" "_" ident num num ")" isla_exp ")" : isla_exp

macro_rules
| `(isla_exp($i:isla_base_val)) => `(Exp.val isla_base_val($i))
| `(isla_exp((not $e))) => `(Exp.unop Unop.not isla_exp($e))
| `(isla_exp((bvnot $e))) => `(Exp.unop Unop.bvnot isla_exp($e))
| `(isla_exp((bvredand $e))) => `(Exp.unop Unop.bvredand isla_exp($e))
| `(isla_exp((bvredor $e))) => `(Exp.unop Unop.bvredor isla_exp($e))
| `(isla_exp((bvneg $e))) => `(Exp.unop Unop.bvneg isla_exp($e))
| `(isla_exp(((_ extract $n $m) $e))) => `(Exp.unop (Unop.extract $n $m) isla_exp($e))
| `(isla_exp(((_ zero_extend $n) $e))) => `(Exp.unop (Unop.zeroExtend $n) isla_exp($e))
| `(isla_exp(((_ sign_extend $n) $e))) => `(Exp.unop (Unop.signExtend $n) isla_exp($e))
| `(isla_exp((= $e1 $e2))) => `(Exp.binop Binop.eq isla_exp($e1) isla_exp($e2))

| `(isla_exp((bvnand $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvnand) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvnor $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvnor) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvxnor $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvxnor) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvsub $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvsub) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvudiv $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvudiv) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvudiv_i $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvudiv_i) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvsdiv $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvsdiv) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvsdiv_i $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvsdiv_i) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvurem $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvurem) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvsrem $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvsrem) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvsmod $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvsmod) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvshl $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvshl) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvlshr $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvlshr) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvashr $e1 $e2))) => `(Exp.binop (Binop.bvArith BvArith.bvashr) isla_exp($e1) isla_exp($e2))

| `(isla_exp((bvult $e1 $e2))) => `(Exp.binop (Binop.bvComp BvComp.bvult) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvslt $e1 $e2))) => `(Exp.binop (Binop.bvComp BvComp.bvslt) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvule $e1 $e2))) => `(Exp.binop (Binop.bvComp BvComp.bvule) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvsle $e1 $e2))) => `(Exp.binop (Binop.bvComp BvComp.bvsle) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvuge $e1 $e2))) => `(Exp.binop (Binop.bvComp BvComp.bvuge) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvsge $e1 $e2))) => `(Exp.binop (Binop.bvComp BvComp.bvsge) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvugt $e1 $e2))) => `(Exp.binop (Binop.bvComp BvComp.bvugt) isla_exp($e1) isla_exp($e2))
| `(isla_exp((bvsgt $e1 $e2))) => `(Exp.binop (Binop.bvComp BvComp.bvsgt) isla_exp($e1) isla_exp($e2))

| `(isla_exp((and $e*))) => `(Exp.manyop Manyop.and [ $[isla_exp($e)],* ])
| `(isla_exp((or $e*))) => `(Exp.manyop Manyop.or [ $[isla_exp($e)],* ])
| `(isla_exp((bvand $e*))) => `(Exp.manyop (Manyop.bvManyArith BvManyArith.bvand) [ $[isla_exp($e)],* ])
| `(isla_exp((bvor $e*))) => `(Exp.manyop (Manyop.bvManyArith BvManyArith.bvor) [ $[isla_exp($e)],* ])
| `(isla_exp((bvxor $e*))) => `(Exp.manyop (Manyop.bvManyArith BvManyArith.bvxor) [ $[isla_exp($e)],* ])
| `(isla_exp((bvadd $e*))) => `(Exp.manyop (Manyop.bvManyArith BvManyArith.bvadd) [ $[isla_exp($e)],* ])
| `(isla_exp((bvmul $e*))) => `(Exp.manyop (Manyop.bvManyArith BvManyArith.bvmul) [ $[isla_exp($e)],* ])
| `(isla_exp((concat $e*))) => `(Exp.manyop Manyop.concat [ $[isla_exp($e)],* ])

| `(isla_exp((ite $e1 $e2 $e3))) => `(Exp.ite isla_exp($e1) isla_exp($e2) isla_exp($e3) )

#check isla_exp((bvlshr #x1 #x2))

declare_syntax_cat isla_aexp
syntax "isla_aexp(" isla_aexp ")" : term

syntax isla_assume_val : isla_aexp
syntax "(" "=" isla_aexp* ")" : isla_aexp
syntax "(" ident isla_aexp* ")" : isla_aexp
syntax "(" "(" "_" ident num ")" isla_aexp ")" : isla_aexp
syntax "(" "(" "_" ident num num ")" isla_aexp ")" : isla_aexp

macro_rules
| `(isla_aexp($i:isla_assume_val)) => `(AExp.val isla_assume_val($i))
| `(isla_aexp((not $e))) => `(AExp.unop Unop.not isla_aexp($e))
| `(isla_aexp((bvnot $e))) => `(AExp.unop Unop.bvnot isla_aexp($e))
| `(isla_aexp((bvredand $e))) => `(AExp.unop Unop.bvredand isla_aexp($e))
| `(isla_aexp((bvredor $e))) => `(AExp.unop Unop.bvredor isla_aexp($e))
| `(isla_aexp((bvneg $e))) => `(AExp.unop Unop.bvneg isla_aexp($e))
| `(isla_aexp(((_ extract $n $m) $e))) => `(AExp.unop (Unop.extract $n $m) isla_aexp($e))
| `(isla_aexp(((_ zero_extend $n) $e))) => `(AExp.unop (Unop.zeroExtend $n) isla_aexp($e))
| `(isla_aexp(((_ sign_extend $n) $e))) => `(AExp.unop (Unop.signExtend $n) isla_aexp($e))
| `(isla_aexp((= $e1 $e2))) => `(AExp.binop Binop.eq isla_aexp($e1) isla_aexp($e2))

| `(isla_aexp((bvnand $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvnand) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvnor $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvnor) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvxnor $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvxnor) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvsub $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvsub) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvudiv $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvudiv) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvudiv_i $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvudiv_i) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvsdiv $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvsdiv) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvsdiv_i $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvsdiv_i) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvurem $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvurem) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvsrem $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvsrem) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvsmod $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvsmod) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvshl $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvshl) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvlshr $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvlshr) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvashr $e1 $e2))) => `(AExp.binop (Binop.bvArith BvArith.bvashr) isla_aexp($e1) isla_aexp($e2))

| `(isla_aexp((bvult $e1 $e2))) => `(AExp.binop (Binop.bvComp BvComp.bvult) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvslt $e1 $e2))) => `(AExp.binop (Binop.bvComp BvComp.bvslt) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvule $e1 $e2))) => `(AExp.binop (Binop.bvComp BvComp.bvule) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvsle $e1 $e2))) => `(AExp.binop (Binop.bvComp BvComp.bvsle) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvuge $e1 $e2))) => `(AExp.binop (Binop.bvComp BvComp.bvuge) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvsge $e1 $e2))) => `(AExp.binop (Binop.bvComp BvComp.bvsge) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvugt $e1 $e2))) => `(AExp.binop (Binop.bvComp BvComp.bvugt) isla_aexp($e1) isla_aexp($e2))
| `(isla_aexp((bvsgt $e1 $e2))) => `(AExp.binop (Binop.bvComp BvComp.bvsgt) isla_aexp($e1) isla_aexp($e2))

| `(isla_aexp((and $e*))) => `(AExp.manyop Manyop.and [ $[isla_aexp($e)],* ])
| `(isla_aexp((or $e*))) => `(AExp.manyop Manyop.or [ $[isla_aexp($e)],* ])
| `(isla_aexp((bvand $e*))) => `(AExp.manyop (Manyop.bvManyArith BvManyArith.bvand) [ $[isla_aexp($e)],* ])
| `(isla_aexp((bvor $e*))) => `(AExp.manyop (Manyop.bvManyArith BvManyArith.bvor) [ $[isla_aexp($e)],* ])
| `(isla_aexp((bvxor $e*))) => `(AExp.manyop (Manyop.bvManyArith BvManyArith.bvxor) [ $[isla_aexp($e)],* ])
| `(isla_aexp((bvadd $e*))) => `(AExp.manyop (Manyop.bvManyArith BvManyArith.bvadd) [ $[isla_aexp($e)],* ])
| `(isla_aexp((bvmul $e*))) => `(AExp.manyop (Manyop.bvManyArith BvManyArith.bvmul) [ $[isla_aexp($e)],* ])
| `(isla_aexp((concat $e*))) => `(AExp.manyop Manyop.concat [ $[isla_aexp($e)],* ])
| `(isla_aexp((ite $e1 $e2 $e3))) => `(AExp.ite isla_aexp($e1) isla_aexp($e2) isla_aexp($e3) )

declare_syntax_cat isla_smt
syntax "isla_smt(" isla_smt ")" : term

syntax "(declare-const" ws isla_var ws isla_ty ")" : isla_smt
syntax "(define-const" ws isla_var ws isla_exp ")" : isla_smt
syntax "(assert" ws isla_exp ")" : isla_smt
syntax "(define-enum" ws isla_name ws num ws "(" isla_name* ")" ")" : isla_smt

macro_rules
| `(isla_smt((declare-const $v $ty))) => `(Smt.declareConst isla_var($v) isla_ty($ty))
| `(isla_smt((define-const $v $e))) => `(Smt.defineConst isla_var($v) isla_exp($e))
| `(isla_smt((assert $e))) => `(Smt.assert isla_exp($e))
| `(isla_smt((define-enum $n $i ( $names* )))) => `(Smt.defineEnum isla_name($n) $(Syntax.mkNatLit i.getNat) [ $[isla_name($names)],* ] )
  -- | `(isla_smt| (define-enum $n $i ( $names* ))) => do
  --   let n ← elabIslaName n
  --   let i := mkNatLit i.getNat
  --   let names ← names.mapM elabIslaName
  --   mkAppM ``Smt.defineEnum #[n, i, ← mkListLit (mkConst ``SailName) names.toList]
--  | _ => throwUnsupportedSyntax

declare_syntax_cat isla_valu
syntax "isla_valu(" isla_valu ")" : term

syntax isla_base_val : isla_valu
syntax str : isla_valu
syntax "(" "_" &"unit" ")" : isla_valu
syntax "(" "_" &"vec" isla_valu* ")" : isla_valu
syntax "(" "_" &"vec" &"nil" ")" : isla_valu
syntax "(" "_" &"list" isla_valu* ")" : isla_valu
syntax "(" "_" &"list" &"nil" ")" : isla_valu
syntax "(" "_" &"struct" ("(" isla_name isla_valu ")")* ")" : isla_valu
syntax "(" isla_name isla_valu ")" : isla_valu
syntax "(" "_" &"poison" ")" : isla_valu

macro_rules
| `(isla_valu($i:isla_base_val)) => `(Valu.base isla_base_val($i))
| `(isla_valu($s:str)) => `(Valu.string $s)
| `(isla_valu((_ struct $[($n $v)]* ))) => `(Valu.struct [ $[(isla_name($n), isla_valu($v))],* ])
| `(isla_valu(($n:isla_name $v:isla_valu))) => `(Valu.constructor isla_name($n) isla_valu($v))
| `(isla_valu((_ unit))) => `(Valu.unit)
| `(isla_valu((_ poison))) => `(Valu.poison)

declare_syntax_cat isla_arg_list
syntax "isla_arg_list(" isla_arg_list ")" : term

syntax isla_valu* : isla_arg_list

macro_rules
| `(isla_arg_list(nil)) => `([])
| `(isla_arg_list($v:isla_valu*)) => `([$[isla_valu($v)],*])


declare_syntax_cat isla_tag_value
syntax "isla_tag_value(" isla_tag_value ")" : term

syntax (ppSpace isla_valu)?  : isla_tag_value

macro_rules
| `(isla_tag_value()) => `(Option.none)
| `(isla_tag_value($v:isla_valu)) => `(Option.some isla_valu($v))


declare_syntax_cat isla_event
syntax "isla_event(" isla_event ")" : term

syntax isla_smt : isla_event
syntax "(branch" ws num ws str ")" : isla_event
syntax "(read-reg" ws isla_name ws isla_accessor_list ws isla_valu ")" : isla_event
syntax "(write-reg" ws isla_name ws isla_accessor_list ws isla_valu ")" : isla_event
syntax "(read-mem" ws isla_valu ws isla_valu ws isla_valu ws num isla_tag_value ")" : isla_event
syntax "(write-mem" ws isla_valu ws isla_valu ws isla_valu ws isla_valu ws num isla_tag_value ")" : isla_event
syntax "(branch-address" ws isla_valu ")" : isla_event
syntax "(mark-reg" isla_name str ")" : isla_event
syntax "(cycle)" : isla_event
syntax "(assume-reg" ws isla_name ws isla_accessor_list ws isla_valu ")" : isla_event
syntax "(assume" ws isla_aexp ")" : isla_event
syntax "(abstract-primop" ws isla_name ws isla_valu ws isla_arg_list ")" : isla_event

macro_rules
| `(isla_event($s:isla_smt)) => `(Event.smt isla_smt($s))
| `(isla_event((branch $n $s))) => `(Event.branch $n $s )
| `(isla_event((read-reg $n $ac $v:isla_valu))) => `(Event.readReg isla_name($n) isla_accessor_list($ac) isla_valu($v))
| `(isla_event((write-reg $n $ac $v:isla_valu))) => `(Event.writeReg isla_name($n) isla_accessor_list($ac) isla_valu($v))
| `(isla_event((read-mem $v $rkind $addr $n $tag))) => `(Event.readMem isla_valu($v) isla_valu($rkind) isla_valu($addr) $n isla_tag_value($tag))
| `(isla_event((write-mem $v $rkind $addr $data $n $tag))) => `(Event.writeMem isla_valu($v) isla_valu($rkind) isla_valu($addr) isla_valu($data) $n isla_tag_value($tag))
| `(isla_event((branch-address $v))) => `(Event.branchAddress isla_valu($v))
| `(isla_event((mark-reg $n $s))) => `(Event.markReg isla_name($n) $s)
| `(isla_event((cycle))) => `(Event.cycle)
| `(isla_event((assume-reg $n $ac $v:isla_valu))) => `(Event.assumeReg isla_name($n) isla_accessor_list($ac) isla_valu($v))
| `(isla_event((assume $e))) => `(Event.assume isla_aexp($e))
| `(isla_event((abstract-primop $n $v $a))) => `(Event.abstractPrimop isla_name($n) isla_valu($v) isla_arg_list($a))


declare_syntax_cat isla
syntax "isla(" isla ")" : term

declare_syntax_cat isla_trace_elem

-- --def untilNewlineFn : ParserFn := takeUntilFn (fun c => c = '\n')
-- def untilNewlineFn : ParserFn := takeUntilFn (fun c => true)

-- def untilNewline : Parser where
--   info := epsilonInfo
--   fn   := untilNewlineFn

-- open Parser

-- open Lean.PrettyPrinter
-- open Lean.PrettyPrinter.Parenthesizer
-- open Lean.PrettyPrinter.Formatter

-- @[combinator_parenthesizer untilNewline] def untilNewline.parenthesizer : Parenthesizer := pure ()
-- @[combinator_formatter untilNewline] def untilNewline.formatter (p : Formatter) : Formatter := p

-- initialize register_parser_alias "untilNewline" untilNewline

-- declare_syntax_cat isla_comment
-- syntax ";" untilNewline : isla_comment
--syntax isla_comment : isla_trace_elem


syntax isla_event : isla_trace_elem
syntax "(cases" ws str ws isla* ")" : isla_trace_elem
syntax "(trace" ws (ppLine isla_trace_elem)* ")" : isla

macro_rules
| `(isla((trace ))) => `(IslaTrace.nil)
| `(isla((trace $i:isla_event $es*))) => `(IslaTrace.cons isla_event($i) isla((trace $es*)))
| `(isla((trace (cases $_ $[$ts]*) )) ) => `(IslaTrace.cases [ $[isla($ts)],* ])


section preprocess

open Lean Elab Term Meta Iris.Lithium

@[isla_preprocess]
def ignored_regs : List String := [
-- aarch64
  "SEE",
  "BTypeNext",
  "__currentInstrLength",
  "__PC_changed",
  "__unconditional",
  "__v81_implemented",
  "__v82_implemented",
  "__v83_implemented",
  "__v84_implemented",
  "__v85_implemented",
  "__trickbox_enabled",
  "__CNTControlBase",
  "__defaultRAM",
  "__monomorphize_reads",
  "__monomorphize_writes",
  "__isla_vector_gpr",
  "__highest_el_aarch32",
-- riscv64
  "nextPC",
]

partial def islaPreprocessEventFilter (e : Expr) : MetaM Bool :=
  match_expr e with
  | Event.assumeReg n _ _ => do
    let .lit (.strVal n) := n | return true
    return n ∉ ignored_regs
  | Event.readReg n _ _ => do
    let .lit (.strVal n) := n | return true
    return n ∉ ignored_regs
  | Event.writeReg n _ _ => do
    let .lit (.strVal n) := n | return true
    return n ∉ ignored_regs
  | Event.cycle => return false
  | Event.markReg _ _ => return false
  | Event.smt e' =>
    match_expr e' with
    | Smt.defineEnum _ _ _ => return false
    | _ => return true
  | _ => return true

partial def islaPreprocess (e : Expr) : MetaM Expr :=
  match_expr e with
  | IslaTrace.nil => return e
  | IslaTrace.cons ev t' => do
    let t' ← islaPreprocess t'
    if ← islaPreprocessEventFilter ev then
      return e.modifyApp1 t'
    else
      return t'
  | IslaTrace.cases ts => do
    let some ts ← ts.mapMListLit islaPreprocess
      | throwError "islaPreprocess: cannot do prepocess in {e}"
    return mkApp (mkConst ``IslaTrace.cases) ts
  | _ => throwError "islaPreprocess: cannot do prepocess in {e}"


syntax (name:=isla_elab) "isla%" ("?")? isla : term

@[term_elab isla_elab]
def islaElab : TermElab := λ stx ty => do
  let e ← elabTerm (←`(isla($(⟨stx[2]⟩)))) ty
  let e' ← islaPreprocess e
  if !stx[1][0].isMissing then logInfo m!"{e'}"
  return e'
