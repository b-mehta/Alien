module

public import Mathlib.Data.Quot
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Free
public import Mathlib.Algebra.FreeMonoid.Basic

import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation

public section

inductive TseitinGen | a' | b' | A' | B' | X'
  deriving Repr, DecidableEq

open TseitinGen

section

inductive Cell | a | b deriving Repr, DecidableEq

@[expose] def Cell.asTop : Cell → TseitinGen
  | .a => .a'
  | .b => .b'

@[expose] def Cell.asBot : Cell → TseitinGen
  | .a => .A'
  | .b => .B'

end

def embed {α : Type*} : FreeSemigroup α →ₙ* FreeMonoid α := FreeSemigroup.lift .of

open FreeMonoid in
inductive TseitinMonoidRel : FreeMonoid TseitinGen → FreeMonoid TseitinGen → Prop
  | ac_comm : TseitinMonoidRel (of A' * of a') (of a' * of A')
  | ad_comm : TseitinMonoidRel (of B' * of a') (of a' * of B')
  | bc_comm : TseitinMonoidRel (of A' * of b') (of b' * of A')
  | bd_comm : TseitinMonoidRel (of B' * of b') (of b' * of B')
  | ea_swap : TseitinMonoidRel ((of X' * of a') * of A') (of A' * of X')
  | eb_swap : TseitinMonoidRel ((of X' * of b') * of B') (of B' * of X')
  | acce : TseitinMonoidRel (((of a' * of A') * of A') * of X') ((of a' * of A') * of A')
  | lcongr (x y z : FreeMonoid TseitinGen) : TseitinMonoidRel x y → TseitinMonoidRel (x * z) (y * z)
  | rcongr (x y z : FreeMonoid TseitinGen) : TseitinMonoidRel y z → TseitinMonoidRel (x * y) (x * z)

def TseitinRel : FreeSemigroup TseitinGen → FreeSemigroup TseitinGen → Prop :=
  fun x y ↦ TseitinMonoidRel (embed x) (embed y)

@[expose] public def Tseitin : Type := Quot TseitinRel

namespace Tseitin

open FreeSemigroup

@[expose] def mk : TseitinGen → Tseitin := Quot.mk _ ∘ of

@[expose, match_pattern] def a : Tseitin := mk a'
@[expose, match_pattern] def b : Tseitin := mk b'
@[expose, match_pattern] def A : Tseitin := mk A'
@[expose, match_pattern] def B : Tseitin := mk B'
@[expose, match_pattern] def X : Tseitin := mk X'

@[simp] lemma mk_a' : mk a' = a := rfl
@[simp] lemma mk_b' : mk b' = b := rfl
@[simp] lemma mk_A' : mk A' = A := rfl
@[simp] lemma mk_B' : mk B' = B := rfl
@[simp] lemma mk_X' : mk X' = X := rfl

@[expose] def mul : Tseitin → Tseitin → Tseitin :=
    .map₂ (· * ·)
    (fun _ _ _ h ↦ by simpa [TseitinRel] using h.rcongr _ _ _)
    (fun _ _ _ h ↦ by simpa [TseitinRel] using h.lcongr _ _ _)

lemma mul_assoc' (x y z : Tseitin) : mul x (mul y z) = mul (mul x y) z := by
  induction x, y, z using Quot.induction_on₃ with
  | h a b c => exact congrArg _ (mul_assoc _ _ _).symm

@[expose] instance : Semigroup Tseitin where
  mul := Tseitin.mul
  mul_assoc _ _ _ := (mul_assoc' _ _ _).symm

instance : CoeFun Tseitin (fun _ ↦ Tseitin → Tseitin) where
  coe x := HMul.hMul x

section Delab

open Lean PrettyPrinter Delaborator SubExpr

@[app_delab HMul.hMul]
meta def delabTseitinHMul : Delab :=
  whenPPOption getPPCoercions <|
  withOverApp 6 do
    let α ← withNaryArg 0 getExpr
    guard <| α.isConstOf ``Tseitin
    let x ← withNaryArg 4 delab
    let y ← withNaryArg 5 delab
    match x with
    | `($f $args*) => `($f $args* $y)
    | _ => `($x $y)

end Delab

variable (x y z : Tseitin)

@[simp] lemma mul_assoc (x y z : Tseitin) : x (y z) = x y z := mul_assoc' _ _ _
@[simp] lemma ac_comm : A a = a A := Quot.sound .ac_comm
@[simp] lemma ad_comm : B a = a B := Quot.sound .ad_comm
@[simp] lemma bc_comm : A b = b A := Quot.sound .bc_comm
@[simp] lemma bd_comm : B b = b B := Quot.sound .bd_comm
lemma ea_swap : X a A = A X := Quot.sound .ea_swap
lemma eb_swap : X b B = B X := Quot.sound .eb_swap
lemma acce : a A A X = a A A := Quot.sound .acce

end Tseitin

end
