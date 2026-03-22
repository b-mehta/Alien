module

public import Mathlib.Data.Quot
public import Mathlib.Algebra.Group.Defs

import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation

public section

inductive TseitinGen | a' | b' | A' | B' | X' | mul (x y : TseitinGen)

open TseitinGen

inductive TseitinRel : TseitinGen → TseitinGen → Prop
  | ac_comm : TseitinRel (A'.mul a') (a'.mul A')
  | ad_comm : TseitinRel (B'.mul a') (a'.mul B')
  | bc_comm : TseitinRel (A'.mul b') (b'.mul A')
  | bd_comm : TseitinRel (B'.mul b') (b'.mul B')
  | ea_swap : TseitinRel ((X'.mul a').mul A') (A'.mul X')
  | eb_swap : TseitinRel ((X'.mul b').mul B') (B'.mul X')
  | acce : TseitinRel (((a'.mul A').mul A').mul X') ((a'.mul A').mul A')
  | assoc (x y z : TseitinGen) : TseitinRel (x.mul (y.mul z)) ((x.mul y).mul z)
  | lcongr (x y z : TseitinGen) : TseitinRel x y → TseitinRel (x.mul z) (y.mul z)
  | rcongr (x y z : TseitinGen) : TseitinRel y z → TseitinRel (x.mul y) (x.mul z)

@[expose] public def Tseitin : Type := Quot TseitinRel

namespace Tseitin

@[expose, match_pattern] def a : Tseitin := Quot.mk _ a'
@[expose, match_pattern] def b : Tseitin := Quot.mk _ b'
@[expose, match_pattern] def A : Tseitin := Quot.mk _ A'
@[expose, match_pattern] def B : Tseitin := Quot.mk _ B'
@[expose, match_pattern] def X : Tseitin := Quot.mk _ X'

@[expose] def mk : TseitinGen → Tseitin := Quot.mk _

@[expose] def mul : Tseitin → Tseitin → Tseitin :=
    .map₂ TseitinGen.mul .rcongr .lcongr

lemma mul_assoc' (x y z : Tseitin) : mul x (mul y z) = mul (mul x y) z := by
  induction x, y, z using Quot.induction_on₃ with
  | h a b c => exact Quot.sound (.assoc _ _ _)

@[expose] instance : Semigroup Tseitin where
  mul := Tseitin.mul
  mul_assoc _ _ _ := (mul_assoc' _ _ _).symm

lemma mk_mul_mk {x y : TseitinGen} : mk x * mk y = mk (x.mul y) := rfl

instance : CoeFun Tseitin (fun _ ↦ Tseitin → Tseitin) where
  coe x := mul x

@[app_unexpander Tseitin.mul]
meta def unexpandTseitinMul : Lean.PrettyPrinter.Unexpander
  | `($_mul $x $y) => `($x $y)
  | _ => throw ()

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
