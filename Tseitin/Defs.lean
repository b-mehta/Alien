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

@[simp] lemma Cell.asTop_a : Cell.asTop .a = .a' := rfl
@[simp] lemma Cell.asTop_b : Cell.asTop .b = .b' := rfl
@[simp] lemma Cell.asBot_a : Cell.asBot .a = .A' := rfl
@[simp] lemma Cell.asBot_b : Cell.asBot .b = .B' := rfl

end

def embed {α : Type*} : FreeSemigroup α →ₙ* FreeMonoid α := FreeSemigroup.lift .of
@[simp, grind =] lemma embed_of {α : Type*} (x : α) : embed (.of x) = .of x := by
  rw [embed, FreeSemigroup.lift_of]

lemma embed_eq_cons {α : Type*} (x : α) (xs : List α) :
    embed ⟨x, xs⟩ = FreeMonoid.ofList (x :: xs) := by
  simp only [embed, FreeSemigroup.lift, Equiv.coe_fn_mk, MulHom.coe_mk, FreeMonoid.ofList_cons]
  rw [← List.foldl_map]
  generalize FreeMonoid.of x = x
  induction xs generalizing x with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.foldl_cons, FreeMonoid.ofList_cons]
    simp [ih, mul_assoc]

lemma embed_injective {α : Type*} : Function.Injective (@embed α) := by
  rintro ⟨x, xs⟩ ⟨y, ys⟩ h
  simp only [embed_eq_cons, Equiv.apply_eq_iff_eq] at h
  simpa using h

lemma eq_one_or_embed {α : Type*} (x : FreeMonoid α) : x = 1 ∨ ∃ y, embed y = x := by
  induction x with
  | one => simp
  | of x => exact Or.inr ⟨.of x, by simp⟩
  | mul x y hx hy =>
    obtain rfl | ⟨x', hx'⟩ := hx <;>
    obtain rfl | ⟨y', hy'⟩ := hy
    · simp
    · exact Or.inr ⟨y', by simp [hy']⟩
    · exact Or.inr ⟨x', by simp [hx']⟩
    · exact Or.inr ⟨x' * y', by simp [hx', hy']⟩

open FreeMonoid in
inductive TseitinMonoidRel : FreeMonoid TseitinGen → FreeMonoid TseitinGen → Prop
  | ac_comm : TseitinMonoidRel (of A' * of a') (of a' * of A')
  | ad_comm : TseitinMonoidRel (of B' * of a') (of a' * of B')
  | bc_comm : TseitinMonoidRel (of A' * of b') (of b' * of A')
  | bd_comm : TseitinMonoidRel (of B' * of b') (of b' * of B')
  | ea_swap : TseitinMonoidRel (of X' * of a' * of A') (of A' * of X')
  | eb_swap : TseitinMonoidRel (of X' * of b' * of B') (of B' * of X')
  | acce : TseitinMonoidRel (of a' * of A' * of A' * of X') (of a' * of A' * of A')
  | lcongr (x y z : FreeMonoid TseitinGen) : TseitinMonoidRel x y → TseitinMonoidRel (x * z) (y * z)
  | rcongr (x y z : FreeMonoid TseitinGen) : TseitinMonoidRel y z → TseitinMonoidRel (x * y) (x * z)

lemma TseitinMonoidRel.ne_one {x y : FreeMonoid TseitinGen} (h : TseitinMonoidRel x y) :
    x ≠ 1 ∧ y ≠ 1 := by
  induction h with simp [← FreeMonoid.length_eq_zero, *]

@[expose] def TseitinRel : FreeSemigroup TseitinGen → FreeSemigroup TseitinGen → Prop :=
  fun x y ↦ TseitinMonoidRel (embed x) (embed y)

open FreeSemigroup in
lemma TseitinRel.inductionOn {motive : FreeSemigroup TseitinGen → FreeSemigroup TseitinGen → Prop}
    {x y : FreeSemigroup TseitinGen} (h : TseitinRel x y)
    (ac_comm : motive (of A' * of a') (of a' * of A'))
    (ad_comm : motive (of B' * of a') (of a' * of B'))
    (bc_comm : motive (of A' * of b') (of b' * of A'))
    (bd_comm : motive (of B' * of b') (of b' * of B'))
    (ea_swap : motive (of X' * of a' * of A') (of A' * of X'))
    (eb_swap : motive (of X' * of b' * of B') (of B' * of X'))
    (acce : motive (of a' * of A' * of A' * of X') (of a' * of A' * of A'))
    (lcongr : ∀ x y z : FreeSemigroup TseitinGen, motive x y → motive (x * z) (y * z))
    (rcongr : ∀ x y z : FreeSemigroup TseitinGen, motive y z → motive (x * y) (x * z)) :
    motive x y := by
  rw [TseitinRel] at h
  generalize hx' : embed x = x' at h
  generalize hy' : embed y = y' at h
  induction h generalizing x y with
  | ac_comm =>
    have hx : x = of A' * of a' := embed_injective (by simp [hx'])
    have hy : y = of a' * of A' := embed_injective (by simp [hy'])
    rwa [hx, hy]
  | ad_comm =>
    have hx : x = of B' * of a' := embed_injective (by simp [hx'])
    have hy : y = of a' * of B' := embed_injective (by simp [hy'])
    rwa [hx, hy]
  | bc_comm =>
    have hx : x = of A' * of b' := embed_injective (by simp [hx'])
    have hy : y = of b' * of A' := embed_injective (by simp [hy'])
    rwa [hx, hy]
  | bd_comm =>
    have hx : x = of B' * of b' := embed_injective (by simp [hx'])
    have hy : y = of b' * of B' := embed_injective (by simp [hy'])
    rwa [hx, hy]
  | ea_swap =>
    have hx : x = of X' * of a' * of A' := embed_injective (by simp [hx'])
    have hy : y = of A' * of X' := embed_injective (by simp [hy'])
    rwa [hx, hy]
  | eb_swap =>
    have hx : x = of X' * of b' * of B' := embed_injective (by simp [hx'])
    have hy : y = of B' * of X' := embed_injective (by simp [hy'])
    rwa [hx, hy]
  | acce =>
    have hx : x = of a' * of A' * of A' * of X' := embed_injective (by simp [hx'])
    have hy : y = of a' * of A' * of A' := embed_injective (by simp [hy'])
    rwa [hx, hy]
  | lcongr x'' y'' z'' h ih =>
    obtain rfl | ⟨x'', rfl⟩ := eq_one_or_embed x''
    · simpa using h.ne_one
    obtain rfl | ⟨y'', rfl⟩ := eq_one_or_embed y''
    · simpa using h.ne_one
    obtain rfl | ⟨z'', rfl⟩ := eq_one_or_embed z''
    · grind
    rw [← map_mul, embed_injective.eq_iff] at hx' hy'
    simp only [embed_injective.eq_iff, forall_eq_apply_imp_iff, forall_eq] at ih
    rw [hx', hy']
    exact lcongr _ _ _ ih
  | rcongr x'' y'' z'' h ih =>
    obtain rfl | ⟨y'', rfl⟩ := eq_one_or_embed y''
    · simpa using h.ne_one
    obtain rfl | ⟨z'', rfl⟩ := eq_one_or_embed z''
    · simpa using h.ne_one
    obtain rfl | ⟨x'', rfl⟩ := eq_one_or_embed x''
    · grind
    rw [← map_mul, embed_injective.eq_iff] at hx' hy'
    simp only [embed_injective.eq_iff, forall_eq_apply_imp_iff, forall_eq] at ih
    rw [hx', hy']
    exact rcongr _ _ _ ih

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
    | `($z $args*) => `($z $args* $y)
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
