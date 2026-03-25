module

public import Tseitin.Defs
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation

namespace Tseitin

public section negative

@[simp, expose] def liftAux {α : Type*} [Mul α] (a b A B X : α) : TseitinGen → α
  | .a' => a
  | .b' => b
  | .A' => A
  | .B' => B
  | .X' => X

@[expose] def lift {α : Type*} [Semigroup α] (a b A B X : α)
    (h1 : A * a = a * A) (h2 : A * b = b * A) (h3 : B * a = a * B) (h4 : B * b = b * B)
    (h5 : (X * a) * A = A * X) (h6 : (X * b) * B = B * X) (h7 : ((a * A) * A) * X = (a * A) * A) :
    Tseitin → α := Quot.lift (FreeSemigroup.lift (liftAux a b A B X)) fun x y h ↦ by
  apply TseitinRel.inductionOn h <;> simp +contextual [*]

@[simp] lemma lift_a {α : Type*} [Semigroup α] {a b A B X : α} {h1 h2 h3 h4 h5 h6 h7} :
    lift a b A B X h1 h2 h3 h4 h5 h6 h7 Tseitin.a = a := rfl
@[simp] lemma lift_b {α : Type*} [Semigroup α] {a b A B X : α} {h1 h2 h3 h4 h5 h6 h7} :
    lift a b A B X h1 h2 h3 h4 h5 h6 h7 Tseitin.b = b := rfl
@[simp] lemma lift_A {α : Type*} [Semigroup α] {a b A B X : α} {h1 h2 h3 h4 h5 h6 h7} :
    lift a b A B X h1 h2 h3 h4 h5 h6 h7 Tseitin.A = A := rfl
@[simp] lemma lift_B {α : Type*} [Semigroup α] {a b A B X : α} {h1 h2 h3 h4 h5 h6 h7} :
    lift a b A B X h1 h2 h3 h4 h5 h6 h7 Tseitin.B = B := rfl
@[simp] lemma lift_X {α : Type*} [Semigroup α] {a b A B X : α} {h1 h2 h3 h4 h5 h6 h7} :
    lift a b A B X h1 h2 h3 h4 h5 h6 h7 Tseitin.X = X := rfl

def heavies : Tseitin → FreeMonoid Cell :=
  lift 1 1 (.of .a) (.of .b) 1
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

lemma A_ne_B : A ≠ B := by
  intro h
  have := congr(heavies $h)
  simp [heavies] at this
  grind [FreeMonoid.of_injective]

def leftMost : Tseitin → Matrix (Fin 2) (Fin 2) ℤ :=
  lift !![1, 0; 0, 0] !![1, 0; 0, 0] 1 1 !![1, 0; 1, 0]
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by decide)

lemma AAX_ne_AAa : A A X ≠ A A a := ne_of_apply_ne leftMost (by decide)
lemma AAaX_ne_AAXa : A A a X ≠ A A X a := ne_of_apply_ne leftMost (by decide)

def signed : Tseitin → Matrix (Fin 3) (Fin 3) ℤ :=
  lift (-1) (-1) !![0, 1, 0; 0, 0, 1; 0, 0, 0] !![0, 1, 0; 0, 0, 1; 0, 0, 0]
    !![1, 0, 0; 0, -1, 0; 0, 0, 1]
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by decide)

lemma aaA_ne_aA : a a A A ≠ a A A := ne_of_apply_ne signed (by decide)
lemma aaAA_ne_aAA : a a A A ≠ a A A := ne_of_apply_ne signed (by decide)
lemma aaX_ne_aX : a a A A X ≠ a A A X := ne_of_apply_ne signed (by decide)
lemma AAX_ne_AXA : A A X ≠ A X A := ne_of_apply_ne signed (by decide)

end negative

end Tseitin
