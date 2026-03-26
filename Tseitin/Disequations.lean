module

public import Tseitin.Defs
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation

namespace Tseitin

public section negative

@[expose] def heavies : Tseitin →ₙ* FreeMonoid Cell :=
  lift 1 1 (.of .a) (.of .b) 1
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

lemma A_ne_B : A ≠ B := by
  intro h
  have := congr(heavies $h)
  simp [heavies, FreeMonoid.of_injective.eq_iff] at this

@[expose] def leftMost : Tseitin → Matrix (Fin 2) (Fin 2) ℤ :=
  lift !![1, 0; 0, 0] !![1, 0; 0, 0] 1 1 !![1, 0; 1, 0] ?_ ?_ ?_ ?_ ?_ ?_ ?_
where finally all_goals decide

lemma AAX_ne_AAa : A A X ≠ A A a := ne_of_apply_ne leftMost (by simp [leftMost])
lemma AAaX_ne_AAXa : A A a X ≠ A A X a := ne_of_apply_ne leftMost (by simp +decide [leftMost])

def signed : Tseitin → Matrix (Fin 3) (Fin 3) ℤ :=
  lift (-1) (-1)
    !![0, 1, 0; 0, 0, 1; 0, 0, 0]
    !![0, 1, 0; 0, 0, 1; 0, 0, 0]
    !![1, 0, 0; 0, -1, 0; 0, 0, 1] ?_ ?_ ?_ ?_ ?_ ?_ ?_
where finally all_goals decide

lemma aaA_ne_aA : a a A A ≠ a A A := ne_of_apply_ne signed (by simp +decide [signed])
lemma aaAA_ne_aAA : a a A A ≠ a A A := ne_of_apply_ne signed (by simp +decide [signed])
lemma aaX_ne_aX : a a A A X ≠ a A A X := ne_of_apply_ne signed (by simp +decide [signed])
lemma AAX_ne_AXA : A A X ≠ A X A := ne_of_apply_ne signed (by simp +decide [signed])

end negative

end Tseitin
