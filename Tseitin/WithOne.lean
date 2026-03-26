module

public import Mathlib.Algebra.PresentedMonoid.Basic
public import Mathlib.Algebra.Group.WithOne.Basic
public import Tseitin.Defs

section

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop} {x y : FreeMonoid α}

lemma PresentedMonoid.mk_eq_mk_of_conGen (h : conGen rels x y) : mk rels x = mk rels y :=
  Quotient.sound h

lemma PresentedMonoid.mk_eq_mk_of_rel (h : rels x y) : mk rels x = mk rels y :=
  mk_eq_mk_of_conGen (.of _ _ h)

end

namespace Tseitin

open TseitinGen PresentedMonoid

def forward : PresentedMonoid TseitinMonoidRel →* WithOne Tseitin :=
  PresentedMonoid.lift ((↑) ∘ mk) fun a b h ↦ by
  induction h with
  | ac_comm => simp [← WithOne.coe_mul]
  | ad_comm => simp [← WithOne.coe_mul]
  | bc_comm => simp [← WithOne.coe_mul]
  | bd_comm => simp [← WithOne.coe_mul]
  | ea_swap => simp [← WithOne.coe_mul, ea_swap]
  | eb_swap => simp [← WithOne.coe_mul, eb_swap]
  | acce => simp [← WithOne.coe_mul, acce]
  | lcongr x y z h ih => simp [ih]
  | rcongr x y z h ih => simp [ih]

@[simp] lemma forward_of {x : TseitinGen} : forward (of _ x) = (mk x : Tseitin) := by simp [forward]

def backwardAux : Tseitin →ₙ* PresentedMonoid TseitinMonoidRel :=
  Tseitin.lift
    (of _ a') (of _ b') (of _ A') (of _ B') (of _ X')
    (mk_eq_mk_of_rel .ac_comm) (mk_eq_mk_of_rel .bc_comm)
    (mk_eq_mk_of_rel .ad_comm) (mk_eq_mk_of_rel .bd_comm)
    (mk_eq_mk_of_rel .ea_swap) (mk_eq_mk_of_rel .eb_swap)
    (mk_eq_mk_of_rel .acce)

@[simp] lemma backwardAux_mk {x : TseitinGen} : backwardAux (mk x) = of _ x := by
  cases x <;> simp [backwardAux]

@[to_additive (attr := simp)]
public theorem _root_.WithOne.lift_symm_apply {α β : Type*} [Semigroup α] [Monoid β]
    (F : WithOne α →* β) (x : α) :
  WithOne.lift.symm F x = F x := rfl

def backward : WithOne Tseitin →* PresentedMonoid TseitinMonoidRel := WithOne.lift backwardAux

@[simp] lemma backward_coe_mk {x : TseitinGen} : backward (mk x) = of _ x := by simp [backward]

lemma forward_comp_backward : forward.comp backward = MonoidHom.id _ := by
  apply WithOne.lift.symm.injective
  ext x
  simp [backward_coe_mk]

lemma backward_comp_forward : backward.comp forward = MonoidHom.id _ := by
  ext (_ | _ | _ | _ | _) <;> simp [forward, backward, backwardAux]

public def equiv : PresentedMonoid TseitinMonoidRel ≃* WithOne Tseitin where
  toMulHom := forward
  invFun := backward
  left_inv := DFunLike.congr_fun backward_comp_forward
  right_inv := DFunLike.congr_fun forward_comp_backward

end Tseitin
