module

public meta import Tseitin.Reify

open Tseitin

section

open Lean Meta Elab Tactic

elab "norm" : tactic => liftMetaTactic1 normTactic
elab "create" : tactic => liftMetaTactic1 createTactic
elab "delete" : tactic => liftMetaTactic1 createTactic
elab "move" : tactic => liftMetaTactic1 moveTactic

elab "norm" : conv => normConv
elab "create" : conv => createConv
elab "delete" : conv => createConv
elab "move" : conv => moveConv

simproc_decl tseitin_norm (HMul.hMul (α := Tseitin) _ _) := fun e => do
  let r ← normaliseExpr e normalise
  if r.expr == e then return .continue
  return .done r

simproc_decl tseitin_create (HMul.hMul (α := Tseitin) _ _) := fun e => do
  let r ← normaliseExpr e (simplify ∘ normalise) (some (``simplify, ``simplify_correctness))
  if r.expr == e then return .continue
  return .done r

simproc_decl tseitin_move (HMul.hMul (α := Tseitin) _ _) := fun e => do
  let r ← normaliseExpr e (moveX ∘ normalise) (some (``moveX, ``moveX_correctness))
  if r.expr == e then return .continue
  return .done r

end

example : a A b = a b A := by norm
example : a A b B = a b A B := by norm
example : a A b B = A B a b := by norm

example : a A A X = a A A := by create
example : A b a A X = b a A A := by create

example : a a A A A X = a a A A A := by create


example : X a A = A X := by move
example : B X = X b B := by move
example : B X = X B b := by move
example : X a b A B = A B X := by move
example : A X A A = X a A A A := by move
example : A X a A = A A X := by move

example : a a A A A = a A A A := by calc
  _ = a A A X a A := by create
  _ = a A A A X := by move
  _ = a A A A := by create

example : X a A A X = X a A A := by create

-- Multiple X absorptions in tail: each block absorbs its trailing X
example : X a A A X a A A X = X a a A A A A := by create
-- Tail simplification with non-matching head
example : b X a A A X = b X a A A := by create
-- Head can't merge but inner block can
example : B X a A A X = B X a A A := by create
-- Already simple, no X to absorb
example : a A A = a A A := by create
-- Deep tail: multiple non-matching heads before a simplifiable block
example : b X b X a A A X = b X b X a A A := by create

#guard_msgs (drop warning) in
example : A a A X = A A a := by
  norm
  guard_target = a A A X = a A A
  sorry

#guard_msgs (drop warning) in
example : A a A X = b := by
  create
  sorry

#guard_msgs (drop warning) in
example : A a A X = sorry := by
  simp only [tseitin_norm]
  guard_target = a A A X = _
  simp only [tseitin_create]
  guard_target = a A A = _
  sorry

#guard_msgs (drop warning) in
example : A a A X = sorry := by
  conv_lhs => norm
  guard_target = a A A X = _
  conv_lhs => create
  guard_target = a A A = _
  sorry
