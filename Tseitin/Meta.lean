module

public meta import Tseitin.Reify

open Tseitin

section

open Lean Meta Elab Tactic

elab "norm" : tactic => liftMetaTactic1 normTactic
elab "create" : tactic => liftMetaFinishingTactic createTactic
elab "delete" : tactic => liftMetaFinishingTactic createTactic
elab "move" : tactic => liftMetaFinishingTactic moveTactic

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

example : A a A X = A A a := by
  sorry
