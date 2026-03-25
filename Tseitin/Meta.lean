module

public meta import Tseitin.Reify

open Tseitin

open Lean Meta Elab Tactic in
elab "tseitin_norm" : tactic => liftMetaFinishingTactic Tseitin.normTactic

open Lean Meta Elab Tactic in
elab "create" : tactic => liftMetaFinishingTactic createTactic

example : a A b = a b A := by tseitin_norm
example : a A b B = a b A B := by tseitin_norm
example : a A b B = A B a b := by tseitin_norm

example : a A A X = a A A := by create
example : A b a A X = b a A A := by create

example : a a A A A X = a a A A A := by create
