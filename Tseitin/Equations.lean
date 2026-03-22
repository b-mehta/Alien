module

public import Tseitin.Defs

open Tseitin

public section positive

variable {x : Tseitin}

@[simp] private lemma ac_comm' : x A a = x a A := by simp only [← Tseitin.mul_assoc, ac_comm]
@[simp] private lemma ad_comm' : x B a = x a B := by simp only [← Tseitin.mul_assoc, ad_comm]
@[simp] private lemma bc_comm' : x A b = x b A := by simp only [← Tseitin.mul_assoc, bc_comm]
@[simp] private lemma bd_comm' : x B b = x b B := by simp only [← Tseitin.mul_assoc, bd_comm]
lemma ea_swap' : x X a A = x A X := by simp only [← Tseitin.mul_assoc x, ea_swap]
lemma eb_swap' : x X b B = x B X := by simp only [← Tseitin.mul_assoc x, eb_swap]
lemma acce' : x a A A X = x a A A := by simp only [← Tseitin.mul_assoc x, acce]

macro "comm" : tactic => `(tactic|
  simp only [ac_comm, ad_comm, bc_comm, bd_comm,
             ac_comm', ad_comm', bc_comm', bd_comm', mul_assoc])

macro "create" : tactic => `(tactic| simp only [acce, acce'])
macro "move_a" : tactic => `(tactic| simp only [ea_swap, ea_swap'])
macro "move_b" : tactic => `(tactic| simp only [eb_swap, eb_swap'])
macro "move" : tactic =>   `(tactic| simp only [ea_swap, ea_swap', eb_swap, eb_swap'])

/-- This is a useful lemma because it lets us create or destroy `a` at the top. -/
lemma duplicate : a a A A A = a A A A := calc
  _ = a A A a A   := by comm
  _ = a A A X a A := by create
  _ = a A A A X   := by move_a
  _ = A a A A X   := by comm
  _ = A a A A     := by create
  _ = a A A A     := by comm

private lemma duplicate' : x a a A A A = x a A A A := by
  simp only [← Tseitin.mul_assoc x, duplicate]

macro "duplicate" : tactic => `(tactic| simp only [duplicate, duplicate'])

namespace beginner

lemma problem1 : a A A A = a a A A A := by duplicate

lemma problem2 : A A A X a = A A A X := by calc
  _ = A A X a A a       := by move
  _ = A X a A a A a     := by move
  _ = X a A a A a A a   := by move
  _ = X a a a a A A A   := by comm
  _ = X a a a A A A     := by duplicate
  _ = X a A a A a A     := by comm
  _ = A X a A a A       := by move
  _ = A A X a A         := by move
  _ = A A A X           := by move

-- We can combine multiple `move` steps:
lemma problem2_alt : A A A X a = A A A X := by calc
  _ = X a A a A a A a   := by move
  _ = X a a a a A A A   := by comm
  _ = X a a a A A A     := by duplicate
  _ = X a A a A a A     := by comm
  _ = A A A X           := by move

lemma problem3 : a a A A A = a A A A := by duplicate

lemma problem4 : a A A B A A = a b a a A A B A A := by calc
  _ = A A B a A A         := by comm
  _ = A A B a A A X       := by create
  _ = a A A B A A X       := by comm
  _ = a A A X b B a A a A := by move
  _ = a A A b B a A a A   := by create
  _ = a b a a A A B A A   := by comm

lemma problem5 : A A X A = A A A X := by calc
  _ = X a A a A A   := by move
  _ = X a a A A A   := by comm
  _ = X a a a A A A := by duplicate
  _ = X a A a A a A := by comm
  _ = A A A X       := by move

lemma problem6 : a b a a A A B A A = a A A B A A := by calc
  _ = a A A b B a A a A   := by comm
  _ = a A A X b B a A a A := by create
  _ = a A A B A A X       := by move
  _ = A A B a A A X       := by comm
  _ = A A B a A A         := by create
  _ = a A A B A A         := by comm

lemma problem7 : a b a A A A B A A A = a b a b a A A A B A A A := by calc
  _ = A A A B a b a A A A         := by comm
  _ = A A A B a b a A A X A       := by create
  _ = A a b a A A B A A X A       := by comm
  _ = A a b a A A X b B a A a A A := by move
  _ = A a b a A A b B a A a A A   := by create
  _ = a b a b A A A B a a A A A   := by comm
  _ = a b a b A A A B a A A A     := by duplicate
  _ = a b a b a A A A B A A A     := by comm

lemma problem8 : X A X b a A B = X A X A B X a := by calc
  _ = X X a A b a A B   := by move
  _ = X X a A A b B a   := by comm
  _ = X X a A A X b B a := by create
  _ = X X a A A B X a   := by move
  _ = X A X A B X a     := by move

lemma problem9 : X a A A X = A X A X X := by calc
  _ = X a A A X X := by create
  _ = A X A X X   := by move

lemma problem10 : A X a A A = A X A A X := by calc
  _ = X a A a A A   := by move
  _ = X a A A a A   := by comm
  _ = X a A A X a A := by create
  _ = A X A A X     := by move

lemma problem11 : a b a A A B A A = a b a a b a A A B A A := by calc
  _ = A A B a A A b a         := by comm
  _ = A A B a A A X b a       := by create
  _ = a A A B A A X b a       := by comm
  _ = a A A X b B a A a A b a := by move
  _ = a A A b B a A a A b a   := by create
  _ = a b a a b a A A B A A   := by comm

lemma problem12 : a A A B A A = a b a a A A B A A := by calc
  _ = A A B a A A         := by comm
  _ = A A B a A A X       := by create
  _ = a A A B A A X       := by comm
  _ = a A A X b B a A a A := by move
  _ = a A A b B a A a A   := by create
  _ = a b a a A A B A A   := by comm

end beginner

namespace intermediate

lemma problem1 : A A A X = A A X A := by calc
  _ = X a A a A a A := by move
  _ = X a a a A A A := by comm
  _ = X a a A A A   := by duplicate
  _ = X a A a A A   := by comm
  _ = A A X A       := by move

lemma problem2 : a b a b A A A B A B A A = a b a b a b a b A A A B A B A A := by calc
  _ = a b A A A B A B a A A b             := by comm
  _ = a b A A A B A B a A A X b           := by create
  _ = a b A a A A B A B A A X b           := by comm
  _ = a b A a A A X b B a A b B a A a A b := by move
  _ = a b A a A A b B a A b B a A a A b   := by create
  _ = a b a b a b a a A A A b B A B A A   := by comm
  _ = a b a b a b a A A A b B A B A A     := by duplicate
  _ = a b a b a b a b A A A B A B A A     := by comm

lemma problem3 : a a a a A A X = a a a A A X a := by calc
  _ = a a a a A A   := by create
  _ = a a a A A a   := by comm
  _ = a a a A A X a := by create

lemma problem4 : A X A A = A A X A := by calc
  _ = X a A A A := by move
  _ = X a a A A A := by duplicate
  _ = X a A a A A := by comm
  _ = A A X A := by move

lemma problem5 : A X b a A A = A X b a a A A := by calc
  _ = X a A b a A A := by move
  _ = X a b a A A A := by comm
  _ = X a b a a A A A := by duplicate
  _ = X a A b a a A A := by comm
  _ = A X b a a A A := by move

lemma problem6 : a a a a A A X = a a A A X a a := by calc
  _ = a a a a A A   := by create
  _ = a a A A a a   := by comm
  _ = a a A A X a a := by create

-- lemma example1 : A A X X = A A X := calc
--   _ = X a A a A X := by move
--   _ = X a a A A X := by comm
--   _ = X a a A A   := by create
--   _ = X a A a A   := by comm
--   _ = A A X       := by move

end intermediate

end positive
