module

public import Tseitin.Defs
meta import Tseitin.Defs
public import Mathlib.Algebra.Group.WithOne.Defs

namespace Tseitin
open TseitinGen

set_option linter.style.setOption false
set_option pp.coercions false

public structure Compressed : Type where
  headTop : List Cell
  headBot : List Cell
  tail : List (List Cell × List Cell)

open Compressed

@[simp] def mapPair (a b : List Cell) : List TseitinGen := a.map Cell.asTop ++ b.map Cell.asBot

def Compressed.toList : Compressed → List TseitinGen
  | ⟨hT, hB, []⟩ => mapPair hT hB
  | ⟨hT, hB, (top, bot) :: tail⟩ =>
    mapPair hT hB ++ .X' :: Compressed.toList ⟨top, bot, tail⟩

@[grind .] lemma toList_ne_empty_of_top {a b c} (ha : a ≠ []) : toList ⟨a, b, c⟩ ≠ [] := by
  cases c
  · simp [toList, *]
  · rw [toList]; simp

@[grind .] lemma toList_ne_empty_of_bot {a b c} (hb : b ≠ []) : toList ⟨a, b, c⟩ ≠ [] := by
  cases c
  · simp [toList, *]
  · rw [toList]; simp

@[grind .] lemma toList_ne_empty_of_tail {a b c} (hc : c ≠ []) : toList ⟨a, b, c⟩ ≠ [] := by
  cases c
  · simp_all
  · rw [toList]; simp

def denote : List TseitinGen → Tseitin
  | [] => X
  | x :: xs => xs.foldl (init := mk x) (fun acc g => acc * mk g)


private lemma foldl_mul_left (a b : Tseitin) (l : List TseitinGen) :
    l.foldl (init := a * b) (fun acc g => acc * mk g) =
    a * l.foldl (init := b) (fun acc g => acc * mk g) := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons, _root_.mul_assoc, ih]

@[simp] lemma denote_cons_cons (x y : TseitinGen) (l : List TseitinGen) :
    denote (x :: y :: l) = mk x * denote (y :: l) :=
  foldl_mul_left (mk x) (mk y) l

lemma denote_cons {x} {l : List TseitinGen} (h : l ≠ []) :
    denote (x :: l) = mk x * denote l :=
  match l, h with | _ :: _, _ => denote_cons_cons ..

@[simp] lemma toList_cons_top (c : Cell) (hT : List Cell) (hB : List Cell)
    (tl : List (List Cell × List Cell)) :
    toList ⟨c :: hT, hB, tl⟩ = Cell.asTop c :: toList ⟨hT, hB, tl⟩ := by
  rcases tl with _ | ⟨⟨top, bot⟩, tl⟩ <;>
    simp only [Compressed.toList, mapPair, List.map_cons, List.cons_append]

@[simp] lemma toList_nil_nil_cons (hT hB : List Cell) (tl : List (List Cell × List Cell)) :
    toList ⟨[], [], (hT, hB) :: tl⟩ = X' :: toList ⟨hT, hB, tl⟩ := by
  simp [toList]

lemma top_bot_comm (t c : Cell) :
    mk (Cell.asTop t) * mk (Cell.asBot c) = mk (Cell.asBot c) * mk (Cell.asTop t) := by
  rcases t <;> rcases c
  exacts [ac_comm.symm, ad_comm.symm, bc_comm.symm, bd_comm.symm]

private lemma mk_mul_comm_denote (t c : Cell) (l : List TseitinGen) :
    mk (Cell.asTop t) * denote (Cell.asBot c :: l) =
    mk (Cell.asBot c) * denote (Cell.asTop t :: l) := by
  cases l with
  | nil => exact top_bot_comm t c
  | cons _ _ => simp [denote_cons_cons, mul_assoc, top_bot_comm t c]

lemma denote_bot_comm_tops (c : Cell) (tops : List Cell) (rest : List TseitinGen) :
    denote (tops.map Cell.asTop ++ Cell.asBot c :: rest) =
    denote (Cell.asBot c :: tops.map Cell.asTop ++ rest) := by
  induction tops with
  | nil => rfl
  | cons t tops' ih =>
    simp only [List.map_cons, List.cons_append]
    conv_lhs => rw [denote_cons (by simp), ih]
    conv_rhs => rw [denote_cons (List.cons_ne_nil _ _)]
    exact mk_mul_comm_denote t c _

@[simp] private lemma denote_toList_cons_bot (c : Cell) (hT hB : List Cell)
    (tl : List (List Cell × List Cell)) :
    denote (toList ⟨hT, c :: hB, tl⟩) = denote (Cell.asBot c :: toList ⟨hT, hB, tl⟩) := by
  rcases tl with _ | ⟨⟨t, b⟩, rest⟩ <;>
    simp only [Compressed.toList, mapPair, List.map_cons, List.cons_append, List.append_assoc] <;>
    exact denote_bot_comm_tops c hT _

meta def normalise : List TseitinGen → Compressed :=
  List.foldr (init := ⟨[], [], []⟩) <| fun
  | .X', ⟨hT, hB, xs⟩ => ⟨[], [], (hT, hB) :: xs⟩
  | .a', ⟨hT, hB, xs⟩ => ⟨.a :: hT, hB, xs⟩
  | .b', ⟨hT, hB, xs⟩ => ⟨.b :: hT, hB, xs⟩
  | .A', ⟨hT, hB, xs⟩ => ⟨hT, .a :: hB, xs⟩
  | .B', ⟨hT, hB, xs⟩ => ⟨hT, .b :: hB, xs⟩

@[simp] lemma normalise_nil : normalise [] = ⟨[], [], []⟩ := rfl
@[simp] lemma normalise_X_cons {l} :
  normalise (.X' :: l) =
    ⟨[], [], ((normalise l).headTop, (normalise l).headBot) :: (normalise l).tail⟩ := rfl
@[simp] lemma normalise_a_cons {l} :
  normalise (.a' :: l) =
    ⟨.a :: (normalise l).headTop, (normalise l).headBot, (normalise l).tail⟩ := rfl
@[simp] lemma normalise_b_cons {l} :
  normalise (.b' :: l) =
    ⟨.b :: (normalise l).headTop, (normalise l).headBot, (normalise l).tail⟩ := rfl
@[simp] lemma normalise_A_cons {l} :
  normalise (.A' :: l) =
    ⟨(normalise l).headTop, .a :: (normalise l).headBot, (normalise l).tail⟩ := rfl
@[simp] lemma normalise_B_cons {l} :
  normalise (.B' :: l) =
    ⟨(normalise l).headTop, .b :: (normalise l).headBot, (normalise l).tail⟩ := rfl

@[simp] lemma normalise_cons_ne_empty {l} : ∀ {x}, (normalise (x :: l)).toList ≠ []
  | .X' => toList_ne_empty_of_tail (by simp)
  | .a' => toList_ne_empty_of_top (by simp)
  | .b' => toList_ne_empty_of_top (by simp)
  | .A' => toList_ne_empty_of_bot (by simp)
  | .B' => toList_ne_empty_of_bot (by simp)

theorem normalise_correctness :
    ∀ {l : List TseitinGen}, denote (normalise l).toList = denote l := by
  intro l
  induction l with
  | nil => simp [toList]
  | cons x l ih =>
    cases l with
    | nil => cases x <;> simp [toList, Cell.asTop, Cell.asBot]
    | cons y l' =>
      cases x <;> simp [denote_cons normalise_cons_ne_empty, ih, Cell.asTop, Cell.asBot]

private meta def simplifyAux (hT hB : List Cell) :
    List (List Cell × List Cell) → Compressed
  | [] => ⟨hT, hB, []⟩
  | (top, bot) :: tl =>
    if [.a].isSuffixOf hT && [.a, .a].isSuffixOf hB then
      simplifyAux (hT ++ top) (hB ++ bot) tl
    else ⟨hT, hB, (top, bot) :: tl⟩

meta def simplify (c : Compressed) : Compressed :=
  simplifyAux c.headTop c.headBot c.tail

lemma simplify_correctness : ∀ c, denote (simplify c).toList = denote c.toList := sorry

open Lean Meta in
meta partial def reify (e : Expr) : MetaM (List TseitinGen) := do
  match_expr e with
  | HMul.hMul _ _ _ _ x y => return (← reify x) ++ (← reify y)
  | Tseitin.a => return [.a']
  | Tseitin.b => return [.b']
  | Tseitin.A => return [.A']
  | Tseitin.B => return [.B']
  | Tseitin.X => return [.X']
  | _ => throwError "reify: unexpected Tseitin expression {e}"

open Lean in
meta instance : ToExpr TseitinGen where
  toExpr
    | .a' => mkConst ``TseitinGen.a'
    | .b' => mkConst ``TseitinGen.b'
    | .A' => mkConst ``TseitinGen.A'
    | .B' => mkConst ``TseitinGen.B'
    | .X' => mkConst ``TseitinGen.X'
  toTypeExpr := mkConst ``TseitinGen

private meta def Compressed.beq : Compressed → Compressed → Bool
  | ⟨hT₁, hB₁, []⟩, ⟨hT₂, hB₂, []⟩ => hT₁ == hT₂ && hB₁ == hB₂
  | ⟨hT₁, hB₁, (t₁, b₁) :: tl₁⟩, ⟨hT₂, hB₂, (t₂, b₂) :: tl₂⟩ =>
     hT₁ == hT₂ && hB₁ == hB₂ && Compressed.beq ⟨t₁, b₁, tl₁⟩ ⟨t₂, b₂, tl₂⟩
  | _, _ => false

theorem simplify_normalise_proof {l₁ l₂ : List TseitinGen}
    (h : denote (simplify (normalise l₁)).toList = denote (simplify (normalise l₂)).toList) :
    denote l₁ = denote l₂ := by
  rw [← normalise_correctness (l := l₁), ← normalise_correctness (l := l₂),
      ← simplify_correctness (normalise l₁), ← simplify_correctness (normalise l₂), h]

open Lean Meta Elab Tactic in
elab "tseitin_norm" : tactic => liftMetaFinishingTactic fun goal ↦ do
  let goalType ← goal.getType'
  let some (_, lhs, rhs) := goalType.eq? | throwError "tseitin_norm: goal is not an equality"
  let raw₁ ← reify lhs
  let raw₂ ← reify rhs
  unless (normalise raw₁).beq (normalise raw₂) do throwError "tseitin_norm: normal forms differ"
  let nc₁ := mkApp (mkConst ``normalise_correctness) (toExpr raw₁)
  let nc₂ := mkApp (mkConst ``normalise_correctness) (toExpr raw₂)
  let symm₁ ← mkAppM ``Eq.symm #[nc₁]
  let proof ← mkAppM ``Eq.trans #[symm₁, nc₂]
  goal.assign proof

open Lean Meta Elab Tactic in
elab "create" : tactic => liftMetaFinishingTactic fun goal ↦ do
  let goalType ← goal.getType'
  let some (_, lhs, rhs) := goalType.eq? | throwError "create: goal is not an equality"
  let raw₁ ← reify lhs
  let raw₂ ← reify rhs
  unless (simplify (normalise raw₁)).beq (simplify (normalise raw₂)) do
    throwError "create: simplified normal forms differ"
  let raw₁Expr := toExpr raw₁
  let raw₂Expr := toExpr raw₂
  let norm₁ := mkApp (mkConst ``normalise) raw₁Expr
  let norm₂ := mkApp (mkConst ``normalise) raw₂Expr
  -- normalise_correctness : denote (normalise l).toList = denote l
  let nc₁ := mkApp (mkConst ``normalise_correctness) raw₁Expr
  let nc₂ := mkApp (mkConst ``normalise_correctness) raw₂Expr
  -- simplify_correctness : denote (simplify c).toList = denote c.toList
  let sc₁ := mkApp (mkConst ``simplify_correctness) norm₁
  let sc₂ := mkApp (mkConst ``simplify_correctness) norm₂
  -- chain: nc₁.symm.trans (sc₁.symm.trans (sc₂.trans nc₂))
  let tseitinTy := mkConst ``Tseitin
  let sc₂_nc₂ ← mkAppM ``Eq.trans #[sc₂, nc₂]
  let sc₁s ← mkAppM ``Eq.symm #[sc₁]
  -- This trans needs kernel reduction of `simplify`, so build with raw mkApp
  let denoteNorm₁ := mkApp (mkConst ``denote) (mkApp (mkConst ``Compressed.toList) norm₁)
  let denoteSimp₁ := mkApp (mkConst ``denote)
    (mkApp (mkConst ``Compressed.toList) (mkApp (mkConst ``simplify) norm₁))
  let denoteRaw₂ := mkApp (mkConst ``denote) raw₂Expr
  let mid := Lean.mkApp6 (mkConst ``Eq.trans [.succ .zero])
    tseitinTy denoteNorm₁ denoteSimp₁ denoteRaw₂ sc₁s sc₂_nc₂
  let nc₁s ← mkAppM ``Eq.symm #[nc₁]
  let proof ← mkAppM ``Eq.trans #[nc₁s, mid]
  goal.assign proof

end Tseitin

open Tseitin

example : a A b = a b A := by tseitin_norm
example : a A b B = a b A B := by tseitin_norm
example : a A b B = A B a b := by tseitin_norm

example : a A A X = a A A := by create
example : A b a A X = b a A A := by create
