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

def mapPair (a b : List Cell) : List TseitinGen := a.map Cell.asTop ++ b.map Cell.asBot

@[simp] lemma mapPair_nil_nil : mapPair [] [] = [] := rfl

def Compressed.toList : Compressed → List TseitinGen
  | ⟨tops, bots, []⟩ => mapPair tops bots
  | ⟨tops, bots, (top, bot) :: tail⟩ => mapPair tops bots ++ .X' :: toList ⟨top, bot, tail⟩

@[grind .] lemma toList_ne_empty_of_top {a b c} (ha : a ≠ []) : toList ⟨a, b, c⟩ ≠ [] := by
  cases c
  · simp [toList, mapPair, *]
  · rw [toList]; simp

@[grind .] lemma toList_ne_empty_of_bot {a b c} (bots : b ≠ []) : toList ⟨a, b, c⟩ ≠ [] := by
  cases c
  · simp [toList, mapPair, *]
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

@[simp, grind =] lemma denote_singleton (x : TseitinGen) : denote [x] = mk x := rfl

@[simp, grind =] lemma denote_cons_cons (x y : TseitinGen) (l : List TseitinGen) :
    denote (x :: y :: l) = mk x * denote (y :: l) :=
  foldl_mul_left (mk x) (mk y) l

lemma denote_cons {x} {l : List TseitinGen} (h : l ≠ []) :
    denote (x :: l) = mk x * denote l :=
  match l, h with | _ :: _, _ => denote_cons_cons ..

@[simp] lemma toList_cons_top (c : Cell) (tops : List Cell) (bots : List Cell)
    (tl : List (List Cell × List Cell)) :
    toList ⟨c :: tops, bots, tl⟩ = Cell.asTop c :: toList ⟨tops, bots, tl⟩ := by
  rcases tl with _ | ⟨⟨top, bot⟩, tl⟩ <;>
    simp only [Compressed.toList, mapPair, List.map_cons, List.cons_append]

@[simp] lemma toList_nil_nil_cons (tops bots : List Cell) (tl : List (List Cell × List Cell)) :
    toList ⟨[], [], (tops, bots) :: tl⟩ = X' :: toList ⟨tops, bots, tl⟩ := by
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

@[simp] private lemma denote_toList_cons_bot (c : Cell) (tops bots : List Cell)
    (tl : List (List Cell × List Cell)) :
    denote (toList ⟨tops, c :: bots, tl⟩) = denote (Cell.asBot c :: toList ⟨tops, bots, tl⟩) := by
  rcases tl with _ | ⟨⟨t, b⟩, rest⟩ <;>
    simp only [Compressed.toList, mapPair, List.map_cons, List.cons_append, List.append_assoc] <;>
    exact denote_bot_comm_tops c tops _

private lemma denote_cons_congr (x : TseitinGen) {l₁ l₂ : List TseitinGen}
    (h : denote l₁ = denote l₂) (he : l₁ = [] ↔ l₂ = []) :
    denote (x :: l₁) = denote (x :: l₂) := by
  rcases l₁ with _ | ⟨y, ys⟩
  · simp [he.mp rfl]
  · have : l₂ ≠ [] := fun h' => List.cons_ne_nil y ys (he.mpr h')
    rw [denote_cons (List.cons_ne_nil _ _), denote_cons this, h]

private lemma denote_append {l₁ l₂ : List TseitinGen} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    denote (l₁ ++ l₂) = denote l₁ * denote l₂ := by
  induction l₁ with
  | nil => exact absurd rfl h₁
  | cons x xs ih =>
    cases xs with
    | nil => exact denote_cons h₂
    | cons y ys =>
      simp only [List.cons_append, denote_cons_cons]
      grind

@[grind =]
private lemma denote_cons_append {x : TseitinGen} {l₁ l₂ : List TseitinGen} (h₂ : l₂ ≠ []) :
    denote (x :: l₁ ++ l₂) = denote (x :: l₁) * denote l₂ := by
  rw [denote_append (by simp) h₂]

@[grind =]
private lemma denote_append_cons {x : TseitinGen} {l₁ l₂ : List TseitinGen} (h₁ : l₁ ≠ []) :
    denote (l₁ ++ x :: l₂) = denote l₁ * denote (x :: l₂) := by
  rw [denote_append h₁ (List.cons_ne_nil _ _)]

private lemma denote_tops_comm_bots (tops : List Cell) (bots : List Cell) (rest : List TseitinGen) :
    denote (tops.map Cell.asTop ++ bots.map Cell.asBot ++ rest) =
    denote (bots.map Cell.asBot ++ tops.map Cell.asTop ++ rest) := by
  induction bots generalizing rest with
  | nil => simp
  | cons c bots' ih =>
    simp only [List.map_cons, List.cons_append, List.append_assoc]
    rw [denote_bot_comm_tops c tops (bots'.map Cell.asBot ++ rest)]
    have ih' := ih rest; simp only [List.append_assoc] at ih'
    exact denote_cons_congr _ ih' (by simp [List.append_eq_nil_iff]; tauto)

private lemma denote_mapPair_mul_X {tops bots : List Cell}
    (ha : [.a] <:+ tops) (haa : [.a, .a] <:+ bots) :
    denote (mapPair tops bots) * X = denote (mapPair tops bots) := by
  obtain ⟨tops', rfl⟩ := ha; obtain ⟨bots', rfl⟩ := haa
  simp only [mapPair, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
             List.singleton_append, Cell.asTop, Cell.asBot]
  suffices base : denote (a' :: List.map Cell.asBot bots' ++ [A', A']) * X =
      denote (a' :: List.map Cell.asBot bots' ++ [A', A']) by
    cases tops' with
    | nil => simpa using base
    | cons x xs =>
      simp only [List.map_cons]
      rw [denote_append_cons (List.cons_ne_nil _ _)]
      grind
  have : denote (a' :: bots'.map Cell.asBot ++ [A', A']) =
         denote (bots'.map Cell.asBot ++ [a', A', A']) := by
    simpa using denote_tops_comm_bots [.a] bots' [A', A']
  rw [this]
  cases bots' with
  | nil => exact acce
  | cons c cs =>
    rw [List.map_cons, denote_append_cons (by simp), ← mul_assoc]
    simp [denote, acce]

private lemma denote_prefix_congr (pref : List TseitinGen) {l₁ l₂ : List TseitinGen}
    (h : denote l₁ = denote l₂) (he : l₁ = [] ↔ l₂ = []) :
    denote (pref ++ l₁) = denote (pref ++ l₂) := by
  cases pref with grind

private lemma denote_mapPair_merge {tops top bots bot : List Cell} (rest : List TseitinGen) :
    denote (mapPair (tops ++ top) (bots ++ bot) ++ rest) =
    denote (mapPair tops bots ++ mapPair top bot ++ rest) := by
  simp only [mapPair, List.map_append, List.append_assoc]
  apply denote_prefix_congr (tops.map Cell.asTop)
  · simpa using denote_tops_comm_bots top bots (bot.map Cell.asBot ++ rest)
  · grind [List.append_eq_nil_iff]

private lemma denote_X_absorb {tops bots : List Cell} (ha : [.a] <:+ tops) (haa : [.a, .a] <:+ bots)
    (rest : List TseitinGen) :
    denote (mapPair tops bots ++ X' :: rest) = denote (mapPair tops bots ++ rest) := by
  have hne : mapPair tops bots ≠ [] := by obtain ⟨_, rfl⟩ := ha; simp [mapPair]
  cases rest with simp [denote_append_cons, denote_mapPair_mul_X, *]

private lemma merge_segments {tops bots : List Cell} (ha : [.a] <:+ tops) (haa : [.a, .a] <:+ bots)
    (top bot : List Cell) (tl : List (List Cell × List Cell)) :
    denote (toList ⟨tops ++ top, bots ++ bot, tl⟩) =
    denote (toList ⟨tops, bots, (top, bot) :: tl⟩) := by
  rcases tl with _ | ⟨⟨t2, b2⟩, tl'⟩
  · simp [toList, denote_X_absorb ha haa]
    simpa using denote_mapPair_merge []
  · simp [toList, denote_X_absorb ha haa]
    simpa using denote_mapPair_merge (X' :: toList ⟨t2, b2, tl'⟩)

meta def normalise : List TseitinGen → Compressed :=
  List.foldr (init := ⟨[], [], []⟩) <| fun
  | .X', ⟨tops, bots, xs⟩ => ⟨[], [], (tops, bots) :: xs⟩
  | .a', ⟨tops, bots, xs⟩ => ⟨.a :: tops, bots, xs⟩
  | .b', ⟨tops, bots, xs⟩ => ⟨.b :: tops, bots, xs⟩
  | .A', ⟨tops, bots, xs⟩ => ⟨tops, .a :: bots, xs⟩
  | .B', ⟨tops, bots, xs⟩ => ⟨tops, .b :: bots, xs⟩

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
    | nil => cases x <;> simp [toList, mapPair]
    | cons y l' => cases x <;> simp [denote_cons normalise_cons_ne_empty, ih]

private meta def simplifyAux (tops bots : List Cell) :
    List (List Cell × List Cell) → Compressed
  | [] => ⟨tops, bots, []⟩
  | (top, bot) :: tl =>
    if [.a].isSuffixOf tops && [.a, .a].isSuffixOf bots then
      simplifyAux (tops ++ top) (bots ++ bot) tl
    else ⟨tops, bots, (top, bot) :: tl⟩

meta def simplify (c : Compressed) : Compressed :=
  simplifyAux c.headTop c.headBot c.tail

private lemma simplifyAux_correctness (tops bots : List Cell) (tl : List (List Cell × List Cell)) :
    denote (simplifyAux tops bots tl).toList = denote (toList ⟨tops, bots, tl⟩) := by
  induction tl generalizing tops bots with
  | nil => rfl
  | cons p tl ih =>
    simp only [simplifyAux]
    split
    case isTrue h =>
      simp only [Bool.and_eq_true_iff, List.isSuffixOf_iff_suffix] at h
      rw [ih]
      exact merge_segments h.1 h.2 p.1 p.2 tl
    case isFalse => rfl

lemma simplify_correctness : ∀ c, denote (simplify c).toList = denote c.toList := by
  intro ⟨tops, bots, tl⟩
  exact simplifyAux_correctness tops bots tl

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
  | ⟨tops₁, bots₁, []⟩, ⟨tops₂, bots₂, []⟩ => tops₁ == tops₂ && bots₁ == bots₂
  | ⟨tops₁, bots₁, (t₁, b₁) :: tl₁⟩, ⟨tops₂, bots₂, (t₂, b₂) :: tl₂⟩ =>
     tops₁ == tops₂ && bots₁ == bots₂ && Compressed.beq ⟨t₁, b₁, tl₁⟩ ⟨t₂, b₂, tl₂⟩
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
