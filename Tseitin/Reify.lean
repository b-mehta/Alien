module

public import Tseitin.Defs
meta import Tseitin.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
meta import Qq

namespace Tseitin
open TseitinGen

set_option linter.style.setOption false
set_option pp.coercions false

section denote

/-- Evaluate a `List TseitinGen` as a product in `Tseitin`.  The empty list
evaluates to `X` as a junk value. -/
@[expose] public def denote : List TseitinGen → Tseitin
  | [] => X
  | x :: xs => xs.foldl (init := mk x) (· * mk ·)

variable {x y : TseitinGen} {l l₁ l₂ : List TseitinGen}

lemma foldl_mul_left (a b : Tseitin) (l : List TseitinGen) :
    l.foldl (init := a * b) (· * mk ·) = a * l.foldl (init := b) (· * mk ·) := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih => simp [← mul_assoc, ih]

@[simp, grind =] lemma denote_singleton : denote [x] = mk x := rfl

@[simp, grind =] lemma denote_cons_cons : denote (x :: y :: l) = mk x * denote (y :: l) :=
  foldl_mul_left (mk x) (mk y) l

@[simp, grind =] lemma denote_cons (h : l ≠ []) : denote (x :: l) = mk x * denote l := by
  induction l with grind

lemma denote_cons_congr (h : denote l₁ = denote l₂) (he : l₁ = [] ↔ l₂ = []) :
    denote (x :: l₁) = denote (x :: l₂) := by grind

lemma denote_append (hl₁ : l₁ ≠ []) (hl₂ : l₂ ≠ []) :
    denote (l₁ ++ l₂) = denote l₁ * denote l₂ := by
  induction l₁ with
  | nil => grind
  | cons x xs ih => cases xs with simp_all

@[grind =]
lemma denote_cons_append (h₂ : l₂ ≠ []) : denote (x :: l₁ ++ l₂) = denote (x :: l₁) * denote l₂ :=
  denote_append (by simp) h₂

@[grind =]
lemma denote_append_cons (h₁ : l₁ ≠ []) : denote (l₁ ++ x :: l₂) = denote l₁ * denote (x :: l₂) :=
  denote_append h₁ (by simp)

lemma denote_prefix_congr (h : denote l₁ = denote l₂) (he : l₁ = [] ↔ l₂ = []) :
    denote (l ++ l₁) = denote (l ++ l₂) := by
  cases l with grind

lemma denote_suffix_congr (h : denote l₁ = denote l₂) (he : l₁ = [] ↔ l₂ = []) :
    denote (l₁ ++ l) = denote (l₂ ++ l) := by
  cases l with grind

end denote

/-- A `Compressed` value represents the normal form of a `List TseitinGen`.
The list is split into *segments* separated by `X`:

  `headTop headBot X top₁ bot₁ X top₂ bot₂ X ...`

where each `topᵢ`/`botᵢ` are lists of `Cell`s.  Within each segment, all top
generators (lowercase: `a`, `b`) come before all bottom generators (uppercase:
`A`, `B`), in the order induced by `mapPair`. -/
public structure Compressed : Type where
  /-- Top-row generators (lowercase) of the leading segment. -/
  headTop : List Cell
  /-- Bottom-row generators (uppercase) of the leading segment. -/
  headBot : List Cell
  /-- Remaining segments, each a `(top, bot)` pair following an `X`. -/
  tail : List (List Cell × List Cell)
deriving BEq

open Compressed

section

/-- Interleave two `Cell` lists as generators: tops first, then bots. -/
@[expose] public def mapPair (tops bots : List Cell) : List TseitinGen :=
  tops.map Cell.asTop ++ bots.map Cell.asBot

@[simp] lemma mapPair_nil_nil : mapPair [] [] = [] := rfl
@[simp] lemma mapPair_nil_left {bots : List Cell} : mapPair [] bots = bots.map Cell.asBot := rfl
@[simp] lemma mapPair_nil_right {tops : List Cell} : mapPair tops [] = tops.map Cell.asTop := by
  simp [mapPair]
@[simp] lemma mapPair_cons_left {c : Cell} {tops : List Cell} {bots : List Cell} :
    mapPair (c :: tops) bots = c.asTop :: mapPair tops bots := by
  simp [mapPair]

/-- Flatten a `Compressed` value back to a `List TseitinGen`, inserting `X'` between segments. -/
@[expose] public def Compressed.toList : Compressed → List TseitinGen
  | ⟨tops, bots, []⟩ => mapPair tops bots
  | ⟨tops, bots, (top, bot) :: tail⟩ => mapPair tops bots ++ .X' :: toList ⟨top, bot, tail⟩

@[simp] lemma toList_nil {tops bots : List Cell} : toList ⟨tops, bots, []⟩ = mapPair tops bots := by
  rw [toList]

@[simp] lemma toList_cons {tops bots : List Cell}
    {t : List Cell × List Cell} {tail : List (List Cell × List Cell)} :
    toList ⟨tops, bots, t :: tail⟩ =
      mapPair tops bots ++ .X' :: toList ⟨t.1, t.2, tail⟩ := by
  rw [toList]

@[grind .] lemma toList_ne_empty_of_top {tops bots tl} (ha : tops ≠ []) :
    toList ⟨tops, bots, tl⟩ ≠ [] := by
  cases tl with simp [mapPair, *]

@[grind .] lemma toList_ne_empty_of_bot {tops bots tl} (hb : bots ≠ []) :
    toList ⟨tops, bots, tl⟩ ≠ [] := by
  cases tl with simp [mapPair, *]

@[grind .] lemma toList_ne_empty_of_tail {tops bots tl} (hc : tl ≠ []) :
    toList ⟨tops, bots, tl⟩ ≠ [] := by
  cases tl with simp_all

@[simp] lemma toList_cons_top (c : Cell) (tops : List Cell) (bots : List Cell)
    (tl : List (List Cell × List Cell)) :
    toList ⟨c :: tops, bots, tl⟩ = c.asTop :: toList ⟨tops, bots, tl⟩ := by
  cases tl with simp [mapPair]

end

lemma bot_top_comm (x y : Cell) : mk x.asBot * mk y.asTop = mk y.asTop * mk x.asBot := by
  rcases x <;> rcases y <;> simp

@[simp] lemma denote_bot_top {x y : Cell} {l : List TseitinGen} :
    denote (x.asBot :: y.asTop :: l) = denote (y.asTop :: x.asBot :: l) := by
  cases l with simp [bot_top_comm]

lemma denote_bot_comm_tops (x : Cell) (tops : List Cell) (rest : List TseitinGen) :
    denote (x.asBot :: (tops.map Cell.asTop ++ rest)) =
    denote (tops.map Cell.asTop ++ x.asBot :: rest) := by
  induction tops with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, List.cons_append, denote_bot_top] at ih ⊢
    apply denote_cons_congr ih (by simp)

lemma denote_bots_comm_tops {tops bots : List Cell} {rest : List TseitinGen} :
    denote (bots.map Cell.asBot ++ (tops.map Cell.asTop ++ rest)) =
    denote (tops.map Cell.asTop ++ (bots.map Cell.asBot ++ rest)) := by
  induction bots with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.cons_append] at ih ⊢
    rw [denote_cons_congr ih (by grind [List.append_eq_nil_iff])]
    grind [denote_bot_comm_tops]

@[simp] lemma denote_toList_cons_bot (c : Cell) (tops bots : List Cell)
    (tl : List (List Cell × List Cell)) :
    denote (toList ⟨tops, c :: bots, tl⟩) = denote (c.asBot :: toList ⟨tops, bots, tl⟩) := by
  cases tl with simp [mapPair, ← denote_bot_comm_tops]

lemma denote_mapPair_merge {tops₁ tops₂ bots₁ bots₂ : List Cell} (rest : List TseitinGen) :
    denote (mapPair tops₁ bots₁ ++ (mapPair tops₂ bots₂ ++ rest)) =
    denote (mapPair (tops₁ ++ tops₂) (bots₁ ++ bots₂) ++ rest) := by
  simpa [mapPair] using
    denote_prefix_congr denote_bots_comm_tops (by grind [List.append_eq_nil_iff])

lemma denote_mapPair_merge' {tops₁ tops₂ bots₁ bots₂ : List Cell} :
    denote (mapPair tops₁ bots₁ ++ mapPair tops₂ bots₂) =
    denote (mapPair (tops₁ ++ tops₂) (bots₁ ++ bots₂)) := by
  simpa using denote_mapPair_merge []

lemma denote_mapPair_mul_X {tops bots : List Cell}
    (htops : [.a] <:+ tops) (hbots : [.a, .a] <:+ bots) :
    denote (mapPair tops bots) * X = denote (mapPair tops bots) := by
  obtain ⟨tops, rfl⟩ := htops
  obtain ⟨bots, rfl⟩ := hbots
  have (l) (hl : l ≠ []) : denote l * X = denote (l ++ [.X']) := by simp [denote_append_cons hl]
  rw [← denote_mapPair_merge', this _ (by simp), List.append_assoc]
  exact denote_prefix_congr (by simp [acce]) (by simp)

lemma denote_X_absorb {tops bots : List Cell}
    (htops : [.a] <:+ tops) (hbots : [.a, .a] <:+ bots) (rest : List TseitinGen) :
    denote (mapPair tops bots ++ X' :: rest) = denote (mapPair tops bots ++ rest) := by
  have hne : mapPair tops bots ≠ [] := by simp [mapPair, htops.ne_nil]
  cases rest with simp [denote_append_cons hne, denote_mapPair_mul_X, *]

lemma merge_segments {tops bots : List Cell} (ha : [.a] <:+ tops) (haa : [.a, .a] <:+ bots)
    (tops₁ bots₁ : List Cell) (tl : List (List Cell × List Cell)) :
    denote (toList ⟨tops, bots, (tops₁, bots₁) :: tl⟩) =
    denote (toList ⟨tops ++ tops₁, bots ++ bots₁, tl⟩) := by
  cases tl with
  | nil => simp [denote_X_absorb ha haa, denote_mapPair_merge']
  | cons hd tl => simp [denote_X_absorb ha haa, denote_mapPair_merge]

/-- Normalise a `List TseitinGen` into `Compressed` form by scanning right-to-left:
`X` starts a new segment, lowercase generators go into `headTop`, uppercase into `headBot`. -/
@[expose] public def normalise : List TseitinGen → Compressed :=
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

/-- The normalised form evaluates to the same element as the original list. -/
public theorem normalise_correctness :
    ∀ l : List TseitinGen, denote (normalise l).toList = denote l
  | [] => by simp
  | [x] => by cases x <;> simp [mapPair]
  | x :: y :: l => by
    cases x <;> simp [denote_cons normalise_cons_ne_empty, normalise_correctness (y :: l)]

/-- Worker for `simplify`.  Merges the current segment `(tops, bots)` with the next one
when the current segment ends with `a … aA A` (i.e. `[.a] <:+ tops` and `[.a,.a] <:+ bots`),
because in that case `X` is absorbed.  Recurses until no further merging is possible. -/
@[expose] public def simplifyAux (tops bots : List Cell) :
    List (List Cell × List Cell) → Compressed
  | [] => ⟨tops, bots, []⟩
  | (top, bot) :: tl =>
    if [.a].isSuffixOf tops && [.a, .a].isSuffixOf bots then
      simplifyAux (tops ++ top) (bots ++ bot) tl
    else
      let r := simplifyAux top bot tl
      ⟨tops, bots, (r.headTop, r.headBot) :: r.tail⟩

/-- Simplify a `Compressed` value by merging segments where `X` is absorbed. -/
@[expose] public def simplify (c : Compressed) : Compressed :=
  simplifyAux c.headTop c.headBot c.tail

lemma simplifyAux_toList_nil_iff (tops bots : List Cell) (tl : List (List Cell × List Cell)) :
    (simplifyAux tops bots tl).toList = [] ↔ toList ⟨tops, bots, tl⟩ = [] := by
  fun_induction simplifyAux with grind [List.append_eq_nil_iff, List.IsSuffix.ne_nil]

lemma simplifyAux_correctness (tops bots : List Cell) (tl : List (List Cell × List Cell)) :
    denote (simplifyAux tops bots tl).toList = denote (toList ⟨tops, bots, tl⟩) := by
  fun_induction simplifyAux with
  | case1 => simp
  | case2 => grind [merge_segments]
  | case3 tops bots tops₁ bots₁ tl h r ih =>
    simp only [toList]
    refine denote_prefix_congr ?_ (by simp)
    apply denote_cons_congr ih
    simp [simplifyAux_toList_nil_iff]

/-- Simplification preserves the denotation. -/
public lemma simplify_correctness : ∀ c, denote (simplify c).toList = denote c.toList := by
  intro ⟨tops, bots, tl⟩
  exact simplifyAux_correctness tops bots tl

/-- Extract the longest common element-wise prefix of two `Cell` lists, returning
`(pfx, tops₁, bots₁)` such that `tops = pfx ++ tops₁` and `bots = pfx ++ bots₁`. -/
@[expose] public def matchPrefix : List Cell → List Cell → List Cell × List Cell × List Cell
  | c :: tops, c₁ :: bots =>
    if c = c₁ then
      let (pfx, tops₁, bots₁) := matchPrefix tops bots
      (c :: pfx, tops₁, bots₁)
    else ([], c :: tops, c₁ :: bots)
  | tops, bots => ([], tops, bots)

lemma matchPrefix_tops (tops bots : List Cell) :
    tops = (matchPrefix tops bots).1 ++ (matchPrefix tops bots).2.1 := by
  induction tops generalizing bots with
  | nil => simp [matchPrefix]
  | cons c tops ih =>
    cases bots with
    | nil => simp [matchPrefix]
    | cons c₁ bots₁ =>
      unfold matchPrefix; split
      · next h => subst h; simpa using ih bots₁
      · simp

lemma matchPrefix_bots (tops bots : List Cell) :
    bots = (matchPrefix tops bots).1 ++ (matchPrefix tops bots).2.2 := by
  induction tops generalizing bots with
  | nil => simp [matchPrefix]
  | cons c tops ih =>
    cases bots with
    | nil => simp [matchPrefix]
    | cons c₁ bots₁ =>
      unfold matchPrefix; split
      · next h => subst h; simpa using ih bots₁
      · simp

/-- Worker for `moveX`. For each `X` boundary, push it rightward past any common prefix
of the adjacent top/bot lists using the `ea`/`eb` swap axioms, absorbing matched pairs
into the preceding segment's `headBot`. -/
@[expose] public def moveXAux (tops bots : List Cell) :
    List (List Cell × List Cell) → Compressed
  | [] => ⟨tops, bots, []⟩
  | (tops₁, bots₁) :: tl =>
    let (pfx, tops₂, bots₂) := matchPrefix tops₁ bots₁
    let r := moveXAux tops₂ bots₂ tl
    ⟨tops, bots ++ pfx, (r.headTop, r.headBot) :: r.tail⟩

/-- Push each `X` rightward past matching top/bot pairs via `ea`/`eb` swap axioms. -/
@[expose] public def moveX (c : Compressed) : Compressed :=
  moveXAux c.headTop c.headBot c.tail

lemma mapPair_append_bots (tops bots extra : List Cell) :
    mapPair tops (bots ++ extra) = mapPair tops bots ++ extra.map Cell.asBot := by
  simp [mapPair, List.map_append, List.append_assoc]

lemma X_cell_swap (c : Cell) (rest : List TseitinGen) :
    denote (X' :: Cell.asTop c :: Cell.asBot c :: rest) = denote (Cell.asBot c :: X' :: rest) := by
  cases rest with
  | nil => cases c <;> [exact ea_swap; exact eb_swap]
  | cons r rs =>
    cases c <;> simp only [denote_cons_cons, Cell.asTop, Cell.asBot, mk_a', mk_b', mk_A', mk_B',
      mk_X']
    · rw [← _root_.mul_assoc, ← _root_.mul_assoc, ea_swap, _root_.mul_assoc]
    · rw [← _root_.mul_assoc, ← _root_.mul_assoc, eb_swap, _root_.mul_assoc]

lemma denote_matchPrefix_swap (pfx tops₁ bots₁ : List Cell)
    (rest : List TseitinGen) :
    denote (X' :: mapPair (pfx ++ tops₁) (pfx ++ bots₁) ++ rest) =
    denote (pfx.map Cell.asBot ++ X' :: mapPair tops₁ bots₁ ++ rest) := by
  induction pfx generalizing tops₁ bots₁ rest with
  | nil => simp
  | cons c pfx₁ ih =>
    simp only [List.cons_append, mapPair, List.map_cons, List.map_append, List.append_assoc,
      List.cons_append]
    -- move c.asBot past (pfx₁++tops₁) tops via denote_bot_comm_tops
    have h1 := denote_bot_comm_tops c (pfx₁ ++ tops₁)
      ((pfx₁ ++ bots₁).map Cell.asBot ++ rest)
    simp only [List.map_append, List.append_assoc] at h1
    have h2 := denote_cons_congr (x := Cell.asTop c) h1 (by simp [List.append_eq_nil_iff])
    have h3 := denote_cons_congr (x := X') h2 (by simp)
    -- Now: denote (X' :: c.asTop :: (c.asBot :: ...) ++ ... ) — flatten cons_append
    rw [← h3, X_cell_swap]
    -- denote (c.asBot :: X' :: ... ++ ...) = denote (c.asBot :: pfx₁.map asBot ++ ...)
    have h4 := ih tops₁ bots₁ rest
    simp only [mapPair, List.map_append, List.append_assoc, List.cons_append] at h4
    exact denote_cons_congr (x := Cell.asBot c) h4 (by simp [List.append_eq_nil_iff])

lemma moveXAux_toList_eq_nil (tops bots : List Cell)
    (tl : List (List Cell × List Cell)) :
    (moveXAux tops bots tl).toList = [] ↔ toList ⟨tops, bots, tl⟩ = [] := by
  induction tl generalizing tops bots with
  | nil => exact Iff.rfl
  | cons p tl _ =>
    obtain ⟨tops₁, bots₁⟩ := p
    simp only [moveXAux, Compressed.toList, mapPair_append_bots]
    constructor <;> (intro h; simp at h)

lemma moveXAux_correctness (tops bots : List Cell)
    (tl : List (List Cell × List Cell)) :
    denote (moveXAux tops bots tl).toList = denote (toList ⟨tops, bots, tl⟩) := by
  induction tl generalizing tops bots with
  | nil => rfl
  | cons p tl ih =>
    obtain ⟨tops₁, bots₁⟩ := p
    simp only [moveXAux]
    set pfx := (matchPrefix tops₁ bots₁).1
    set tops₂ := (matchPrefix tops₁ bots₁).2.1
    set bots₂ := (matchPrefix tops₁ bots₁).2.2
    have htops : tops₁ = pfx ++ tops₂ := matchPrefix_tops tops₁ bots₁
    have hbots : bots₁ = pfx ++ bots₂ := matchPrefix_bots tops₁ bots₁
    set r := moveXAux tops₂ bots₂ tl
    have ih_step : denote r.toList = denote (toList ⟨tops₂, bots₂, tl⟩) := ih tops₂ bots₂
    simp only [Compressed.toList, mapPair_append_bots, List.append_assoc]
    rw [htops, hbots]
    apply denote_prefix_congr (l := mapPair tops bots)
    · have h_inner := denote_cons_congr (x := X') ih_step (moveXAux_toList_eq_nil tops₂ bots₂ tl)
      have h_swap := denote_prefix_congr (l := pfx.map Cell.asBot) h_inner (by simp)
      rw [h_swap]
      rcases tl with _ | ⟨⟨tops₃, bots₃⟩, tl₁⟩ <;> simp only [Compressed.toList]
      · have := (denote_matchPrefix_swap pfx tops₂ bots₂ []).symm
        simpa using this
      · have := (denote_matchPrefix_swap pfx tops₂ bots₂
            (X' :: toList ⟨tops₃, bots₃, tl₁⟩)).symm
        simpa [List.append_assoc] using this
    · simp

/-- Moving `X` rightward preserves the denotation. -/
public lemma moveX_correctness : ∀ c : Compressed,
    denote (moveX c).toList = denote c.toList := by
  intro ⟨tops, bots, tl⟩
  exact moveXAux_correctness tops bots tl

open Lean Meta Elab Tactic

/-- `ToExpr` instance for `TseitinGen`, used when building proof terms by reflection. -/
instance : ToExpr TseitinGen where
  toExpr
    | .a' => mkConst ``TseitinGen.a'
    | .b' => mkConst ``TseitinGen.b'
    | .A' => mkConst ``TseitinGen.A'
    | .B' => mkConst ``TseitinGen.B'
    | .X' => mkConst ``TseitinGen.X'
  toTypeExpr := mkConst ``TseitinGen

open Qq in
/-- Map a `TseitinGen` to its corresponding quoted `Tseitin` generator expression. -/
def genToExpr : TseitinGen → Q(Tseitin)
  | .a' => q(a)
  | .b' => q(b)
  | .A' => q(A)
  | .B' => q(B)
  | .X' => q(X)

open Qq in
/-- Convert a `List TseitinGen` to a quoted `Tseitin` product expression. -/
def unreify (l : List TseitinGen) : MetaM Q(Tseitin) :=
  match l with
  | [] => return q(X)
  | g :: gs => gs.foldlM (init := genToExpr g) fun acc g => return q($acc * $(genToExpr g))

open Qq in
/-- Quoted `HMul` instance for `Tseitin`, used in `unreify'`. -/
nonrec def hMul : Q(HMul Tseitin Tseitin Tseitin) := q(inferInstance)

/-- Convert a `List TseitinGen` to a raw `Expr` product without `MetaM`. -/
def unreify' (l : List TseitinGen) : Expr :=
  match l with
  | [] => mkConst ``Tseitin.X
  | g :: gs => gs.foldl (init := genToExpr g) fun acc g =>
    mkAppN (mkConst ``HMul.hMul)
      #[mkConst ``Tseitin, mkConst ``Tseitin, mkConst ``Tseitin, hMul, acc, genToExpr g]

open Lean Meta in
/-- Parse a `Tseitin` product expression into a `List TseitinGen`,
failing on unrecognised subterms. -/
partial def reify (e : Expr) : MetaM (List TseitinGen) := do
  match_expr e with
  | HMul.hMul _ _ _ _ x y => return (← reify x) ++ (← reify y)
  | Tseitin.a => return [.a']
  | Tseitin.b => return [.b']
  | Tseitin.A => return [.A']
  | Tseitin.B => return [.B']
  | Tseitin.X => return [.X']
  | _ => throwError "reify: unexpected Tseitin expression {e}"

/-- Normalise a single `Tseitin` expression, returning a `Simp.Result` containing the
new expression and a proof `old = new`.  `compute` is the normalisation function;
`extraStep` optionally names an additional `Compressed → Compressed` pass (e.g. `simplify`
or `moveX`) and its correctness lemma, for proof-chain construction. -/
public def normaliseExpr (e : Expr)
    (compute : List TseitinGen → Compressed)
    (extraStep : Option (Lean.Name × Lean.Name) := none) : MetaM Simp.Result := do
  let raw ← reify e
  let norm := (compute raw).toList
  let rawExpr := toExpr raw
  let normExpr := toExpr norm
  let nc_raw := mkApp (mkConst ``normalise_correctness) rawExpr
  let nc_norm := mkApp (mkConst ``normalise_correctness) normExpr
  let proof ← match extraStep with
  | none =>
    let s ← mkAppM ``Eq.symm #[nc_raw]
    mkAppM ``Eq.trans #[s, nc_norm]
  | some (stepName, corrName) =>
    let normC_raw := mkApp (mkConst ``normalise) rawExpr
    let normC_norm := mkApp (mkConst ``normalise) normExpr
    let xc_raw := mkApp (mkConst corrName) normC_raw
    let xc_norm := mkApp (mkConst corrName) normC_norm
    let tseitinTy := mkConst ``Tseitin
    let xc_norm_nc_norm ← mkAppM ``Eq.trans #[xc_norm, nc_norm]
    let xc_raw_s ← mkAppM ``Eq.symm #[xc_raw]
    let denoteNormRaw := mkApp (mkConst ``denote)
      (mkApp (mkConst ``Compressed.toList) normC_raw)
    let denoteStepRaw := mkApp (mkConst ``denote)
      (mkApp (mkConst ``Compressed.toList) (mkApp (mkConst stepName) normC_raw))
    let denoteNormExpr := mkApp (mkConst ``denote) normExpr
    let mid := Lean.mkApp6 (mkConst ``Eq.trans [.succ .zero])
      tseitinTy denoteNormRaw denoteStepRaw denoteNormExpr xc_raw_s xc_norm_nc_norm
    let nc_raw_s ← mkAppM ``Eq.symm #[nc_raw]
    mkAppM ``Eq.trans #[nc_raw_s, mid]
  let newExpr ← unreify norm
  return { expr := newExpr, proof? := some proof }

/-- Conv mode: normalise the currently focused expression. -/
def convNormalise (compute : List TseitinGen → Compressed)
    (extraStep : Option (Lean.Name × Lean.Name) := none) : TacticM Unit := do
  let lhs ← instantiateMVars (← Conv.getLhs)
  Conv.applySimpResult (← normaliseExpr lhs compute extraStep)

/-- Tactic mode: normalise both sides of an equality goal; close if they match, else rewrite. -/
def eqTactic (goal : MVarId) (compute : List TseitinGen → Compressed)
    (extraStep : Option (Lean.Name × Lean.Name) := none) : MetaM (Option MVarId) := do
  let goalType ← goal.getType'
  let some (_, lhs, rhs) := goalType.eq? | throwError "goal is not an equality"
  let rLhs ← normaliseExpr lhs compute extraStep
  let rRhs ← normaliseExpr rhs compute extraStep
  if rLhs.expr == rRhs.expr then
    -- Both sides normalise to the same thing: close with proofLhs.trans proofRhs.symm
    let proofRhsSymm ← mkAppM ``Eq.symm #[rRhs.proof?.get!]
    let proof ← mkAppM ``Eq.trans #[rLhs.proof?.get!, proofRhsSymm]
    goal.assign proof
    return none
  else
    -- Change goal to newLhs = newRhs
    let tseitinTy := mkConst ``Tseitin
    let newGoalTy := mkApp3 (mkConst ``Eq [.succ .zero]) tseitinTy rLhs.expr rRhs.expr
    let newGoalMVar ← mkFreshExprMVar newGoalTy
    let proofRhsSymm ← mkAppM ``Eq.symm #[rRhs.proof?.get!]
    let proof ← mkAppM ``Eq.trans
      #[rLhs.proof?.get!, ← mkAppM ``Eq.trans #[newGoalMVar, proofRhsSymm]]
    goal.assign proof
    return some newGoalMVar.mvarId!

/-- Tactic implementation for `norm`: reorder generators within each segment. -/
public def normTactic (goal : MVarId) : MetaM (Option MVarId) :=
  eqTactic goal normalise
/-- Tactic implementation for `create`: additionally absorb `X` where possible. -/
public def createTactic (goal : MVarId) : MetaM (Option MVarId) :=
  eqTactic goal (simplify ∘ normalise) (some (``simplify, ``simplify_correctness))
/-- Tactic implementation for `move`: additionally push `X` rightward via swap axioms. -/
public def moveTactic (goal : MVarId) : MetaM (Option MVarId) :=
  eqTactic goal (moveX ∘ normalise) (some (``moveX, ``moveX_correctness))

/-- Conv implementation for `norm`. -/
public def normConv : TacticM Unit :=
  convNormalise normalise
/-- Conv implementation for `create`. -/
public def createConv : TacticM Unit :=
  convNormalise (simplify ∘ normalise) (some (``simplify, ``simplify_correctness))
/-- Conv implementation for `move`. -/
public def moveConv : TacticM Unit :=
  convNormalise (moveX ∘ normalise) (some (``moveX, ``moveX_correctness))

end Tseitin
