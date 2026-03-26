module

public import Tseitin.Defs
meta import Tseitin.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
meta import Qq

namespace Tseitin
open TseitinGen

set_option linter.style.setOption false
set_option pp.coercions false

public structure Compressed : Type where
  headTop : List Cell
  headBot : List Cell
  tail : List (List Cell × List Cell)
deriving BEq

open Compressed

@[expose] public def mapPair (a b : List Cell) : List TseitinGen :=
  a.map Cell.asTop ++ b.map Cell.asBot

@[simp] lemma mapPair_nil_nil : mapPair [] [] = [] := rfl

@[expose] public def Compressed.toList : Compressed → List TseitinGen
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

@[expose] public def denote : List TseitinGen → Tseitin
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

public theorem normalise_correctness :
    ∀ l : List TseitinGen, denote (normalise l).toList = denote l := by
  intro l
  induction l with
  | nil => simp [toList]
  | cons x l ih =>
    cases l with
    | nil => cases x <;> simp [toList, mapPair]
    | cons y l' => cases x <;> simp [denote_cons normalise_cons_ne_empty, ih]

@[expose] public def simplifyAux (tops bots : List Cell) :
    List (List Cell × List Cell) → Compressed
  | [] => ⟨tops, bots, []⟩
  | (top, bot) :: tl =>
    if [.a].isSuffixOf tops && [.a, .a].isSuffixOf bots then
      simplifyAux (tops ++ top) (bots ++ bot) tl
    else
      let r := simplifyAux top bot tl
      ⟨tops, bots, (r.headTop, r.headBot) :: r.tail⟩

@[expose] public def simplify (c : Compressed) : Compressed :=
  simplifyAux c.headTop c.headBot c.tail

private lemma simplifyAux_toList_ne_nil (tops bots : List Cell)
    (tl : List (List Cell × List Cell)) (htl : tl ≠ []) :
    (simplifyAux tops bots tl).toList ≠ [] := by
  induction tl generalizing tops bots with
  | nil => exact absurd rfl htl
  | cons p tl ih =>
    obtain ⟨top, bot⟩ := p
    simp only [simplifyAux]
    split
    · cases tl with
      | nil =>
        simp only [simplifyAux, Compressed.toList]
        simp only [Bool.and_eq_true_iff, List.isSuffixOf_iff_suffix] at *
        obtain ⟨⟨t', rfl⟩, _⟩ := ‹_ ∧ _›
        simp [mapPair]
      | cons q tl' => exact ih (tops ++ top) (bots ++ bot) (List.cons_ne_nil _ _)
    · intro h
      have hr : (⟨(simplifyAux top bot tl).headTop, (simplifyAux top bot tl).headBot,
          (simplifyAux top bot tl).tail⟩ : Compressed) = simplifyAux top bot tl := by
        cases simplifyAux top bot tl; rfl
      simp [Compressed.toList, hr] at h

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
    case isFalse =>
      obtain ⟨top, bot⟩ := p
      have hr : (⟨(simplifyAux top bot tl).headTop, (simplifyAux top bot tl).headBot,
          (simplifyAux top bot tl).tail⟩ : Compressed) = simplifyAux top bot tl := by
        cases simplifyAux top bot tl; rfl
      simp only [hr, Compressed.toList]
      have h_iff : (simplifyAux top bot tl).toList = [] ↔
          toList ⟨top, bot, tl⟩ = [] := by
        cases tl with
        | nil => exact Iff.rfl
        | cons q tl' =>
          exact ⟨fun h => absurd h (simplifyAux_toList_ne_nil _ _ _ (List.cons_ne_nil _ _)),
                 fun h => absurd h (toList_ne_empty_of_tail (List.cons_ne_nil _ _))⟩
      apply denote_prefix_congr (mapPair tops bots) _ ⟨by simp, by simp⟩
      exact denote_cons_congr X' (ih top bot) h_iff

public lemma simplify_correctness : ∀ c, denote (simplify c).toList = denote c.toList := by
  intro ⟨tops, bots, tl⟩
  exact simplifyAux_correctness tops bots tl

-- matchPrefix: extract longest common prefix of tops and bots (element-wise)
@[expose] public def matchPrefix : List Cell → List Cell → List Cell × List Cell × List Cell
  | c :: tops, c' :: bots =>
    if c = c' then
      let (matched, remTops, remBots) := matchPrefix tops bots
      (c :: matched, remTops, remBots)
    else ([], c :: tops, c' :: bots)
  | tops, bots => ([], tops, bots)

private lemma matchPrefix_tops (tops bots : List Cell) :
    tops = (matchPrefix tops bots).1 ++ (matchPrefix tops bots).2.1 := by
  induction tops generalizing bots with
  | nil => simp [matchPrefix]
  | cons c tops ih =>
    cases bots with
    | nil => simp [matchPrefix]
    | cons c' bots' =>
      unfold matchPrefix; split
      · next h => subst h; simpa using ih bots'
      · simp

private lemma matchPrefix_bots (tops bots : List Cell) :
    bots = (matchPrefix tops bots).1 ++ (matchPrefix tops bots).2.2 := by
  induction tops generalizing bots with
  | nil => simp [matchPrefix]
  | cons c tops ih =>
    cases bots with
    | nil => simp [matchPrefix]
    | cons c' bots' =>
      unfold matchPrefix; split
      · next h => subst h; simpa using ih bots'
      · simp

-- moveX: push X rightward by consuming matched top/bot pairs via ea_swap/eb_swap
@[expose] public def moveXAux (headTop headBot : List Cell) :
    List (List Cell × List Cell) → Compressed
  | [] => ⟨headTop, headBot, []⟩
  | (tops, bots) :: tl =>
    let (matched, remTops, remBots) := matchPrefix tops bots
    let r := moveXAux remTops remBots tl
    ⟨headTop, headBot ++ matched, (r.headTop, r.headBot) :: r.tail⟩

@[expose] public def moveX (c : Compressed) : Compressed :=
  moveXAux c.headTop c.headBot c.tail

private lemma mapPair_append_bots (tops bots extra : List Cell) :
    mapPair tops (bots ++ extra) = mapPair tops bots ++ extra.map Cell.asBot := by
  simp [mapPair, List.map_append, List.append_assoc]

private lemma X_cell_swap (c : Cell) (rest : List TseitinGen) :
    denote (X' :: Cell.asTop c :: Cell.asBot c :: rest) = denote (Cell.asBot c :: X' :: rest) := by
  cases rest with
  | nil => cases c <;> [exact ea_swap; exact eb_swap]
  | cons r rs =>
    cases c <;> simp only [denote_cons_cons, Cell.asTop, Cell.asBot, mk_a', mk_b', mk_A', mk_B',
      mk_X']
    · rw [← _root_.mul_assoc, ← _root_.mul_assoc, ea_swap, _root_.mul_assoc]
    · rw [← _root_.mul_assoc, ← _root_.mul_assoc, eb_swap, _root_.mul_assoc]

private lemma denote_matchPrefix_swap (matched remTops remBots : List Cell)
    (rest : List TseitinGen) :
    denote (X' :: mapPair (matched ++ remTops) (matched ++ remBots) ++ rest) =
    denote (matched.map Cell.asBot ++ X' :: mapPair remTops remBots ++ rest) := by
  induction matched generalizing remTops remBots rest with
  | nil => simp
  | cons c matched' ih =>
    simp only [List.cons_append, mapPair, List.map_cons, List.map_append, List.append_assoc,
      List.cons_append]
    -- move c.asBot past (matched'++remTops) tops via denote_bot_comm_tops
    have h1 := denote_bot_comm_tops c (matched' ++ remTops)
      ((matched' ++ remBots).map Cell.asBot ++ rest)
    simp only [List.map_append, List.append_assoc] at h1
    have h2 := denote_cons_congr (Cell.asTop c) h1 (by simp [List.append_eq_nil_iff])
    have h3 := denote_cons_congr X' h2 (by simp)
    -- Now: denote (X' :: c.asTop :: (c.asBot :: ...) ++ ... ) — flatten cons_append
    rw [h3]; simp only [List.cons_append, List.append_assoc]; rw [X_cell_swap]
    -- denote (c.asBot :: X' :: ... ++ ...) = denote (c.asBot :: matched'.map asBot ++ ...)
    have h4 := ih remTops remBots rest
    simp only [mapPair, List.map_append, List.append_assoc, List.cons_append] at h4
    exact denote_cons_congr (Cell.asBot c) h4 (by simp [List.append_eq_nil_iff])

private lemma moveXAux_toList_eq_nil (hTop hBot : List Cell)
    (tl : List (List Cell × List Cell)) :
    (moveXAux hTop hBot tl).toList = [] ↔ toList ⟨hTop, hBot, tl⟩ = [] := by
  induction tl generalizing hTop hBot with
  | nil => exact Iff.rfl
  | cons p tl _ =>
    obtain ⟨t, b⟩ := p
    simp only [moveXAux, Compressed.toList, mapPair_append_bots]
    constructor <;> (intro h; simp at h)

private lemma moveXAux_correctness (headTop headBot : List Cell)
    (tl : List (List Cell × List Cell)) :
    denote (moveXAux headTop headBot tl).toList = denote (toList ⟨headTop, headBot, tl⟩) := by
  induction tl generalizing headTop headBot with
  | nil => rfl
  | cons p tl ih =>
    obtain ⟨tops, bots⟩ := p
    simp only [moveXAux]
    set m := (matchPrefix tops bots).1
    set rt := (matchPrefix tops bots).2.1
    set rb := (matchPrefix tops bots).2.2
    have htops : tops = m ++ rt := matchPrefix_tops tops bots
    have hbots : bots = m ++ rb := matchPrefix_bots tops bots
    set r := moveXAux rt rb tl
    have ih_step : denote r.toList = denote (toList ⟨rt, rb, tl⟩) := ih rt rb
    have hr_eta : (⟨r.headTop, r.headBot, r.tail⟩ : Compressed) = r := by cases r; rfl
    simp only [Compressed.toList, mapPair_append_bots, List.append_assoc, hr_eta]
    rw [htops, hbots]
    apply denote_prefix_congr (mapPair headTop headBot)
    · -- Use congruence to replace r.toList with toList ⟨rt, rb, tl⟩
      have h_inner := denote_cons_congr X' ih_step (moveXAux_toList_eq_nil rt rb tl)
      have h_swap := denote_prefix_congr (m.map Cell.asBot) h_inner ⟨by simp, by simp⟩
      rw [h_swap]
      rcases tl with _ | ⟨⟨t2, b2⟩, tl'⟩ <;> simp only [Compressed.toList]
      · have := (denote_matchPrefix_swap m rt rb []).symm
        simpa using this
      · have := (denote_matchPrefix_swap m rt rb
          (X' :: toList ⟨t2, b2, tl'⟩)).symm
        simpa [List.append_assoc] using this
    · simp

public lemma moveX_correctness : ∀ c : Compressed,
    denote (moveX c).toList = denote c.toList := by
  intro ⟨tops, bots, tl⟩
  exact moveXAux_correctness tops bots tl

open Lean in
def genToExpr : TseitinGen → Expr
  | .a' => mkConst ``Tseitin.a
  | .b' => mkConst ``Tseitin.b
  | .A' => mkConst ``Tseitin.A
  | .B' => mkConst ``Tseitin.B
  | .X' => mkConst ``Tseitin.X

open Lean Meta in
def unreify (l : List TseitinGen) : MetaM Expr :=
  match l with
  | [] => return mkConst ``Tseitin.X
  | g :: gs => gs.foldlM (init := genToExpr g) fun acc g =>
    mkAppM ``HMul.hMul #[acc, genToExpr g]

open Lean Meta in
partial def reify (e : Expr) : MetaM (List TseitinGen) := do
  match_expr e with
  | HMul.hMul _ _ _ _ x y => return (← reify x) ++ (← reify y)
  | Tseitin.a => return [.a']
  | Tseitin.b => return [.b']
  | Tseitin.A => return [.A']
  | Tseitin.B => return [.B']
  | Tseitin.X => return [.X']
  | _ => throwError "reify: unexpected Tseitin expression {e}"

open Lean in
instance : ToExpr TseitinGen where
  toExpr
    | .a' => mkConst ``TseitinGen.a'
    | .b' => mkConst ``TseitinGen.b'
    | .A' => mkConst ``TseitinGen.A'
    | .B' => mkConst ``TseitinGen.B'
    | .X' => mkConst ``TseitinGen.X'
  toTypeExpr := mkConst ``TseitinGen

theorem simplify_normalise_proof {l₁ l₂ : List TseitinGen}
    (h : denote (simplify (normalise l₁)).toList = denote (simplify (normalise l₂)).toList) :
    denote l₁ = denote l₂ := by
  rw [← normalise_correctness (l := l₁), ← normalise_correctness (l := l₂),
      ← simplify_correctness (normalise l₁), ← simplify_correctness (normalise l₂), h]

open Lean Meta Elab Tactic

public def normTactic (goal : MVarId) : MetaM (Option MVarId) := do
  let goalType ← goal.getType'
  let some (_, lhs, rhs) := goalType.eq? | throwError "tseitin_norm: goal is not an equality"
  let raw₁ ← reify lhs
  let raw₂ ← reify rhs
  let raw₁Expr := toExpr raw₁
  let raw₂Expr := toExpr raw₂
  -- normalise_correctness : denote (normalise l).toList = denote l
  let nc₁ := mkApp (mkConst ``normalise_correctness) raw₁Expr
  let nc₂ := mkApp (mkConst ``normalise_correctness) raw₂Expr
  -- new goal: denote (normalise raw₁).toList = denote (normalise raw₂).toList
  let tseitinTy := mkConst ``Tseitin
  let denoteNormLhs := mkApp (mkConst ``denote)
    (mkApp (mkConst ``Compressed.toList) (mkApp (mkConst ``normalise) raw₁Expr))
  let denoteNormRhs := mkApp (mkConst ``denote)
    (mkApp (mkConst ``Compressed.toList) (mkApp (mkConst ``normalise) raw₂Expr))
  let newGoalTy := mkApp3 (mkConst ``Eq [.succ .zero]) tseitinTy denoteNormLhs denoteNormRhs
  -- Also build a nice (reduced) version for display
  let niceNormLhs ← unreify (normalise raw₁).toList
  let niceNormRhs ← unreify (normalise raw₂).toList
  let niceGoalTy := mkApp3 (mkConst ``Eq [.succ .zero]) tseitinTy niceNormLhs niceNormRhs
  if normalise raw₁ == normalise raw₂ then
    -- Close by chaining nc₁.symm ∘ nc₂
    let symm₁ ← mkAppM ``Eq.symm #[nc₁]
    let proof ← mkAppM ``Eq.trans #[symm₁, nc₂]
    goal.assign proof
    return none
  else
    -- Change goal to the normalised form
    let newGoalMVar ← mkFreshExprMVar newGoalTy
    let nc₁s ← mkAppM ``Eq.symm #[nc₁]
    let proof ← mkAppM ``Eq.trans #[nc₁s, ← mkAppM ``Eq.trans #[newGoalMVar, nc₂]]
    goal.assign proof
    -- Replace the goal type with the reduced (nice) version for display
    let niceGoal ← newGoalMVar.mvarId!.replaceTargetDefEq niceGoalTy
    return some niceGoal

public def createTactic (goal : MVarId) : MetaM Unit := do
  let goalType ← goal.getType'
  let some (_, lhs, rhs) := goalType.eq? | throwError "create: goal is not an equality"
  let raw₁ ← reify lhs
  let raw₂ ← reify rhs
  unless simplify (normalise raw₁) == simplify (normalise raw₂) do
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

public def moveTactic (goal : MVarId) : MetaM Unit := do
  let goalType ← goal.getType'
  let some (_, lhs, rhs) := goalType.eq? | throwError "move: goal is not an equality"
  let raw₁ ← reify lhs
  let raw₂ ← reify rhs
  unless moveX (normalise raw₁) == moveX (normalise raw₂) do
    throwError "move: normal forms after moveX differ"
  let raw₁Expr := toExpr raw₁
  let raw₂Expr := toExpr raw₂
  let norm₁ := mkApp (mkConst ``normalise) raw₁Expr
  let norm₂ := mkApp (mkConst ``normalise) raw₂Expr
  let nc₁ := mkApp (mkConst ``normalise_correctness) raw₁Expr
  let nc₂ := mkApp (mkConst ``normalise_correctness) raw₂Expr
  let mc₁ := mkApp (mkConst ``moveX_correctness) norm₁
  let mc₂ := mkApp (mkConst ``moveX_correctness) norm₂
  let tseitinTy := mkConst ``Tseitin
  -- Chain: nc₁⁻¹ ∘ mc₁⁻¹ ∘ [kernel rfl] ∘ mc₂ ∘ nc₂
  let mc₂_nc₂ ← mkAppM ``Eq.trans #[mc₂, nc₂]
  let mc₁s ← mkAppM ``Eq.symm #[mc₁]
  let denoteNorm₁ := mkApp (mkConst ``denote)
    (mkApp (mkConst ``Compressed.toList) norm₁)
  let denoteMoveX₁ := mkApp (mkConst ``denote)
    (mkApp (mkConst ``Compressed.toList) (mkApp (mkConst ``moveX) norm₁))
  let denoteRaw₂ := mkApp (mkConst ``denote) raw₂Expr
  let mid := Lean.mkApp6 (mkConst ``Eq.trans [.succ .zero])
    tseitinTy denoteNorm₁ denoteMoveX₁ denoteRaw₂ mc₁s mc₂_nc₂
  let nc₁s ← mkAppM ``Eq.symm #[nc₁]
  let proof ← mkAppM ``Eq.trans #[nc₁s, mid]
  goal.assign proof

end Tseitin
