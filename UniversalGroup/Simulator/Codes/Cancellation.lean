module

public import UniversalGroup.Simulator.Codes.Free
public import UniversalGroup.Simulator.Core.PositiveWords

@[expose] public section

/-!
# Literal cancellation for Valiev's code words and marker

The code words share a stem and a tail, with respective middle branches `10`
and `01`. In a reduced signed code word, adjacent opposite signs cancel only
these common pieces; a letter of every branch survives. The marker leaves
this graph through `001`, so an inverse final branch retains a negative
letter. An explicit reduced spelling proves positivity reflection.

Comparing the reduced conjugate with a negative-positive fraction then shows
that one of its two positive endpoints ends in the marker. Prefix decoding
upgrades this alternative to the recognition conclusion needed by the
simulator subgroup-intersection proof.
-/

namespace UniversalGroup.CodeCancellation
open CodeSubgroups
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
abbrev Letter := Fin 2 × Bool

def positiveLetters (w : PositiveWord) : List Letter := w.map (fun i => (i, true))
def negativeLetters (w : PositiveWord) : List Letter := FreeGroup.invRev (positiveLetters w)
def stem : PositiveWord := [0, 1, 0, 1, 0, 0]
def tail (r : ℕ) : PositiveWord := List.replicate (r - 1) 0
def branch (i : Fin 2) : PositiveWord := if i = 0 then [1, 0] else [0, 1]
def markerTail (r t : ℕ) : PositiveWord := [0, 0, 1] ++ tail r ++ List.replicate (2 * t) 1

theorem code_split (r : ℕ) (hr : 2 ≤ r) (i : Fin 2) :
    valievCode r i = stem ++ branch i ++ tail r := by
  fin_cases i
  · have h : r = 1 + (r - 1) := by omega
    conv_lhs => unfold valievCode
    simp only [Fin.val_zero, Nat.zero_add, Nat.sub_zero]
    rw [h, List.replicate_add]
    simp [stem, branch, tail, List.append_assoc, show 1 + (r - 1) - 1 = r - 1 by omega]
  · simp [valievCode, stem, branch, tail, List.append_assoc]

theorem marker_split (r t : ℕ) : valievMarker r t = stem ++ markerTail r t := by
  simp [valievMarker, stem, markerTail, tail, List.append_assoc]

@[simp] theorem mk_positiveLetters (w : PositiveWord) :
    FreeGroup.mk (positiveLetters w) = positiveFree w := BorisovCStage.positiveFree_eq_eval w
@[simp] theorem mk_negativeLetters (w : PositiveWord) :
    FreeGroup.mk (negativeLetters w) = (positiveFree w)⁻¹ := by
  rw [negativeLetters, ← FreeGroup.inv_mk, mk_positiveLetters]
@[simp] theorem positiveFree_append (u v : PositiveWord) :
    positiveFree (u ++ v) = positiveFree u * positiveFree v := by
  simp [positiveFree, evalPositive, List.map_append, List.prod_append]
@[simp] theorem positiveFree_nil : positiveFree [] = 1 := by simp [positiveFree, evalPositive]
@[simp] theorem positiveFree_cons (i : Fin 2) (w : PositiveWord) :
    positiveFree (i :: w) = FreeGroup.of i * positiveFree w := by
  fin_cases i <;> simp [positiveFree, evalPositive]
@[simp] theorem positiveFree_toWord (w : PositiveWord) :
    (positiveFree w).toWord = positiveLetters w := by
  rw [← mk_positiveLetters]
  exact BorisovCStage.positiveFree_toWord w

private theorem reduced_same_sign (L : List Letter) (b : Bool)
    (h : ∀ a ∈ L, a.2 = b) : FreeGroup.IsReduced L := by
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [FreeGroup.IsReduced, List.isChain_cons]
      refine ⟨?_, ih (by intro x hx; exact h x (by simp [hx]))⟩
      intro x hx _
      exact (h a (by simp)).trans (h x (List.mem_cons_of_mem _ (List.mem_of_mem_head? hx))).symm

private theorem prepend_same_sign (L R : List Letter) (b : Bool)
    (hL : ∀ a ∈ L, a.2 = b) (hR : FreeGroup.IsReduced R)
    (hhead : ∀ a ∈ R.head?, a.2 = b) : FreeGroup.IsReduced (L ++ R) := by
  apply List.IsChain.append (reduced_same_sign L b hL) hR
  intro a ha z hz _
  exact (hL a (List.mem_of_mem_getLast? ha)).trans (hhead z hz).symm
private theorem positive_sign (w : PositiveWord) (a : Letter)
    (ha : a ∈ positiveLetters w) : a.2 = true := by
  rcases List.mem_map.mp ha with ⟨i, _, rfl⟩
  rfl
private theorem negative_sign (w : PositiveWord) (a : Letter)
    (ha : a ∈ negativeLetters w) : a.2 = false := by
  simp only [negativeLetters, FreeGroup.invRev, List.mem_map, List.mem_reverse] at ha
  rcases ha with ⟨x, hx, rfl⟩
  simp [positive_sign w x hx]

def gap (r : ℕ) (b c : Bool) : List Letter :=
  if b = c then
    if b then positiveLetters (tail r ++ stem) else negativeLetters (tail r ++ stem)
  else []
def signedBranch (a : Letter) : List Letter :=
  if a.2 then positiveLetters (branch a.1) else negativeLetters (branch a.1)
def lastPart (r t : ℕ) (a : Letter) : List Letter :=
  if a.2 then positiveLetters (branch a.1 ++ tail r ++ valievMarker r t)
  else if a.1 = 0 then [(0, false), (1, false)] ++ positiveLetters (markerTail r t)
  else [(1, false)] ++ positiveLetters ([0, 1] ++ tail r ++ List.replicate (2 * t) 1)
def inner (r t : ℕ) (a : Letter) : List Letter → List Letter
  | [] => lastPart r t a
  | b :: w => signedBranch a ++ gap r a.2 b.2 ++ inner r t b w
def start (r : ℕ) (b : Bool) : List Letter :=
  if b then positiveLetters stem else negativeLetters (tail r)
def normal (r t : ℕ) : List Letter → List Letter
  | [] => positiveLetters (valievMarker r t)
  | a :: w => start r a.2 ++ inner r t a w

private theorem inner_head (r t : ℕ) (a : Letter) (w : List Letter) :
    (inner r t a w).head? =
      some (if a.2 then (if a.1 = 0 then 1 else 0, true) else (a.1, false)) := by
  rcases a with ⟨i, b⟩
  cases w <;> cases b <;> fin_cases i <;>
    simp [inner, lastPart, signedBranch, branch, positiveLetters, negativeLetters,
      FreeGroup.invRev]

private theorem lastPart_reduced (r t : ℕ) (a : Letter) :
    FreeGroup.IsReduced (lastPart r t a) := by
  rcases a with ⟨i, b⟩
  cases b
  · fin_cases i
    · change FreeGroup.IsReduced ((0, false) :: (1, false) ::
        (0, true) :: (0, true) :: (1, true) :: positiveLetters (tail r ++ List.replicate (2*t) 1))
      simp only [FreeGroup.isReduced_cons_cons]
      exact ⟨by simp, by simp, by simp, by simp,
        prepend_same_sign [(1,true)] _ true (by simp) (reduced_same_sign _ true (positive_sign _))
          (by intro a ha; exact positive_sign _ a (List.mem_of_mem_head? ha))⟩
    · change FreeGroup.IsReduced ((1, false) :: (0, true) :: (1, true) ::
        positiveLetters (tail r ++ List.replicate (2*t) 1))
      simp only [FreeGroup.isReduced_cons_cons]
      exact ⟨by simp, by simp,
        prepend_same_sign [(1,true)] _ true (by simp) (reduced_same_sign _ true (positive_sign _))
          (by intro a ha; exact positive_sign _ a (List.mem_of_mem_head? ha))⟩
  · exact reduced_same_sign _ true (positive_sign _)

private theorem inner_reduced (r t : ℕ) (a : Letter) (w : List Letter)
    (h : FreeGroup.IsReduced (a :: w)) : FreeGroup.IsReduced (inner r t a w) := by
  induction w generalizing a with
  | nil => exact lastPart_reduced r t a
  | cons b w ih =>
      have hab := (FreeGroup.isReduced_cons_cons.mp h).1
      have hb := ih b (FreeGroup.isReduced_cons_cons.mp h).2
      rw [inner]
      by_cases hs : a.2 = b.2
      · apply prepend_same_sign _ _ a.2 ?_ hb ?_
        · intro x hx
          simp only [List.mem_append] at hx
          rcases hx with hx | hx
          · cases ha : a.2 <;> simp only [signedBranch, ha, Bool.false_eq_true, ↓reduceIte] at hx
            · exact negative_sign _ x hx
            · exact positive_sign _ x hx
          · simp only [gap, hs, ↓reduceIte] at hx
            rw [← hs] at hx
            cases ha : a.2 <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] at hx
            · exact negative_sign _ x hx
            · exact positive_sign _ x hx
        · simp only [inner_head, Option.mem_some_iff]
          rintro x rfl
          cases hb' : b.2 <;> simp [hb', hs]
      · simp only [gap, hs, ↓reduceIte, List.append_nil]
        rcases a with ⟨i, s⟩
        rcases b with ⟨j, z⟩
        have hhead := inner_head r t (j,z) w
        clear ih h
        cases s <;> cases z <;> fin_cases i <;> fin_cases j <;>
          simp_all [signedBranch, branch, positiveLetters, negativeLetters, FreeGroup.invRev,
            FreeGroup.IsReduced, List.isChain_cons]


private theorem normal_reduced (r t : ℕ) (w : List Letter)
    (h : FreeGroup.IsReduced w) : FreeGroup.IsReduced (normal r t w) := by
  cases w with
  | nil => exact reduced_same_sign _ true (positive_sign _)
  | cons a w =>
      apply prepend_same_sign _ _ a.2 ?_ (inner_reduced r t a w h) ?_
      · intro x hx
        cases ha : a.2 <;> simp only [start, ha, Bool.false_eq_true, ↓reduceIte] at hx
        · exact negative_sign _ x hx
        · exact positive_sign _ x hx
      · simp only [inner_head, Option.mem_some_iff]
        rintro x rfl
        cases ha : a.2 <;> simp [ha]

private theorem mk_letter (a : Letter) :
    FreeGroup.mk [a] = if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹ := by
  rcases a with ⟨i, b⟩
  cases b <;> rfl
private theorem mk_cons (a : Letter) (w : List Letter) :
    FreeGroup.mk (a :: w) = FreeGroup.mk [a] * FreeGroup.mk w :=
  by
  change FreeGroup.mk ([a] ++ w) = _
  exact FreeGroup.mul_mk.symm

private theorem mk_cons_eval (a : Letter) (w : List Letter) :
    FreeGroup.mk (a :: w) =
      (if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹) * FreeGroup.mk w := by
  rw [mk_cons, mk_letter]

private theorem inner_eval (r t : ℕ) (hr : 2 ≤ r) (a : Letter) (w : List Letter) :
    FreeGroup.mk (inner r t a w) =
      (FreeGroup.mk (start r a.2))⁻¹ * codeLift r (FreeGroup.mk (a :: w)) *
        positiveFree (valievMarker r t) := by
  induction w generalizing a with
  | nil =>
      rcases a with ⟨i,b⟩
      cases b <;> fin_cases i <;>
        simp only [inner, lastPart, start, Prod.fst, Prod.snd, Bool.false_eq_true,
          Bool.true_eq_false, ↓reduceIte, Fin.isValue, Fin.reduceEq,
          mk_positiveLetters, mk_negativeLetters, mk_letter, codeLift,
          map_inv, FreeGroup.lift_apply_of, code_split r hr, marker_split,
          positiveFree_append, branch, markerTail, List.cons_append, List.nil_append]
      all_goals
        simp only [mk_cons_eval, mk_letter, Prod.fst, Prod.snd, ↓reduceIte,
          mk_positiveLetters, positiveFree_cons, positiveFree_nil]
        simp [Fin.ext_iff, mk_cons_eval, mk_letter, positiveFree_cons, mul_assoc]
  | cons b w ih =>
      rw [inner, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ih,
        mk_cons a (b :: w), map_mul]
      rcases a with ⟨i,s⟩
      rcases b with ⟨j,z⟩
      cases s <;> cases z <;>
        simp only [signedBranch, gap, start, Prod.fst, Prod.snd,
          Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
          mk_positiveLetters, mk_negativeLetters, mk_letter,
          codeLift, map_inv, FreeGroup.lift_apply_of, code_split r hr,
          positiveFree_append, FreeGroup.one_eq_mk.symm]
      all_goals group

private theorem normal_eval (r t : ℕ) (hr : 2 ≤ r) (w : List Letter) :
    FreeGroup.mk (normal r t w) =
      codeLift r (FreeGroup.mk w) * positiveFree (valievMarker r t) := by
  cases w with
  | nil => simp [normal, ← FreeGroup.one_eq_mk]
  | cons a w =>
      rw [normal, ← FreeGroup.mul_mk, inner_eval r t hr]
      group

private theorem inner_signs (r t : ℕ) (a : Letter) (w : List Letter)
    (h : ∀ x ∈ inner r t a w, x.2 = true) :
    ∀ x ∈ a :: w, x.2 = true := by
  induction w generalizing a with
  | nil =>
      have hh := h _ (List.mem_of_mem_head? (show _ ∈ (inner r t a []).head? from
        by rw [inner_head]; exact Option.mem_some.mpr rfl))
      have ha : a.2 = true := by
        cases hb : a.2
        · simp [hb] at hh
        · rfl
      simpa using ha
  | cons b w ih =>
      have hh := h _ (List.mem_of_mem_head? (show _ ∈ (inner r t a (b::w)).head? from
        by rw [inner_head]; exact Option.mem_some.mpr rfl))
      have ha : a.2 = true := by
        cases hb : a.2
        · simp [hb] at hh
        · rfl
      have hb := ih b (by
        intro x hx
        exact h x (by simp only [inner, List.mem_append]; exact Or.inr hx))
      simpa only [List.mem_cons, forall_eq_or_imp] using And.intro ha hb

private theorem normal_signs (r t : ℕ) (w : List Letter)
    (h : ∀ x ∈ normal r t w, x.2 = true) : ∀ x ∈ w, x.2 = true := by
  cases w with
  | nil => simp
  | cons a w =>
      exact inner_signs r t a w (by
        intro x hx
        exact h x (List.mem_append_right _ hx))

private theorem positive_of_signs (g : FreeGroup (Fin 2))
    (h : ∀ a ∈ g.toWord, a.2 = true) :
    g = positiveFree (g.toWord.map Prod.fst) := by
  apply (FreeGroup.mk_toWord (x := g)).symm.trans
  rw [← mk_positiveLetters]
  congr 1
  simp only [positiveLetters, List.map_map]
  conv_lhs => rw [← List.map_id g.toWord]
  apply List.map_congr_left
  intro a ha
  rcases a with ⟨i,b⟩
  simp only [id_eq, Function.comp_apply, Prod.fst, Prod.mk.injEq, true_and]
  exact h (i,b) ha

@[simp] theorem codeLift_positive (r : ℕ) (v : PositiveWord) :
    codeLift r (positiveFree v) = positiveFree (v.flatMap (valievCode r)) := by
  induction v with
  | nil => simp
  | cons i v ih =>
      rw [positiveFree_cons, map_mul, ih, List.flatMap_cons, positiveFree_append]
      simp [codeLift]

/-- A signed code word followed by the literal marker can be positive only
when every code letter is positive. The marker suffix survives literally. -/
theorem code_mul_marker_positive (r t : ℕ) (hr : 2 ≤ r)
    (g : FreeGroup (Fin 2)) (Q : PositiveWord)
    (h : codeLift r g * positiveFree (valievMarker r t) = positiveFree Q) :
    ∃ v : PositiveWord, g = positiveFree v ∧
      Q = v.flatMap (valievCode r) ++ valievMarker r t := by
  have hn := normal_reduced r t g.toWord FreeGroup.isReduced_toWord
  have he : normal r t g.toWord = positiveLetters Q := by
    have he := congrArg FreeGroup.toWord (normal_eval r t hr g.toWord)
    rw [FreeGroup.mk_toWord, h, positiveFree_toWord, FreeGroup.toWord_mk, hn.reduce_eq] at he
    exact he
  have hg := positive_of_signs g (normal_signs r t g.toWord (by
    intro a ha
    exact positive_sign Q a (he ▸ ha)))
  refine ⟨g.toWord.map Prod.fst, hg, ?_⟩
  apply BorisovCStage.positiveFree_injective
  rw [BorisovCStage.positiveFree_eq_eval, BorisovCStage.positiveFree_eq_eval]
  change positiveFree Q = positiveFree _
  calc
    positiveFree Q = codeLift r g * positiveFree (valievMarker r t) := h.symm
    _ = codeLift r (positiveFree (g.toWord.map Prod.fst)) * positiveFree (valievMarker r t) :=
      congrArg (fun x => codeLift r x * positiveFree (valievMarker r t)) hg
    _ = _ := by rw [codeLift_positive, positiveFree_append]

@[simp] theorem negativeLetters_append (A B : PositiveWord) :
    negativeLetters (A ++ B) = negativeLetters B ++ negativeLetters A := by
  simp [negativeLetters, positiveLetters, FreeGroup.invRev, List.map_append]
@[simp] theorem negativeLetters_cons (i : Fin 2) (W : PositiveWord) :
    negativeLetters (i :: W) = negativeLetters W ++ [(i, false)] := by
  simp [negativeLetters, positiveLetters, FreeGroup.invRev]

private theorem fraction_reduced (A B : PositiveWord)
    (h : ∀ a ∈ A.head?, ∀ b ∈ B.head?, a ≠ b) :
    FreeGroup.IsReduced (negativeLetters A ++ positiveLetters B) := by
  apply List.IsChain.append (reduced_same_sign _ false (negative_sign _))
    (reduced_same_sign _ true (positive_sign _))
  intro a ha b hb hab
  simp only [negativeLetters, FreeGroup.invRev, List.getLast?_map,
    List.getLast?_reverse, positiveLetters, List.head?_map, Option.mem_map] at ha
  rcases ha with ⟨x, ⟨y, hy, rfl⟩, rfl⟩
  simp only [positiveLetters, List.head?_map, Option.mem_map] at hb
  rcases hb with ⟨z, hz, rfl⟩
  exact False.elim (h y hy z hz hab)

/-- Cancelling the common initial segment of two positive words gives the
canonical negative-positive spelling of their quotient. -/
private theorem fraction_normal (W V : PositiveWord) :
    ∃ X A B : PositiveWord, W = X ++ A ∧ V = X ++ B ∧
      ((positiveFree W)⁻¹ * positiveFree V).toWord = negativeLetters A ++ positiveLetters B := by
  induction W generalizing V with
  | nil =>
      refine ⟨[], [], V, rfl, rfl, ?_⟩
      simp [negativeLetters, positiveLetters, FreeGroup.invRev]
  | cons a W ih =>
      cases V with
      | nil =>
          refine ⟨[], a::W, [], rfl, rfl, ?_⟩
          rw [positiveFree_nil, mul_one, ← mk_negativeLetters, FreeGroup.toWord_mk,
            (reduced_same_sign _ false (negative_sign _)).reduce_eq]
          simp [positiveLetters]
      | cons b V =>
          by_cases hab : a = b
          · subst b
            rcases ih V with ⟨X,A,B,hW,hV,he⟩
            refine ⟨a::X,A,B,by simp [hW],by simp [hV],?_⟩
            simpa [positiveFree_cons, mul_inv_rev, mul_assoc] using he
          · refine ⟨[],a::W,b::V,rfl,rfl,?_⟩
            have hr := fraction_reduced (a::W) (b::V) (by simpa using hab)
            rw [← mk_negativeLetters, ← mk_positiveLetters, FreeGroup.mul_mk,
              FreeGroup.toWord_mk, hr.reduce_eq]

private theorem negative_prefix (L A B : List Letter)
    (hL : ∀ x ∈ L, x.2 = false) (hB : ∀ x ∈ B, x.2 = true)
    (h : L <+: A ++ B) : L <+: A := by
  induction A generalizing L with
  | nil =>
      cases L with
      | nil => simp
      | cons x L =>
          have hf := hL x (by simp)
          have ht := hB x (h.sublist.subset (by simp))
          simp [hf] at ht
  | cons a A ih =>
      cases L with
      | nil => simp
      | cons x L =>
          obtain ⟨rfl, hp⟩ := List.cons_prefix_cons.mp h
          exact List.cons_prefix_cons.mpr ⟨rfl,
            ih L (by intro x hx; exact hL x (by simp [hx])) hp⟩


private theorem positive_prefix (L A B : List Letter)
    (hL : ∀ x ∈ L, x.2 = true) (hB : ∀ x ∈ B, x.2 = false)
    (h : L <+: A ++ B) : L <+: A := by
  induction A generalizing L with
  | nil =>
      cases L with
      | nil => simp
      | cons x L =>
          have hf := hL x (by simp)
          have ht := hB x (h.sublist.subset (by simp))
          simp [hf] at ht
  | cons a A ih =>
      cases L with
      | nil => simp
      | cons x L =>
          obtain ⟨rfl, hp⟩ := List.cons_prefix_cons.mp h
          exact List.cons_prefix_cons.mpr ⟨rfl,
            ih L (by intro x hx; exact hL x (by simp [hx])) hp⟩

private theorem positive_suffix (L A B : List Letter)
    (hL : ∀ x ∈ L, x.2 = true) (hA : ∀ x ∈ A, x.2 = false)
    (h : L <:+ A ++ B) : L <:+ B := by
  apply List.reverse_prefix.mp
  apply positive_prefix L.reverse B.reverse A.reverse
  · intro x hx
    exact hL x (by simpa using hx)
  · intro x hx
    exact hA x (by simpa using hx)
  · simpa using List.reverse_prefix.mpr h

private theorem fraction_signs (A B : PositiveWord) :
    (negativeLetters A ++ positiveLetters B).Pairwise
      (fun a b => a.2 = true → b.2 = true) := by
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_of_forall_sublist
    intro a b hab ht
    have ha := negative_sign A a (hab.subset (by simp))
    simp [ha] at ht
  · apply List.pairwise_of_forall_sublist
    intro a b hab _
    exact positive_sign B b (hab.subset (by simp))
  · intro a ha b _ hab
    simp [negative_sign A a ha] at hab

private theorem all_positive_of_pairwise_head (L : List Letter)
    (hp : L.Pairwise (fun a b => a.2 = true → b.2 = true))
    (hh : ∃ i, L.head? = some (i, true)) : ∀ a ∈ L, a.2 = true := by
  rcases hh with ⟨i, hi⟩
  rcases List.head?_eq_some_iff.mp hi with ⟨R,rfl⟩
  simp only [List.mem_cons, forall_eq_or_imp, true_and]
  intro a ha
  exact (List.pairwise_cons.mp hp).1 a ha rfl

private theorem positiveLetters_suffix_iff (P W : PositiveWord) :
    positiveLetters P <:+ positiveLetters W ↔ P <:+ W := by
  constructor
  · intro h
    simpa [positiveLetters, List.map_map, Function.comp_def] using h.map Prod.fst
  · intro h
    exact h.map (fun i => (i,true))

private theorem negativeLetters_prefix_iff (P W : PositiveWord) :
    negativeLetters P <+: negativeLetters W ↔ P <:+ W := by
  constructor
  · intro h
    apply List.reverse_prefix.mp
    simpa [negativeLetters, FreeGroup.invRev, positiveLetters, List.map_map,
      Function.comp_def] using h.map Prod.fst
  · intro h
    have he := (List.reverse_prefix.mpr h).map (fun i => (i,false))
    simpa [negativeLetters, FreeGroup.invRev, positiveLetters, List.map_map,
      Function.comp_def, List.map_reverse] using he

def trimmed (r t : ℕ) (i : Fin 2) (w : List Letter) : List Letter :=
  if i = 0 then inner r t (i,true) w else (inner r t (i,true) w).tail

def markerCut (r t : ℕ) (i : Fin 2) : PositiveWord :=
  if i = 0 then markerTail r t else [0,1] ++ tail r ++ List.replicate (2*t) 1

private theorem inner_trimmed (r t : ℕ) (i : Fin 2) (w : List Letter) :
    inner r t (i,true) w =
      (if i = 0 then [] else [(0,true)]) ++ trimmed r t i w := by
  fin_cases i
  · simp [trimmed]
  · have hh := inner_head r t (1,true) w
    simp only [Prod.fst, Prod.snd, ↓reduceIte, Fin.isValue, Fin.reduceEq] at hh
    rcases List.head?_eq_some_iff.mp hh with ⟨R, hR⟩
    simp [trimmed, hR]

private theorem trimmed_head (r t : ℕ) (i : Fin 2) (w : List Letter) :
    (trimmed r t i w).head? = some (1,true) := by
  fin_cases i <;> cases w <;>
    simp [trimmed, inner, lastPart, signedBranch, branch, positiveLetters]

private theorem trimmed_reduced (r t : ℕ) (i : Fin 2) (w : List Letter)
    (h : FreeGroup.IsReduced ((i,true)::w)) : FreeGroup.IsReduced (trimmed r t i w) := by
  have hi := inner_reduced r t (i,true) w h
  rw [inner_trimmed] at hi
  exact List.IsChain.right_of_append hi

private theorem positive_conjugate_reduced (r t : ℕ) (i : Fin 2) (w : List Letter)
    (h : FreeGroup.IsReduced ((i,true)::w)) :
    FreeGroup.IsReduced (negativeLetters (markerCut r t i) ++ trimmed r t i w) := by
  apply List.IsChain.append (reduced_same_sign _ false (negative_sign _))
    (trimmed_reduced r t i w h)
  intro a ha b hb hab
  simp only [trimmed_head, Option.mem_some_iff] at hb
  subst b
  fin_cases i <;>
    simp [markerCut, markerTail, negativeLetters, FreeGroup.invRev, positiveLetters] at ha
  all_goals rcases ha with rfl; simp at hab

private theorem positive_conjugate_eval (r t : ℕ) (hr : 2 ≤ r)
    (i : Fin 2) (w : List Letter) :
    FreeGroup.mk (negativeLetters (markerCut r t i) ++ trimmed r t i w) =
      (positiveFree (valievMarker r t))⁻¹ * codeLift r (FreeGroup.mk ((i,true)::w)) *
        positiveFree (valievMarker r t) := by
  have he := inner_eval r t hr (i,true) w
  rw [inner_trimmed, ← FreeGroup.mul_mk] at he
  rw [← FreeGroup.mul_mk, mk_negativeLetters]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at he ⊢
  · simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, ← FreeGroup.one_eq_mk,
      one_mul, start, mk_positiveLetters] at he
    rw [he, marker_split]
    simp only [markerCut, Fin.isValue, Fin.reduceEq, ↓reduceIte, positiveFree_append]
    group
  · simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, mk_letter, Prod.fst, Prod.snd,
      start, mk_positiveLetters] at he
    have ht : FreeGroup.mk (trimmed r t 1 w) =
        (FreeGroup.of 0)⁻¹ * ((positiveFree stem)⁻¹ *
          codeLift r (FreeGroup.mk ((1,true)::w)) * positiveFree (valievMarker r t)) := by
      rw [← he]
      group
    rw [ht, marker_split]
    simp only [markerCut, Fin.isValue, Fin.reduceEq, ↓reduceIte, markerTail,
      positiveFree_append, positiveFree_cons, positiveFree_nil]
    group

private theorem normal_negative_head (r t : ℕ) (i : Fin 2) (w : List Letter) :
    ∀ a ∈ (normal r t ((i,false)::w)).head?, a.2 = false := by
  simp only [normal, start, Bool.false_eq_true, ↓reduceIte]
  cases he : negativeLetters (tail r) with
  | nil =>
      simp only [List.nil_append, inner_head, Prod.fst, Prod.snd,
        Bool.false_eq_true, ↓reduceIte, Option.mem_some_iff]
      rintro a rfl
      rfl
  | cons x L =>
      simp only [List.cons_append, List.head?_cons, Option.mem_some_iff]
      rintro a rfl
      exact negative_sign _ x (by rw [he]; simp)

private theorem negative_conjugate_reduced (r t : ℕ) (i : Fin 2) (w : List Letter)
    (h : FreeGroup.IsReduced ((i,false)::w)) :
    FreeGroup.IsReduced (negativeLetters (valievMarker r t) ++ normal r t ((i,false)::w)) :=
  prepend_same_sign _ _ false (negative_sign _) (normal_reduced r t _ h)
    (normal_negative_head r t i w)

private theorem positiveLetters_of_signs (w : List Letter)
    (h : ∀ x ∈ w, x.2 = true) : w = positiveLetters (w.map Prod.fst) := by
  simp only [positiveLetters, List.map_map]
  conv_lhs => rw [← List.map_id w]
  apply List.map_congr_left
  intro a ha
  rcases a with ⟨i,b⟩
  simp only [id_eq, Function.comp_apply, Prod.fst, Prod.mk.injEq, true_and]
  exact h (i,b) ha

private theorem inner_positive (r t : ℕ) (hr : 2 ≤ r) (i : Fin 2) (v : PositiveWord) :
    inner r t (i,true) (positiveLetters v) =
      positiveLetters (branch i ++ tail r ++ v.flatMap (valievCode r) ++ valievMarker r t) := by
  induction v generalizing i with
  | nil => simp [positiveLetters, inner, lastPart]
  | cons j v ih =>
      simp only [positiveLetters, List.map_cons] at *
      rw [inner, ih]
      simp [signedBranch, gap, positiveLetters, List.flatMap_cons, code_split r hr,
        List.map_append, List.append_assoc]

private theorem trimmed_marker_suffix (r t : ℕ) (hr : 2 ≤ r)
    (i : Fin 2) (w : List Letter) (hw : ∀ a ∈ w, a.2 = true) :
    positiveLetters (valievMarker r t) <:+ trimmed r t i w := by
  have hi := inner_positive r t hr i (w.map Prod.fst)
  rw [← positiveLetters_of_signs w hw] at hi
  unfold trimmed
  rw [hi]
  fin_cases i <;> simp [branch, positiveLetters, List.map_append]
  all_goals
    simp only [← List.cons_append, ← List.append_assoc]
    exact List.suffix_append ..

/-- The reduced conjugate of a nontrivial code word has a marker at one end
of its negative-positive spelling. Thus an equality between positive words
forces at least one of those words to end in the literal marker. -/
theorem marker_suffix_alternative (r t : ℕ) (hr : 2 ≤ r)
    (g : FreeGroup (Fin 2)) (hg : g ≠ 1) (W V : PositiveWord)
    (h : positiveFree W * (positiveFree (valievMarker r t))⁻¹ * codeLift r g *
      positiveFree (valievMarker r t) = positiveFree V) :
    valievMarker r t <:+ W ∨ valievMarker r t <:+ V := by
  have he : (positiveFree (valievMarker r t))⁻¹ * codeLift r g *
      positiveFree (valievMarker r t) = (positiveFree W)⁻¹ * positiveFree V := by
    rw [← h]
    group
  rcases fraction_normal W V with ⟨X,A,B,hW,hV,hfraction⟩
  cases hw : g.toWord with
  | nil => exact False.elim (hg (FreeGroup.toWord_eq_nil_iff.mp hw))
  | cons a w =>
      rcases a with ⟨i,b⟩
      have hred : FreeGroup.IsReduced ((i,b)::w) := hw ▸ FreeGroup.isReduced_toWord
      have hmk : FreeGroup.mk ((i,b)::w) = g := by rw [← hw]; exact FreeGroup.mk_toWord
      cases b
      · left
        have hn := negative_conjugate_reduced r t i w hred
        have hev : FreeGroup.mk (negativeLetters (valievMarker r t) ++ normal r t ((i,false)::w)) =
            (positiveFree W)⁻¹ * positiveFree V := by
          rw [← FreeGroup.mul_mk, mk_negativeLetters, normal_eval r t hr, hmk]
          simpa only [mul_assoc] using he
        have heq := congrArg FreeGroup.toWord hev
        rw [FreeGroup.toWord_mk, hn.reduce_eq, hfraction] at heq
        have hp : negativeLetters (valievMarker r t) <+: negativeLetters A ++ positiveLetters B := by
          rw [← heq]
          exact List.prefix_append ..
        have hp' := negative_prefix _ _ _ (negative_sign _) (positive_sign _) hp
        have hPA := (negativeLetters_prefix_iff _ _).mp hp'
        rw [hW]
        exact hPA.trans (List.suffix_append ..)
      · right
        have hn := positive_conjugate_reduced r t i w hred
        have hev : FreeGroup.mk (negativeLetters (markerCut r t i) ++ trimmed r t i w) =
            (positiveFree W)⁻¹ * positiveFree V := by
          rw [positive_conjugate_eval r t hr, hmk]
          exact he
        have heq := congrArg FreeGroup.toWord hev
        rw [FreeGroup.toWord_mk, hn.reduce_eq, hfraction] at heq
        have hp := fraction_signs A B
        rw [← heq] at hp
        have htrim := all_positive_of_pairwise_head (trimmed r t i w)
          ((List.pairwise_append.mp hp).2.1) ⟨1, trimmed_head r t i w⟩
        have hi : ∀ a ∈ inner r t (i,true) w, a.2 = true := by
          rw [inner_trimmed]
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · split_ifs at ha
            · simp at ha
            · simp only [List.mem_singleton] at ha
              subst a
              rfl
          · exact htrim a ha
        have hws : ∀ a ∈ w, a.2 = true := by
          intro a ha
          exact inner_signs r t (i,true) w hi a (by simp [ha])
        have hs := trimmed_marker_suffix r t hr i w hws
        have hs' : positiveLetters (valievMarker r t) <:+ negativeLetters A ++ positiveLetters B := by
          rw [← heq]
          exact hs.trans (List.suffix_append ..)
        have hPB := (positiveLetters_suffix_iff _ _).mp
          (positive_suffix _ _ _ (positive_sign _) (negative_sign _) hs')
        rw [hV]
        exact hPB.trans (List.suffix_append ..)

/-- Prefix decoding upgrades the marker-suffix alternative to the original
coded recognition language. This is the signed separator step in Valiev's
intersection argument. -/
theorem coded_marker_of_separator {G : PreparedInput} (D : ValievDatum G)
    (g : FreeGroup (Fin 2)) (hg : g ≠ 1) (W V : PositiveWord)
    (hW : PositiveEq D.toCodeWords.rules W D.P)
    (hV : PositiveEq D.toCodeWords.rules V D.P)
    (h : positiveFree W * (positiveFree D.P)⁻¹ * codeLift D.r g *
      positiveFree D.P = positiveFree V) :
    ∃ v : PositiveWord, W = v.flatMap D.code ++ D.P ∧ PositiveEq G.monoidRules v [] := by
  have hs := marker_suffix_alternative D.r D.t D.r_ge_two g hg W V
    (by simpa only [D.marker_shape] using h)
  rw [← D.marker_shape] at hs
  have hshape : ∃ v : PositiveWord, W = v.flatMap D.code ++ D.P := by
    rcases hs with hs | hs
    · rcases hs with ⟨u, hu⟩
      have huW : PositiveEq D.toCodeWords.rules (u ++ D.P) D.P := hu ▸ hW
      rcases D.prefix_decoding u huW with ⟨v, hv⟩
      exact ⟨v, by rw [← hu, hv]⟩
    · rcases hs with ⟨u, hu⟩
      have huV : PositiveEq D.toCodeWords.rules (u ++ D.P) D.P := hu ▸ hV
      rcases D.prefix_decoding u huV with ⟨v, hv⟩
      have hVshape : V = v.flatMap (valievCode D.r) ++ D.P := by
        rw [← hu, hv, D.code_shape]
      have hc : codeLift D.r (positiveFree v * g⁻¹) *
          positiveFree (valievMarker D.r D.t) = positiveFree W := by
        rw [map_mul, map_inv, codeLift_positive, ← D.marker_shape]
        have he : positiveFree W * (positiveFree D.P)⁻¹ * codeLift D.r g *
            positiveFree D.P = positiveFree (v.flatMap (valievCode D.r)) * positiveFree D.P := by
          rw [← positiveFree_append, ← hVshape]
          exact h
        have he' := congrArg (fun z => z * (positiveFree D.P)⁻¹ *
          (codeLift D.r g)⁻¹ * positiveFree D.P) he
        group at he'
        simpa only [zpow_neg_one] using he'.symm
      rcases code_mul_marker_positive D.r D.t D.r_ge_two _ W hc with ⟨v', _, hv'⟩
      exact ⟨v', by simpa only [D.code_shape, D.marker_shape] using hv'⟩
  rcases hshape with ⟨v,hv⟩
  refine ⟨v,hv,(D.recognizes v).mpr ?_⟩
  rw [← hv]
  exact hW

end
end UniversalGroup.CodeCancellation
