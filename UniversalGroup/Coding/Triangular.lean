module

public import UniversalGroup.Coding.SourceMarker
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Triangularize the source marker semigroup while making every auxiliary
letter represent a word containing the marker. This preserves literal prefix decoding. -/
namespace UniversalGroup.Coding.Triangular
open Thue
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
local instance {α : Type*} (S : ThueSystem α) : Trans (ThueEq S) (ThueEq S) (ThueEq S) :=
  ⟨Relation.ReflTransGen.trans⟩

variable (G : PreparedInput)
abbrev Position := Σ i : Fin G.relatorCount, Fin (G.relators i).length
abbrev Extra := Position G ⊕ Fin 2
abbrev Alphabet := Fin 3 ⊕ Extra G
abbrev RuleIndex := Position G ⊕ (Fin 2 × Bool)

def old (x : Fin 3) : Alphabet G := Sum.inl x
def letter (i : Fin 2) : Alphabet G := old G (SourceMarker.letter i)
def marker : Alphabet G := old G SourceMarker.marker
def lift (w : PositiveWord) : List (Alphabet G) := w.map (letter G)
def oldWord (w : List (Fin 3)) : List (Alphabet G) := w.map (old G)

@[simp] theorem oldWord_append (v w : List (Fin 3)) :
    oldWord G (v++w) = oldWord G v ++ oldWord G w := by simp [oldWord]
@[simp] theorem oldWord_single (x : Fin 3) : oldWord G [x] = [old G x] := rfl

def tailSymbol (i : Fin G.relatorCount) (k : ℕ) : Alphabet G :=
  if h : k < (G.relators i).length then Sum.inr (Sum.inl ⟨i,⟨k,h⟩⟩) else marker G

def headSymbol (i : Fin G.relatorCount) (k : ℕ) : Alphabet G :=
  if k = 0 then marker G else tailSymbol G i k

def lhs : RuleIndex G → Alphabet G
  | .inl ⟨i,j⟩ => headSymbol G i j.val
  | .inr (i,_) => Sum.inr (Sum.inr i)

def rhs : RuleIndex G → Alphabet G × Alphabet G
  | .inl ⟨i,j⟩ => (letter G ((G.relators i).get j),tailSymbol G i (j.val+1))
  | .inr (i,b) => if b then (marker G,letter G i) else (letter G i,marker G)

def rules : ThueSystem (Alphabet G) :=
  Set.range fun i => ([lhs G i],[ (rhs G i).1, (rhs G i).2 ])

def decodeSymbol : Alphabet G → List (Fin 3)
  | .inl x => [x]
  | .inr (.inl ⟨i,j⟩) => SourceMarker.lift ((G.relators i).drop j.val) ++ [SourceMarker.marker]
  | .inr (.inr i) => [SourceMarker.letter i,SourceMarker.marker]
def decode (w : List (Alphabet G)) : List (Fin 3) := w.flatMap (decodeSymbol G)

@[simp] theorem decode_old (x : Fin 3) : decodeSymbol G (old G x) = [x] := rfl
@[simp] theorem decode_marker : decodeSymbol G (marker G) = [SourceMarker.marker] := rfl
@[simp] theorem decode_letter (i : Fin 2) : decodeSymbol G (letter G i) = [SourceMarker.letter i] := rfl
@[simp] theorem decode_append (v w : List (Alphabet G)) : decode G (v++w) = decode G v ++ decode G w := by
  simp [decode]
@[simp] theorem decode_oldWord (w : List (Fin 3)) : decode G (oldWord G w) = w := by
  simp [decode,oldWord,List.flatMap_map]
@[simp] theorem decode_lift (w : PositiveWord) : decode G (lift G w) = SourceMarker.lift w := by
  simp [decode,lift,SourceMarker.lift,List.flatMap_map,← List.map_eq_flatMap]
@[simp] theorem oldWord_lift (w : PositiveWord) : oldWord G (SourceMarker.lift w) = lift G w := by
  simp [oldWord,SourceMarker.lift,lift,letter,List.map_map,Function.comp_def]

@[simp] theorem decode_tail (i : Fin G.relatorCount) (k : ℕ) :
    decodeSymbol G (tailSymbol G i k) =
      SourceMarker.lift ((G.relators i).drop k) ++ [SourceMarker.marker] := by
  unfold tailSymbol
  split_ifs with hk
  · rfl
  · rw [List.drop_eq_nil_of_le (by omega)]
    rfl

theorem decode_rhs (i : Fin G.relatorCount) (j : Fin (G.relators i).length) :
    decode G [(rhs G (.inl ⟨i,j⟩)).1,(rhs G (.inl ⟨i,j⟩)).2] =
      SourceMarker.lift ((G.relators i).drop j.val) ++ [SourceMarker.marker] := by
  simp only [rhs,decode,List.flatMap_cons,List.flatMap_nil,List.append_nil,decode_letter,decode_tail]
  rw [List.drop_eq_getElem_cons j.isLt]
  rfl

theorem decode_relation (i : RuleIndex G) :
    ThueEq (SourceMarker.rules G) (decode G [lhs G i])
      (decode G [(rhs G i).1,(rhs G i).2]) := by
  rcases i with ⟨i,j⟩ | ⟨i,b⟩
  · rw [decode_rhs]
    by_cases hj : j.val = 0
    · simpa [lhs,headSymbol,hj,decode,SourceMarker.lift] using
        thueEq_symm (SourceMarker.primary G i)
    · simp only [lhs,headSymbol,ite_eq_right hj,decode,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,decode_tail]
      exact Relation.ReflTransGen.refl
  · cases b
    · exact Relation.ReflTransGen.refl
    · exact SourceMarker.shift G i

theorem reflection {X Y : List (Alphabet G)} (h : ThueEq (rules G) X Y) :
    ThueEq (SourceMarker.rules G) (decode G X) (decode G Y) := by
  apply SourceMarker.substitute_eq (decodeSymbol G) ?_ h
  rintro x y ⟨i,hi⟩
  rcases Prod.mk.inj hi with ⟨rfl,rfl⟩
  exact decode_relation G i

/-- Expanding a suffix auxiliary spells the remaining original relator and marker. -/
theorem expand (i : Fin G.relatorCount) (k : ℕ) :
    ThueEq (rules G) [headSymbol G i k] (lift G ((G.relators i).drop k) ++ [marker G]) := by
  by_cases hk : k < (G.relators i).length
  · let j : Fin (G.relators i).length := ⟨k,hk⟩
    have hstep := SourceMarker.relation_eq (S := rules G) ⟨Sum.inl ⟨i,j⟩,rfl⟩
    have hi := expand i (k+1)
    have hi' : ThueEq (rules G) [tailSymbol G i (k+1)]
        (lift G ((G.relators i).drop (k+1)) ++ [marker G]) := by
      simpa only [headSymbol,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte] using hi
    have hc := thueEq_context [letter G ((G.relators i).get j)] [] hi'
    have he := hstep.trans (by simpa only [ThueEq,rhs,j,List.singleton_append,List.append_nil] using hc)
    simpa only [ThueEq,lhs,j,List.drop_eq_getElem_cons hk,lift,List.map_cons,List.cons_append,List.get_eq_getElem] using he
  · have he : headSymbol G i k = marker G := by
      simp [headSymbol,tailSymbol,hk]
    rw [he,List.drop_eq_nil_of_le (by omega)]
    exact Relation.ReflTransGen.refl
termination_by (G.relators i).length - k

theorem primary (i : Fin G.relatorCount) :
    ThueEq (rules G) (lift G (G.relators i) ++ [marker G]) [marker G] := by
  simpa [headSymbol] using thueEq_symm (expand G i 0)

theorem shift (i : Fin 2) :
    ThueEq (rules G) [letter G i,marker G] [marker G,letter G i] := by
  have h₁ := SourceMarker.relation_eq (S := rules G) ⟨Sum.inr (i,false),rfl⟩
  have h₂ := SourceMarker.relation_eq (S := rules G) ⟨Sum.inr (i,true),rfl⟩
  exact (thueEq_symm h₁).trans h₂

theorem forward {X Y : List (Fin 3)} (h : ThueEq (SourceMarker.rules G) X Y) :
    ThueEq (rules G) (oldWord G X) (oldWord G Y) := by
  have hm : ∀ x y, (x,y) ∈ SourceMarker.rules G →
      ThueEq (rules G) (oldWord G x) (oldWord G y) := by
    rintro x y ⟨i,hi⟩
    rcases Prod.mk.inj hi with ⟨rfl,rfl⟩
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [SourceMarker.left_primary,SourceMarker.right_primary,oldWord_append,
        oldWord_lift,oldWord_single,marker] using primary G j
    · intro j
      simpa only [SourceMarker.left_shift,SourceMarker.right_shift,oldWord,
        List.map_cons,List.map_nil,letter,marker] using shift G j
  simpa only [← List.map_eq_flatMap,oldWord] using
    SourceMarker.substitute_eq (T := rules G) (fun x => [old G x])
      (by simpa only [← List.map_eq_flatMap,oldWord] using hm) h

theorem recognizes (w : PositiveWord) :
    PositiveEq G.monoidRules w [] ↔ ThueEq (rules G) (lift G w ++ [marker G]) [marker G] := by
  constructor
  · intro h
    simpa only [oldWord_append,oldWord_lift,oldWord_single,marker] using forward G ((SourceMarker.recognizes G w).1 h)
  · intro h
    apply (SourceMarker.recognizes G w).2
    have hh := reflection G h
    rw [decode_append,decode_lift] at hh
    simpa only [decode,List.flatMap_cons,List.flatMap_nil,decode_marker,List.append_nil] using hh

/-- Only an original input letter can have marker-free decoding. -/
theorem decodeSymbol_zero {a : Alphabet G}
    (h : (decodeSymbol G a).count SourceMarker.marker = 0) :
    ∃ i : Fin 2, a = letter G i := by
  rcases a with x | (⟨i,j⟩ | i)
  · fin_cases x
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · change (1 : ℕ) = 0 at h
      omega
  · simp only [decodeSymbol,List.count_append,List.count_singleton_self] at h
    omega
  · simp only [decodeSymbol,List.count_cons] at h
    simp [Ne.symm (SourceMarker.marker_ne_letter i)] at h

theorem decode_zero {v : List (Alphabet G)}
    (h : (decode G v).count SourceMarker.marker = 0) :
    ∃ w : PositiveWord, v = lift G w := by
  induction v with
  | nil => exact ⟨[],rfl⟩
  | cons a v ih =>
      have hc : (decodeSymbol G a).count SourceMarker.marker +
          (decode G v).count SourceMarker.marker = 0 := by
        simpa only [decode,List.flatMap_cons,List.count_append] using h
      obtain ⟨ha,hv⟩ := Nat.add_eq_zero_iff.mp hc
      obtain ⟨i,rfl⟩ := decodeSymbol_zero G ha
      obtain ⟨w,rfl⟩ := ih hv
      exact ⟨i::w,rfl⟩

/-- Prefix decoding survives triangularization because every fresh letter
has strictly positive marker multiplicity under the source projection. -/
theorem prefix_decoding (v : List (Alphabet G))
    (h : ThueEq (rules G) (v ++ [marker G]) [marker G]) :
    ∃ w : PositiveWord, v = lift G w ∧ PositiveEq G.monoidRules w [] := by
  have hh := SourceMarker.count_marker_eq G (reflection G h)
  have hz : (decode G v).count SourceMarker.marker = 0 := by
    simpa only [decode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      decode_marker,List.append_nil,List.count_append,List.count_singleton_self,
      Nat.add_eq_right] using hh
  obtain ⟨w,hw⟩ := decode_zero G hz
  refine ⟨w,hw,(recognizes G w).2 ?_⟩
  rwa [← hw]

end UniversalGroup.Coding.Triangular
