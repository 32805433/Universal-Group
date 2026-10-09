module

public import UniversalGroup.Higman.Recognizer.FiniteAlphabet
public import UniversalGroup.Higman.Recognizer.Triangular
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Fresh input and boundary aliases, followed by binary triangularization.
The aliases are distinct from every machine symbol. -/
namespace UniversalGroup.HigmanMarkedSource
open Thue Coding.SourceMarker
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ} {language : List (Fin k) → Prop}
variable (D : HigmanFiniteRecognizer.Data k language)

abbrev Alias (k : ℕ) := Fin k ⊕ Fin 2
abbrev Alphabet := D.Alphabet ⊕ Alias k
abbrev Rule := D.rules ⊕ Alias k

local instance : Fintype D.Alphabet := @Fintype.ofFinite D.Alphabet D.finiteAlphabet
local instance : Fintype D.rules := D.finiteRules.fintype

abbrev old (a : D.Alphabet) : Alphabet D := Sum.inl a
abbrev aliasSymbol (a : Alias k) : Alphabet D := Sum.inr a
abbrev input (i : Fin k) : Alphabet D := aliasSymbol D (.inl i)
abbrev left : Alphabet D := aliasSymbol D (.inr 0)
abbrev right : Alphabet D := aliasSymbol D (.inr 1)

def aliasWord : Alias k → List D.Alphabet
  | .inl i => D.code i
  | .inr i => ![D.left,D.right] i

def lhs : Rule D → List (Alphabet D)
  | .inl p => p.val.1.map (old D)
  | .inr a => [aliasSymbol D a]

def rhs : Rule D → List (Alphabet D)
  | .inl p => p.val.2.map (old D)
  | .inr a => (aliasWord D a).map (old D)

def rules : ThueSystem (Alphabet D) := Set.range (fun p => (lhs D p,rhs D p))

def decodeSymbol : Alphabet D → List D.Alphabet
  | .inl a => [a]
  | .inr a => aliasWord D a

def decode (w : List (Alphabet D)) : List D.Alphabet := w.flatMap (decodeSymbol D)

@[simp] theorem decode_old (w : List D.Alphabet) : decode D (w.map (old D)) = w := by
  simp [decode,List.flatMap_map,decodeSymbol]

theorem source_forward {u v : List D.Alphabet} (h : ThueEq D.rules u v) :
    ThueEq (rules D) (u.map (old D)) (v.map (old D)) := by
  have hh := substitute_eq (fun a => [old D a]) (T := rules D) (S := D.rules) ?_ h
  · simpa only [←List.map_eq_flatMap] using hh
  · intro x y hxy
    simpa only [lhs, rhs, ←List.map_eq_flatMap] using
      (relation_eq (S := rules D) ⟨Sum.inl ⟨(x,y),hxy⟩,rfl⟩)

theorem rule_decode (p : Rule D) : ThueEq D.rules (decode D (lhs D p)) (decode D (rhs D p)) := by
  cases p with
  | inl p => simp only [lhs,rhs,decode_old]; exact relation_eq p.property
  | inr a =>
      change ThueEq D.rules (aliasWord D a ++ []) (decode D ((aliasWord D a).map (old D)))
      rw [List.append_nil,decode_old]
      exact Relation.ReflTransGen.refl

theorem reflection {u v : List (Alphabet D)} (h : ThueEq (rules D) u v) :
    ThueEq D.rules (decode D u) (decode D v) := by
  apply substitute_eq (decodeSymbol D) ?_ h
  rintro x y ⟨p,hp⟩
  cases hp
  exact rule_decode D p

theorem symbol_expand (a : Alphabet D) :
    ThueEq (rules D) [a] ((decodeSymbol D a).map (old D)) := by
  cases a with
  | inl a => exact Relation.ReflTransGen.refl
  | inr a => exact relation_eq ⟨Sum.inr a,rfl⟩

theorem expand (w : List (Alphabet D)) :
    ThueEq (rules D) w ((decode D w).map (old D)) := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | cons a w ih =>
      have h₁ := thueEq_context [] w (symbol_expand D a)
      have h₂ := thueEq_context ((decodeSymbol D a).map (old D)) [] ih
      exact h₁.trans (by simpa [ThueEq, decode,List.map_append] using h₂)

theorem equivalence (u v : List (Alphabet D)) :
    ThueEq (rules D) u v ↔ ThueEq D.rules (decode D u) (decode D v) := by
  refine ⟨reflection D, fun h => ?_⟩
  exact (expand D u).trans ((source_forward D h).trans (thueEq_symm (expand D v)))

def marked (w : List (Fin k)) : List (Alphabet D) := [left D] ++ w.map (input D) ++ [right D]

@[simp] theorem decode_marked (w : List (Fin k)) :
    decode D (marked D w) = D.left ++ w.flatMap D.code ++ D.right := by
  simp [decode,marked,List.flatMap_map,decodeSymbol,aliasWord, left, right, aliasSymbol]

/-- The machine is queried only on the newly introduced literal input and
boundary aliases. -/
theorem recognizes (hempty : language []) (w : List (Fin k)) :
    language w ↔ ThueEq (rules D) (marked D w) (marked D []) := by
  have he := (D.recognizes []).mp hempty
  simp only [List.flatMap_nil,List.append_nil] at he
  rw [equivalence,decode_marked,decode_marked]
  simp only [List.flatMap_nil,List.append_nil]
  constructor
  · exact fun h => ((D.recognizes w).mp h).trans (thueEq_symm he)
  · exact fun h => (D.recognizes w).mpr (h.trans he)

theorem aliasWord_nonempty (a : Alias k) : aliasWord D a ≠ [] := by
  cases a with
  | inl i => exact D.code_nonempty i
  | inr i => fin_cases i <;> first | exact D.left_nonempty | exact D.right_nonempty

theorem lhs_nonempty (p : Rule D) : lhs D p ≠ [] := by
  cases p with
  | inl p => simpa [lhs] using (D.nonemptyRules p.val p.property).1
  | inr a => simp [lhs]

theorem rhs_nonempty (p : Rule D) : rhs D p ≠ [] := by
  cases p with
  | inl p => simpa [rhs] using (D.nonemptyRules p.val p.property).2
  | inr a => simpa [rhs] using aliasWord_nonempty D a

abbrev TriAlphabet := HigmanTriangular.Alphabet (lhs D) (rhs D)
abbrev TriRow := HigmanTriangular.Row (lhs D) (rhs D)

abbrev triRules := HigmanTriangular.rules (lhs D) (rhs D)
abbrev triLift := HigmanTriangular.lift (lhs D) (rhs D)

abbrev paired (a : Alias k) (b : Fin 2) : TriAlphabet D :=
  HigmanTriangular.base (lhs D) (rhs D) (aliasSymbol D a,b)

/-- Each input and boundary alias becomes its own disjoint pair of letters. -/
theorem paired_injective : Function.Injective (fun p : Alias k × Fin 2 => paired D p.1 p.2) := by
  rintro ⟨a,b⟩ ⟨a',b'⟩ h
  simpa only [paired, HigmanTriangular.base, aliasSymbol, Sum.inl.injEq, Prod.mk.injEq, Sum.inr.injEq] using h

theorem triangular_recognizes (hempty : language []) (w : List (Fin k)) :
    language w ↔ ThueEq (triRules D) (triLift D (marked D w)) (triLift D (marked D [])) :=
  (recognizes D hempty w).trans
    (HigmanTriangular.equivalence (lhs D) (rhs D) (lhs_nonempty D) (rhs_nonempty D) _ _)

instance triAlphabetFintype : Fintype (TriAlphabet D) := inferInstance
instance triRowFintype : Fintype (TriRow D) := inferInstance

theorem triRow_nonempty : Nonempty (TriRow D) := by
  let p : Rule D := Sum.inr (Sum.inr 0)
  have hp := HigmanTriangular.side_length (lhs D) (rhs D) (lhs_nonempty D) (rhs_nonempty D) p false
  exact ⟨⟨p,false,⟨0,by omega⟩⟩⟩

end
end UniversalGroup.HigmanMarkedSource
