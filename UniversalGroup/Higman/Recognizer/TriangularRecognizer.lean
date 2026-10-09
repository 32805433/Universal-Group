module

public import UniversalGroup.Higman.Recognizer.MarkedSource
public import UniversalGroup.Higman.Recognizer.Code
public import UniversalGroup.Coding.BooneCollins.Theorem
public import UniversalGroup.Coding.BooneCollins.Rules

@[expose] public section

/-! A finite triangular source recognizer with a positive input retraction.
This is the computation interface used by the Higman embedding assembly. -/
namespace UniversalGroup.HigmanTriangularRecognizer
open Thue Coding.SourceMarker HigmanMarkedSource
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

structure Data (k : ℕ) (language : List (Fin k) → Prop) where
  r : ℕ
  t : ℕ
  r_ge_three : 3 ≤ r
  lhs : Fin (2^t) → Fin r
  rhs : Fin (2^t) → Fin r × Fin r
  input : HigmanCode.Input (Fin k) r
  recognizes : ∀ w, language w ↔
    ThueEq (BooneCollinsTheorem.sourceSystem r t lhs rhs)
      (input.left ++ w.flatMap input.words ++ input.right) (input.left ++ input.right)

namespace Build
variable {k : ℕ} {language : List (Fin k) → Prop}
variable (D : HigmanFiniteRecognizer.Data k language)

abbrev r := Fintype.card (TriAlphabet D)
abbrev t := Fintype.card (TriRow D)
def alphabetEquiv : TriAlphabet D ≃ Fin (r D) := Fintype.equivFin _
def rowEquiv : TriRow D ≃ Fin (t D) := Fintype.equivFin _

theorem t_pos : 0 < t D := Fintype.card_pos_iff.mpr (triRow_nonempty D)

def row (i : Fin (2^t D)) : TriRow D :=
  (rowEquiv D).symm (if h : i.val < t D then ⟨i.val,h⟩ else ⟨0,t_pos D⟩)

theorem row_surjective : Function.Surjective (row D) := by
  intro p
  let j := rowEquiv D p
  refine ⟨⟨j.val,lt_trans j.isLt Nat.lt_two_pow_self⟩,?_⟩
  simp only [row, dite_eq_left j.isLt]
  exact (rowEquiv D).symm_apply_apply p

def lhs (i : Fin (2^t D)) : Fin (r D) :=
  alphabetEquiv D (HigmanTriangular.rowLeft (HigmanMarkedSource.lhs D) (HigmanMarkedSource.rhs D) (row D i))

def rhs (i : Fin (2^t D)) : Fin (r D) × Fin (r D) :=
  let p := HigmanTriangular.rowRight (HigmanMarkedSource.lhs D) (HigmanMarkedSource.rhs D) (row D i)
  (alphabetEquiv D p.1,alphabetEquiv D p.2)

def system : ThueSystem (Fin (r D)) :=
  BooneCollinsTheorem.sourceSystem (r D) (t D) (lhs D) (rhs D)

theorem row_forward (p : TriRow D) :
    ([(alphabetEquiv D) (HigmanTriangular.rowLeft (HigmanMarkedSource.lhs D) (HigmanMarkedSource.rhs D) p)],
      [(alphabetEquiv D) (HigmanTriangular.rowRight (HigmanMarkedSource.lhs D) (HigmanMarkedSource.rhs D) p).1,
       (alphabetEquiv D) (HigmanTriangular.rowRight (HigmanMarkedSource.lhs D) (HigmanMarkedSource.rhs D) p).2]) ∈ system D := by
  obtain ⟨i,hi⟩ := row_surjective D p
  exact ⟨i,by simp [lhs,rhs,hi]⟩

theorem rename_forward {u v : List (TriAlphabet D)} (h : ThueEq (triRules D) u v) :
    ThueEq (system D) (u.map (alphabetEquiv D)) (v.map (alphabetEquiv D)) := by
  have hh := substitute_eq (fun a => [alphabetEquiv D a]) (S := triRules D) (T := system D) ?_ h
  · simpa only [←List.map_eq_flatMap] using hh
  · rintro x y ⟨p,hp⟩
    cases hp
    exact relation_eq (row_forward D p)

theorem rename_reflection {u v : List (Fin (r D))} (h : ThueEq (system D) u v) :
    ThueEq (triRules D) (u.map (alphabetEquiv D).symm) (v.map (alphabetEquiv D).symm) := by
  have hh := substitute_eq (fun a => [(alphabetEquiv D).symm a])
    (S := system D) (T := triRules D) ?_ h
  · simpa only [←List.map_eq_flatMap] using hh
  · rintro x y ⟨i,hi⟩
    cases hi
    simpa [lhs,rhs] using
      (relation_eq (S := triRules D) ⟨row D i,rfl⟩)

theorem rename_equivalence (u v : List (TriAlphabet D)) :
    ThueEq (triRules D) u v ↔
      ThueEq (system D) (u.map (alphabetEquiv D)) (v.map (alphabetEquiv D)) := by
  refine ⟨rename_forward D,fun h => ?_⟩
  simpa only [List.map_map,Equiv.symm_comp_self,List.map_id] using rename_reflection D h

def pair (a : Alias k) : List (Fin (r D)) :=
  [alphabetEquiv D (paired D a 0),alphabetEquiv D (paired D a 1)]

def retract (a : Fin (r D)) : List (Fin k) :=
  match (alphabetEquiv D).symm a with
  | .inl (.inr (.inl i), b) => if b=0 then [i] else []
  | _ => []

def input : HigmanCode.Input (Fin k) (r D) where
  words i := pair D (.inl i)
  left := pair D (.inr 0)
  right := pair D (.inr 1)
  retract := retract D
  retract_words i := by simp [pair,retract,paired,aliasSymbol]
  retract_left := by simp [pair,retract,paired,aliasSymbol]
  retract_right := by simp [pair,retract,paired,aliasSymbol]

theorem r_ge_three : 3 ≤ r D := by
  have hh := Fintype.card_le_of_injective (fun p : Alias k × Fin 2 =>
    alphabetEquiv D (paired D p.1 p.2)) ((alphabetEquiv D).injective.comp (paired_injective D))
  have hh' : (k+2)*2 ≤ r D := calc
    (k+2)*2 = Fintype.card (Alias k × Fin 2) := by simp [Alias]
    _ ≤ Fintype.card (Fin (r D)) := hh
    _ = r D := Fintype.card_fin _
  omega


theorem input_endpoint (w : List (Fin k)) :
    (triLift D (marked D w)).map (alphabetEquiv D) =
      (input D).left ++ w.flatMap (input D).words ++ (input D).right := by
  have hword (w : List (Fin k)) :
      (triLift D (w.map (HigmanMarkedSource.input D))).map (alphabetEquiv D)=
        w.flatMap (fun i => pair D (.inl i)) := by
    induction w with
    | nil => rfl
    | cons a w ih =>
        change alphabetEquiv D (paired D (.inl a) 0) ::
          alphabetEquiv D (paired D (.inl a) 1) ::
          (triLift D (w.map (HigmanMarkedSource.input D))).map (alphabetEquiv D) = _
        rw [ih]
        rfl
  change (triLift D ([left D] ++ w.map (HigmanMarkedSource.input D) ++ [right D])).map
    (alphabetEquiv D) = _
  simp only [triLift,HigmanTriangular.lift,HigmanTriangular.doubleWord,
    List.flatMap_append,List.map_append]
  rw [show (((w.map (HigmanMarkedSource.input D)).flatMap HigmanTriangular.doubleLetter).map
    (HigmanTriangular.base (HigmanMarkedSource.lhs D) (HigmanMarkedSource.rhs D))).map
      (alphabetEquiv D)=w.flatMap (fun i=>pair D (.inl i)) from hword w]
  rfl

theorem recognizes (hempty : language []) (w : List (Fin k)) :
    language w ↔ ThueEq (system D)
      ((input D).left ++ w.flatMap (input D).words ++ (input D).right)
      ((input D).left ++ (input D).right) := by
  rw [triangular_recognizes D hempty,rename_equivalence,input_endpoint,input_endpoint]
  simp

def data (hempty : language []) : Data k language where
  r := r D
  t := t D
  r_ge_three := r_ge_three D
  lhs := lhs D
  rhs := rhs D
  input := input D
  recognizes := recognizes D hempty

end Build

/-- A constructed finite triangular recognizer for each recursively enumerable
language containing the empty word. -/
theorem exists_data {k : ℕ} {language : List (Fin k) → Prop}
    (hL : REPred language) (hempty : language []) : Nonempty (Data k language) := by
  obtain ⟨D⟩ := HigmanFiniteRecognizer.exists_data hL
  exact ⟨Build.data D hempty⟩


namespace Data
variable {k : ℕ} {language : List (Fin k) → Prop} (D : Data k language)

/-- The final literal binary three-rule recognizer, ready for the simulator. -/
theorem binary_recognizes (w : List (Fin k)) :
    language w ↔ PositiveEq (BooneCollinsWords.words D.r D.t D.lhs D.rhs).rules
      (D.input.spelling (2*D.t) w) (D.input.marker (2*D.t)) := by
  have h := (D.recognizes w).trans
    ((BooneCollinsTheorem.literal_equivalence D.r D.t D.lhs D.rhs
      (D.input.left ++ w.flatMap D.input.words ++ D.input.right)
      (D.input.left ++ D.input.right)).trans
      (BooneCollinsRules.eq_iff D.r D.t D.lhs D.rhs _ _))
  simpa only [HigmanCode.Input.spelling,HigmanCode.Input.marker,HigmanCode.suffix,
    BooneCollinsNormalForm.finalEndpoint,List.append_assoc] using h

end Data

end
end UniversalGroup.HigmanTriangularRecognizer
