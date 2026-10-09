module

public import UniversalGroup.Coding.FiniteSource
public import UniversalGroup.Coding.BooneCollins.Theorem
public import UniversalGroup.Coding.BooneCollins.Rules

@[expose] public section

/-! The explicit Valiev datum, assembled from a triangular marked source and
the literal Boone–Collins three-rule compiler. -/
namespace UniversalGroup.Coding.Completion
open Thue BooneCollinsWords BooneCollinsNormalForm
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable (G : PreparedInput)

abbrev r := FiniteSource.alphabetSize G
abbrev t := FiniteSource.relationCount G

def rowIndex (i : Fin (2^t G)) : Fin (t G) :=
  if h : i.val<t G then ⟨i.val,h⟩ else ⟨0,FiniteSource.relationCount_pos G⟩

theorem rowIndex_surjective : Function.Surjective (rowIndex G) := by
  intro i
  refine ⟨⟨i.val,lt_trans i.isLt Nat.lt_two_pow_self⟩,?_⟩
  simp [rowIndex,i.isLt]

def lhs (i : Fin (2^t G)) : Fin (r G) := FiniteSource.lhs G (rowIndex G i)
def rhs (i : Fin (2^t G)) : Fin (r G) × Fin (r G) := FiniteSource.rhs G (rowIndex G i)

theorem source_eq : BooneCollinsTheorem.sourceSystem (r G) (t G) (lhs G) (rhs G)=
    FiniteSource.rules G := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨rowIndex G i,rfl⟩
  · rintro ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := rowIndex_surjective G i
    exact ⟨j,by simp [lhs,rhs,hj]⟩

def codeWords : CodeWords := words (r G) (t G) (lhs G) (rhs G)

theorem chi_input (w : PositiveWord) :
    chi (r G) (FiniteSource.inputWord G w)=w.flatMap (valievCode (r G)) := by
  simp only [FiniteSource.inputWord,chi,List.flatMap_map]
  congr 1
  funext i
  exact chiLetter_input _ _ i

theorem marker_endpoint : finalEndpoint (r G) (t G) [FiniteSource.marker G]=
    (codeWords G).P := by
  change chiLetter (r G) (FiniteSource.marker G) ++ [] ++ [0] ++
    List.replicate (2*t G) 1=valievMarker (r G) (t G)
  rw [List.append_nil]
  exact chiLetter_marker _ _ (FiniteSource.alphabetSize_ge_three G)

theorem input_endpoint (w : PositiveWord) :
    finalEndpoint (r G) (t G) (FiniteSource.inputWord G w ++ [FiniteSource.marker G])=
      w.flatMap (codeWords G).code ++ (codeWords G).P := by
  rw [finalEndpoint,chi_append,chi_input]
  have hm := marker_endpoint G
  dsimp only [finalEndpoint] at hm
  simp only [List.append_assoc] at hm ⊢
  rw [hm]
  rfl

theorem recognizes (w : PositiveWord) :
    PositiveEq G.monoidRules w [] ↔
      PositiveEq (codeWords G).rules (w.flatMap (codeWords G).code ++ (codeWords G).P)
        (codeWords G).P := by
  rw [FiniteSource.recognizes,←source_eq]
  rw [BooneCollinsTheorem.literal_equivalence]
  rw [input_endpoint,marker_endpoint]
  exact BooneCollinsRules.eq_iff _ _ _ _ _ _

theorem prefix_decoding (v : PositiveWord)
    (h : PositiveEq (codeWords G).rules (v ++ (codeWords G).P) (codeWords G).P) :
    ∃ w : PositiveWord, v=w.flatMap (codeWords G).code := by
  have hh := (BooneCollinsRules.eq_iff (r G) (t G) (lhs G) (rhs G) _ _).mpr h
  rw [←marker_endpoint] at hh
  obtain ⟨u,hu,heq⟩ := BooneCollinsTheorem.literal_prefix _ _ _ _ (FiniteSource.marker G) hh
  rw [source_eq] at heq
  obtain ⟨w,hw,-⟩ := FiniteSource.prefix_decoding G u heq
  refine ⟨w,?_⟩
  rw [hu,hw,chi_input]
  rfl

/-- The complete recognition datum, including the literal code and marker. -/
def datum : ValievDatum G where
  toCodeWords := codeWords G
  r := r G
  t := t G
  r_ge_two := le_trans (by decide) (FiniteSource.alphabetSize_ge_three G)
  code_shape := rfl
  marker_shape := rfl
  E_support := words_E_support _ _ _ _
  F_support := words_F_support _ _ _ _
  P_support := valievMarker_support _ _
  recognizes := recognizes G
  prefix_decoding := prefix_decoding G

end
end UniversalGroup.Coding.Completion

namespace UniversalGroup

/-- Construct the three rewriting rules and the literal Valiev codewords,
with recognition, arbitrary-prefix decoding, and both-letter support. -/
theorem exists_valievDatum (G : PreparedInput) : Nonempty (ValievDatum G) :=
  ⟨Coding.Completion.datum G⟩

end UniversalGroup
