module

public import UniversalGroup.Embedding.ProtectedInput
public import UniversalGroup.Embedding.ProtectedInput.MarkedQuotient
public import UniversalGroup.Embedding.ProtectedInput.ProtectedAction

@[expose] public section

/-!
# Positive preparation with a protected row triple

The reflection-based preparation retains a marked map to every pair `u,v` satisfying
`(u*v)²=1`.  The four-state action supplies such a pair in row coordinates,
and detects the required free triple.  The faithful input embedding comes
from the reflection-based preparation; the detecting map need not be injective.
-/

namespace UniversalGroup.Embedding

noncomputable section

private theorem protected_pair_relation :
    ((ProtectedAction.b ^ 2 * ProtectedAction.c * (ProtectedAction.b ^ 2)⁻¹) *
      (ProtectedAction.b⁻¹ * ProtectedAction.c * ProtectedAction.b)) ^ 2 = 1 := by
  have he : (ProtectedAction.b ^ 2 * ProtectedAction.c * (ProtectedAction.b ^ 2)⁻¹) *
      (ProtectedAction.b⁻¹ * ProtectedAction.c * ProtectedAction.b) =
      ProtectedAction.b ^ 2 *
        (ProtectedAction.c * (ProtectedAction.b ^ 3)⁻¹ * ProtectedAction.c * ProtectedAction.b ^ 3) *
        (ProtectedAction.b ^ 2)⁻¹ := by simp only [pow_two]; group
  rw [he]
  calc
    _ = ProtectedAction.b ^ 2 *
        (ProtectedAction.c * (ProtectedAction.b ^ 3)⁻¹ * ProtectedAction.c * ProtectedAction.b ^ 3) ^ 2 *
        (ProtectedAction.b ^ 2)⁻¹ := by simp only [pow_two]; group
    _ = 1 := by rw [ProtectedAction.relation]; group

/-- Every finite presentation embeds in a positive prepared input whose row
group contains the specified free triple `b,cbc⁻¹,c³`. -/
theorem prepare_protected_input (Q : FP n m) :
    ∃ G : PreparedInput,
      Nonempty (GroupEmbedding Q.Group G.presentation.Group) ∧ ProtectedRowTriple G := by
  let B := ProtectedAction.b
  let C := ProtectedAction.c
  obtain ⟨G, hG, f, hf⟩ := MarkedQuotient.exists_prepared_with_values Q
    (B ^ 2 * C * (B ^ 2)⁻¹) (B⁻¹ * C * B) protected_pair_relation
  have hr (i : Fin G.relatorCount) :
      Word.eval ![B,C] ((rowPresentation G).relator i) = 1 := by
    change Word.eval ![B,C]
      (Word.substitute RowWords.input (G.presentation.relator i)) = 1
    rw [Word.eval_substitute]
    have hh := congrArg f (G.presentation.relator_eq_one i)
    rw [map_one, FP.evalWord, Word.map_eval] at hh
    convert hh using 1
    congr 1
    funext j
    simp only [RowWords.eval_input, Matrix.cons_val_zero, Matrix.cons_val_one,
      Function.comp_apply]
    exact (hf j).symm
  let r := (rowPresentation G).homOfRelators ![B,C] hr
  have hcomp : r.comp (rowTriple G) = ProtectedAction.triple := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;>
      simp [r, rowTriple, rowGeneratorB, rowGeneratorC, generators,
        ProtectedAction.triple, B, C]
  refine ⟨G, hG, ?_⟩
  intro x y hxy
  apply ProtectedAction.triple_injective
  simpa only [← MonoidHom.comp_apply, hcomp] using congrArg r hxy

end
end UniversalGroup.Embedding
