module

public import UniversalGroup.Embedding.PositiveHost.Model
public import UniversalGroup.Embedding.PositiveHost.ModelLaws

@[expose] public section

/-! All nineteen positive host relators hold in the faithful h/a/b model.
The resulting homomorphism can detect injectivity of maps into the literal presentation.
These concrete model identities are used explicitly; the generic simplification
rules live in `BaseModelLaws`. -/
namespace UniversalGroup.Embedding.PositiveHost.BaseModel
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
variable (G : PreparedInput) (D : ValievDatum G) (hi : ValievIntersections G D)

abbrev value (w : Word 6) : Model G D hi :=
  BaseModelLaws.value D.toCodeWords (sim G D hi) (a G D hi) (b G D hi) w

theorem value_x1 : value G D hi baseWords.x1 =
    (f G D hi)⁻¹ * s1 G D hi * f G D hi := by
  simpa [BaseWords.x1, value, f, k, mul_assoc] using column_one G D hi

theorem value_h : value G D hi baseWords.h = h G D hi := by
  simpa [BaseWords.h, value, f, k, mul_assoc] using column_two G D hi

theorem value_s1 : value G D hi baseWords.s1 = s1 G D hi := by
  simp [BaseWords.s1, f, mul_assoc, value_x1]

theorem value_s2 : value G D hi baseWords.s2 = s2 G D hi :=
  BaseModelLaws.eval_s2_of_conjugates
    (BaseModelLaws.values D.toCodeWords (sim G D hi) (a G D hi) (b G D hi))
    (f G D hi) (h G D hi) (s1 G D hi) (s2 G D hi)
    (BaseModelLaws.value_f _ _ _ _) (value_h G D hi) (value_x1 G D hi) (h_x1 G D hi)

theorem value_e : value G D hi (positiveE baseWords) = e G D hi :=
  BaseModelLaws.eval_e_of_conjugates
    (BaseModelLaws.values D.toCodeWords (sim G D hi) (a G D hi) (b G D hi))
    (f G D hi) (h G D hi) (d G D hi) (e G D hi)
    (BaseModelLaws.value_f _ _ _ _) (value_h G D hi) (BaseModelLaws.value_d _ _ _ _) (h_d G D hi)

theorem value_t : value G D hi baseWords.t = t G D hi :=
  BaseModelLaws.eval_t_of_conjugates
    (BaseModelLaws.values D.toCodeWords (sim G D hi) (a G D hi) (b G D hi))
    (f G D hi) (h G D hi) (t G D hi)
    (BaseModelLaws.value_f _ _ _ _) (value_h G D hi) (h_f G D hi)

theorem value_positive (w : PositiveWord) :
    value G D hi (baseWords.positive w) = positive G D hi w := by
  change Word.eval _ _ = _
  simp only [BaseWords.positive, Word.eval_substitutePositive]
  change (w.map (fun i => if i = 0 then value G D hi baseWords.s1 else value G D hi baseWords.s2)).prod = _
  rw [value_s1, value_s2]
  rfl

theorem value_ell : value G D hi baseWords.ell = ell G D hi := by
  simpa [BaseWords.ell, value, c, mul_assoc] using (substitutions G D hi).1.symm

theorem value_u (i : Fin 2) : value G D hi (baseWords.u i) = u G D hi i := by
  fin_cases i
  · simpa [BaseWords.u, value, c, mul_assoc] using (substitutions G D hi).2.1.symm
  · simpa [BaseWords.u, value, c, mul_assoc] using (substitutions G D hi).2.2.symm

/-- Every expanded letter agrees with the faithful HNN tower. -/
theorem laws : BaseModelLaws.Laws D.toCodeWords (sim G D hi) (a G D hi) (b G D hi) where
  s1 := value_s1 G D hi
  s2 := value_s2 G D hi
  e := value_e G D hi
  t := value_t G D hi
  attachment i := by simpa only [value_positive, value_ell, value_u, f] using attachment G D hi i
  ell_code i := by simpa only [value_positive, value_ell, k] using ell_code G D hi i
  h_square := by simpa only [value_h, d] using d_h_square G D hi
  column_three := by simpa only [value_positive, t, f, k] using column_three G D hi
  c_a := c_a G D hi
  a_b := a_b G D hi
  b_x := b_x G D hi

/-- Interpret the six actual generators in the proper HNN tower. -/
def hom : (positiveBasePresentation D.toCodeWords).Group →* Model G D hi :=
  BaseModelLaws.hom _ _ _ _ (laws G D hi)

theorem hom_generator (i : Fin 6) :
    hom G D hi (generators (positiveBasePresentation D.toCodeWords) i) =
      ![c G D hi,d G D hi,f G D hi,k G D hi,a G D hi,b G D hi] i :=
  BaseModelLaws.hom_generator _ _ _ _ (laws G D hi) i

theorem hom_evalWord (w : Word 6) :
    hom G D hi ((positiveBasePresentation D.toCodeWords).evalWord w) = value G D hi w :=
  BaseModelLaws.hom_evalWord _ _ _ _ (laws G D hi) w

theorem hom_input_word (i : Fin 2) :
    hom G D hi ((positiveBasePresentation D.toCodeWords).evalWord (baseWords.u i)) =
      input G D hi (generators G.presentation i) := by
  rw [hom_evalWord, value_u]
  rfl

end
end UniversalGroup.Embedding.PositiveHost.BaseModel
