module

public import UniversalGroup.Foundations.Conjugation

@[expose] public section

/-!
# Algebra of the thirteen-relator factor swap

These identities hold in arbitrary groups. They certify the five ordered
generator eliminations and the six deleted relations independently of any
embedding or small-cancellation argument.
-/

namespace UniversalGroup.Embedding

variable {G : Type*} [Group G]

def rowB (c b : G) : G := c * b * c⁻¹
def rowA (c b : G) : G := rowB c b * c ^ 3 * (rowB c b)⁻¹
def finalJ (c r : G) : G := (r ^ 2)⁻¹ * c ^ 2 * r ^ 2
def finalB (c r : G) : G := (finalJ c r)⁻¹ * c ^ 6 * finalJ c r

/-- The fifth conjugacy really defines `b` using only the retained letters
`c,r`; the other four definitions can then be substituted in order. -/
theorem factor_swap_substitutions (c d f k a b r : G)
    (hc : r⁻¹ * c * r = a)
    (hd : r⁻¹ * d * r = k⁻¹ * f * k)
    (hf : r⁻¹ * f * r = rowA c b)
    (hk : r⁻¹ * k * r = rowB c b)
    (hh : r⁻¹ * ((a ^ 2)⁻¹ * (k⁻¹ * f * k) * a ^ 2) ^ 2 * r = b) :
    a = r⁻¹ * c * r ∧ b = finalB c r ∧
      k = r * rowB c b * r⁻¹ ∧
      f = r * rowA c b * r⁻¹ ∧
      k⁻¹ * f * k = r * c ^ 3 * r⁻¹ ∧
      d = r ^ 2 * c ^ 3 * (r ^ 2)⁻¹ := by
  have ha := hc.symm
  have hk' := eq_conjugate_of_inv_conjugate_eq hk
  have hf' := eq_conjugate_of_inv_conjugate_eq hf
  have hx : k⁻¹ * f * k = r * c ^ 3 * r⁻¹ := by
    rw [hk', hf']
    simp only [rowA, rowB]
    group
  have hb : b = finalB c r := by
    rw [← hh, ha, hx]
    simp only [finalB, finalJ, pow_two]
    group
    simp only [zpow_two, mul_assoc]
  refine ⟨ha, hb, hk', hf', hx, ?_⟩
  rw [eq_conjugate_of_inv_conjugate_eq hd, hx]
  simp only [pow_two]
  group

/-- Pull back four cross-commutations and the positive symmetry relation.
The two commutations with `c` are established before they are used to obtain
the two commutations with `d`. -/
theorem factor_swap_deleted_commutations (c d f k a b r : G)
    (hc : r⁻¹ * c * r = a)
    (hd : r⁻¹ * d * r = k⁻¹ * f * k)
    (hf : r⁻¹ * f * r = rowA c b)
    (hk : r⁻¹ * k * r = rowB c b)
    (hh : r⁻¹ * ((a ^ 2)⁻¹ * (k⁻¹ * f * k) * a ^ 2) ^ 2 * r = b)
    (hca : Commute c a) (hab : Commute a b)
    (hbx : Commute b (k⁻¹ * f * k)) :
    Commute c f ∧ Commute c k ∧ Commute d f ∧ Commute d k ∧
      Commute d (((a ^ 2)⁻¹ * (k⁻¹ * f * k) * a ^ 2) ^ 2) := by
  have haB : Commute a (rowB c b) :=
    (hca.symm.mul_right hab).mul_right hca.symm.inv_right
  have haA : Commute a (rowA c b) :=
    (haB.mul_right (hca.symm.pow_right 3)).mul_right haB.inv_right
  have hcf : Commute c f := by
    apply commute_of_inv_conjugates (g := r)
    rw [hc, hf]
    exact haA
  have hck : Commute c k := by
    apply commute_of_inv_conjugates (g := r)
    rw [hc, hk]
    exact haB
  have hcx : Commute c (k⁻¹ * f * k) :=
    (hck.inv_right.mul_right hcf).mul_right hck
  have hxB : Commute (k⁻¹ * f * k) (rowB c b) :=
    (hcx.symm.mul_right hbx.symm).mul_right hcx.symm.inv_right
  have hxA : Commute (k⁻¹ * f * k) (rowA c b) :=
    (hxB.mul_right (hcx.symm.pow_right 3)).mul_right hxB.inv_right
  refine ⟨hcf, hck, ?_, ?_, ?_⟩
  · apply commute_of_inv_conjugates (g := r)
    rw [hd, hf]
    exact hxA
  · apply commute_of_inv_conjugates (g := r)
    rw [hd, hk]
    exact hxB
  · apply commute_of_inv_conjugates (g := r)
    rw [hd, hh]
    exact hbx.symm

/-- The final deletion: `a` commutes with the recovered word for `b` as soon
as `c` commutes with `a = c^r`. No simulator relation is used. -/
theorem final_commutation (c r : G) (hc : Commute c (r⁻¹ * c * r)) :
    Commute (r⁻¹ * c * r) (finalB c r) := by
  have hcc : Commute (r⁻¹ * c * r) ((r ^ 2)⁻¹ * c * r ^ 2) := by
    simpa only [pow_two, mul_inv_rev, inv_inv, mul_assoc] using hc.conj r⁻¹
  have hJ : Commute (r⁻¹ * c * r) (finalJ c r) := by
    unfold finalJ
    convert hcc.pow_right 2 using 1
    simp only [pow_two, mul_inv_rev]
    group
  exact (hJ.inv_right.mul_right (hc.symm.pow_right 6)).mul_right hJ

end UniversalGroup.Embedding
