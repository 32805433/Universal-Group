module

public import UniversalGroup.Foundations.Presentation
public import UniversalGroup.Foundations.FinitePresentation.Extensions
public import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section

/-!
# Finite presentations on a prescribed finite generating set

The kernel of any surjection from a free group of finite rank onto a
finitely presented group is finitely normally generated.  Thus the abstract
HNN construction can be returned to the literal `FP n m` syntax without
changing its chosen generators.
-/

namespace UniversalGroup.PreparationGenerators

variable {H : Type*} [Group H] [Group.IsFinitelyPresented H] {n : ℕ}

/-- Finite normal generation of the kernel is independent of the chosen
finite generating set. -/
theorem kernel_of_surjective (ρ : FreeGroup (Fin n) →* H)
    (hρ : Function.Surjective ρ) : ρ.ker.IsFinitelyNormallyGenerated := by
  classical
  obtain ⟨m, π, hπ, S, hSfin, hSker⟩ :=
    (inferInstance : Group.IsFinitelyPresented H).out
  choose a ha using fun i : Fin m => hρ (π (FreeGroup.of i))
  choose b hb using fun i : Fin n => hπ (ρ (FreeGroup.of i))
  let α : FreeGroup (Fin m) →* FreeGroup (Fin n) := FreeGroup.lift a
  let β : FreeGroup (Fin n) →* FreeGroup (Fin m) := FreeGroup.lift b
  have hα : ρ.comp α = π := by
    apply FreeGroup.ext_hom
    intro i
    simpa [α] using ha i
  have hβ : π.comp β = ρ := by
    apply FreeGroup.ext_hom
    intro i
    simpa [β] using hb i
  let rel : Fin n → FreeGroup (Fin n) := fun i =>
    FreeGroup.of i * (α (β (FreeGroup.of i)))⁻¹
  let T : Set (FreeGroup (Fin n)) := α '' S ∪ Set.range rel
  let N : Subgroup (FreeGroup (Fin n)) := Subgroup.normalClosure T
  let q : FreeGroup (Fin n) →* FreeGroup (Fin n) ⧸ N := QuotientGroup.mk' N
  have hNρ : N ≤ ρ.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro x (⟨y, hy, rfl⟩ | ⟨i, rfl⟩)
    · change ρ (α y) = 1
      rw [show ρ (α y) = π y from DFunLike.congr_fun hα y]
      change y ∈ π.ker
      rw [← hSker]
      exact Subgroup.subset_normalClosure hy
    · change ρ (rel i) = 1
      simp only [rel, map_mul, map_inv]
      rw [show ρ (α (β (FreeGroup.of i))) = π (β (FreeGroup.of i)) from
        DFunLike.congr_fun hα _, show π (β (FreeGroup.of i)) = ρ (FreeGroup.of i) from
        DFunLike.congr_fun hβ _]
      exact mul_inv_cancel _
  have hq : q.comp (α.comp β) = q := by
    apply FreeGroup.ext_hom
    intro i
    have hm : rel i ∈ N := Subgroup.subset_normalClosure (Or.inr ⟨i, rfl⟩)
    have hh : q (rel i) = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    simp only [rel, map_mul, map_inv, mul_inv_eq_one] at hh
    exact hh.symm
  have hπq : π.ker ≤ (q.comp α).ker := by
    rw [← hSker]
    apply Subgroup.normalClosure_le_normal
    intro x hx
    change q (α x) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure (Or.inl ⟨x, hx, rfl⟩)
  have hρN : ρ.ker ≤ N := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    change q x = 1
    rw [← DFunLike.congr_fun hq x]
    apply hπq
    change π (β x) = 1
    rw [show π (β x) = ρ x from DFunLike.congr_fun hβ x]
    exact hx
  exact ⟨T, (hSfin.image α).union (Set.finite_range rel), le_antisymm hNρ hρN⟩

/-- A literal finite presentation on the prescribed generators, together
with an isomorphism that preserves those generators exactly. -/
theorem presentation_of_surjective (ρ : FreeGroup (Fin n) →* H)
    (hρ : Function.Surjective ρ) :
    ∃ m : ℕ, ∃ P : FP n m, ∃ e : P.Group ≃* H,
      ∀ i : Fin n, e (generators P i) = ρ (FreeGroup.of i) := by
  classical
  obtain ⟨S, hSfin, hSker⟩ := kernel_of_surjective ρ hρ
  let : Fintype S := hSfin.fintype
  let f : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let P : FP n (Fintype.card S) := ⟨fun i => ((f i : S) : FreeGroup (Fin n)).toWord⟩
  have hP : P.relSet = S := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      simpa only [P, FreeGroup.mk_toWord] using (f i).property
    · intro hx
      obtain ⟨i, hi⟩ := f.surjective ⟨x, hx⟩
      exact ⟨i, by simp [P, hi, FreeGroup.mk_toWord]⟩
  have hker : Subgroup.normalClosure P.relSet = ρ.ker := by rw [hP, hSker]
  let e : P.Group ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
  refine ⟨Fintype.card S, P, e, ?_⟩
  intro i
  rfl

end UniversalGroup.PreparationGenerators
