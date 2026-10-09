module

public import UniversalGroup.Preparation.ReflectionInput
public import UniversalGroup.Foundations.FinitePresentation.Generators
public import UniversalGroup.Preparation.Positive

@[expose] public section

/-!
# A marked quotient retained by the reflection-based preparation

The free coding family in `C₄ * C₄` is killed whenever the second cyclic
factor has square one. Consequently the reflection-based two-generator preparation admits
a marked map to any pair `a,b` with `(a*b)²=1`. This extra property supplies
the protected-row preparation without a small-cancellation theorem.
-/

namespace UniversalGroup.Embedding.MarkedQuotient

noncomputable section
open PreparationFreeProduct PreparationTwoGenerators
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {H : Type} [Group H]

theorem fourth_of_square (x : H) (hx : x ^ 2 = 1) : x ^ 4 = 1 := by
  calc
    x ^ 4 = (x ^ 2) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [hx, one_pow]

/-- The coding family vanishes under every map killing the square of the second factor. -/
theorem freeFamily_killed (f : Pair →* H) (hf : f v ^ 2 = 1) (n : ℕ) :
    f.comp (freeFamily n) = 1 := by
  have hp : f.comp freePair = 1 := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [freePair, hf]
  change f.comp (freePair.comp (FiniteFree.hom n)) = 1
  rw [← MonoidHom.comp_assoc, hp, MonoidHom.one_comp]

variable {P : Type} [Group P] {n : ℕ} (D : Input P n)
variable (x t : H) (hx : x ^ 2 = 1)

include hx in
theorem conjugate_square (g : H) : (g * x * g⁻¹) ^ 2 = 1 := by
  have h := congrArg ((MulAut.conj g).toMonoidHom) hx
  simpa only [map_pow, map_one, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

def pairMap : Pair →* H :=
  Monoid.Coprod.lift (cyclicHom x (fourth_of_square x hx))
    (cyclicHom (t * x * t⁻¹) (fourth_of_square _ (conjugate_square x hx t)))

@[simp] theorem pairMap_b : pairMap x t hx b = x := by simp [pairMap, b]
@[simp] theorem pairMap_v : pairMap x t hx v = t * x * t⁻¹ := by simp [pairMap, v]

def inputMap : P →* H :=
  (cyclicHom (t⁻¹ * x * t)
    (fourth_of_square _ (by simpa only [inv_inv] using conjugate_square x hx t⁻¹))).comp D.rho

@[simp] theorem inputMap_u : inputMap D x t hx D.u = t⁻¹ * x * t := by
  simp [inputMap, D.rho_u]

theorem inputMap_j : (inputMap D x t hx).comp D.j = 1 := by
  rw [inputMap, MonoidHom.comp_assoc, D.rho_j, MonoidHom.comp_one]

def amalgamMaps : (i : Bool) → Input.Factor (P := P) i →* H
  | false => inputMap D x t hx
  | true => pairMap x t hx

def amalgamMap : D.Amalgam →* H :=
  Monoid.PushoutI.lift (amalgamMaps D x t hx) 1 (by
    intro i
    cases i
    · exact inputMap_j D x t hx
    · change (pairMap x t hx).comp (freeFamily n) = 1
      apply freeFamily_killed
      rw [pairMap_v]
      exact conjugate_square x hx t)

@[simp] theorem amalgamMap_inP (g : P) :
    amalgamMap D x t hx (D.inP g) = inputMap D x t hx g :=
  Monoid.PushoutI.lift_of (φ := D.diagram) _ _ _ (i := false) g

@[simp] theorem amalgamMap_inPair (g : Pair) :
    amalgamMap D x t hx (D.inPair g) = pairMap x t hx g :=
  Monoid.PushoutI.lift_of (φ := D.diagram) _ _ _ (i := true) g

theorem conjugates_pair (g : Pair) :
    t⁻¹ * amalgamMap D x t hx (D.inPair g) * t =
      amalgamMap D x t hx (D.targetPair g) := by
  have hh : (MulAut.conj t⁻¹).toMonoidHom.comp
      ((amalgamMap D x t hx).comp D.inPair) =
      (amalgamMap D x t hx).comp D.targetPair := by
    apply Monoid.Coprod.hom_ext
    · apply PreparationCyclic.hom_ext
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      change t⁻¹ * amalgamMap D x t hx (D.inPair b) * t =
        amalgamMap D x t hx (D.targetPair b)
      rw [D.targetPair_b, amalgamMap_inP, inputMap_u, amalgamMap_inPair, pairMap_b]
    · apply PreparationCyclic.hom_ext
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      change t⁻¹ * amalgamMap D x t hx (D.inPair v) * t =
        amalgamMap D x t hx (D.targetPair v)
      rw [D.targetPair_v, amalgamMap_inPair, amalgamMap_inPair, pairMap_b, pairMap_v]
      group
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
    DFunLike.congr_fun hh g

/-- The prepared torsion generator maps to an arbitrary involution and the
stable generator maps to an arbitrary group element. -/
def map : D.Host →* H :=
  IdentifyingHNN.lift _ _ _ _ (amalgamMap D x t hx) t (conjugates_pair D x t hx)

@[simp] theorem map_x : map D x t hx D.x = x := by
  simp [map, Input.x, Input.ofBase]

@[simp] theorem map_t : map D x t hx D.t = t := by
  simp [map, Input.t]

/-- Strengthened positive preparation, with a specified marked map in addition
to the faithful input embedding. -/
theorem exists_prepared_with_values (Q : FP k m) (a b : H) (hab : (a*b)^2=1) :
    ∃ G : PreparedInput,
      Nonempty (GroupEmbedding Q.Group G.presentation.Group) ∧
      ∃ f : G.presentation.Group →* H,
        ∀ i, f (generators G.presentation i) = ![a,b] i := by
  let D := PreparationReflectionInput.input Q
  obtain ⟨r, P, e, he⟩ := PreparationGenerators.presentation_of_surjective
    D.generators D.generators_surjective
  have hx : (generators P 0)^4=1 := by
    apply e.injective
    rw [map_pow, map_one, he, D.generators_zero, D.x_fourthPower]
  let chi : P.Group →* Multiplicative ℤ := D.character.comp e.toMonoidHom
  have hchi_x : chi (generators P 0)=1 := by
    change D.character (e (generators P 0))=1
    rw [he, D.generators_zero, D.character_x]
  have hchi_t : chi (generators P 1)=Multiplicative.ofAdd 1 := by
    change D.character (e (generators P 1))=Multiplicative.ofAdd 1
    rw [he, D.generators_one, D.character_t]
  let G := PreparationPositive.prepared P hx chi hchi_x hchi_t
  let j : Q.Group →* P.Group := e.symm.toMonoidHom.comp
    (D.embedding.comp (PreparationReflectionStage.embedding Q))
  have hj : Function.Injective j := e.symm.injective.comp
    (D.embedding_injective.comp (PreparationReflectionStage.embedding_injective Q))
  let embedding : GroupEmbedding Q.Group G.presentation.Group :=
    ⟨(PreparationPositive.ofOld P).comp j,
      (PreparationPositive.ofOld_injective P hx).comp hj⟩
  let f : G.presentation.Group →* H :=
    (map D (a*b) a hab).comp (e.toMonoidHom.comp (PreparationPositive.toOld P hx))
  refine ⟨G, ⟨embedding⟩, f, ?_⟩
  intro i
  fin_cases i
  · change map D (a*b) a hab (e (PreparationPositive.toOld P hx (PreparationPositive.a P))) = a
    rw [PreparationPositive.toOld_a, he, D.generators_one, map_t]
  · change map D (a*b) a hab (e (PreparationPositive.toOld P hx (PreparationPositive.b P))) = b
    rw [PreparationPositive.toOld_b, map_mul, map_inv, he, he,
      D.generators_zero, D.generators_one, map_mul, map_inv, map_x, map_t]
    group

end
end UniversalGroup.Embedding.MarkedQuotient
