module

public import UniversalGroup.Simulator.Core.PinchClassification

@[expose] public section

/-!
# Borisov contexts with an arbitrary outer free word

Only the middle word in the pinch induction is assumed positive. The terminal
projection proves that the arbitrary outer free word is itself positive.
-/
namespace UniversalGroup
namespace BorisovCStage
open BorisovHNNModel
noncomputable section

/-- Evaluate an arbitrary free word in the two simulator letters. -/
def sLift3 : FreeGroup (Fin 2) →* Gamma3 := FreeGroup.lift stable3

@[simp] theorem stableProjection3_sLift3 (W : FreeGroup (Fin 2)) :
    stableProjection3 (sLift3 W) = W := by
  have h : stableProjection3.comp sLift3 = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [sLift3, stable3]
  exact DFunLike.congr_fun h W

/-- The arbitrary-outer-word terminal case. -/
theorem lemma4_zero_c
    (W : FreeGroup (Fin 2)) (Q : List (Fin 2)) (L R : Gamma3)
    (hL : L ∈ DE3) (hR : R ∈ DE3)
    (heq : (sLift3 W)⁻¹ * L * positive3 Q * R = 1) :
    W = positiveFree Q := by
  have hmap := congrArg stableProjection3 heq
  have hL1 : stableProjection3 L = 1 := DE3_le_projection_ker hL
  have hR1 : stableProjection3 R = 1 := DE3_le_projection_ker hR
  simpa only [map_mul, map_inv, map_one, stableProjection3_positive,
    stableProjection3_sLift3, hL1, hR1, mul_one, inv_mul_eq_one] using hmap

def dCyclic : Subgroup Gamma3 :=
  Subgroup.closure ({d3} : Set Gamma3)

def eCyclic : Subgroup Gamma3 :=
  Subgroup.closure ({e3} : Set Gamma3)

theorem dCyclic_le_DE3 : dCyclic ≤ DE3 := by
  rw [dCyclic, Subgroup.closure_le, Set.singleton_subset_iff]
  exact Subgroup.subset_closure (by simp)

theorem eCyclic_le_DE3 : eCyclic ≤ DE3 := by
  rw [eCyclic, Subgroup.closure_le, Set.singleton_subset_iff]
  exact Subgroup.subset_closure (by simp)

abbrev CReducedWord (datum : UniversalGroup.SupportedRules)
    (_hfree : RankFiveFree datum) :=
  HNNExtension.NormalWord.ReducedWord Gamma3 (U datum) (V datum)

/-- An HNN-reduced word on `{c,d}`.  Its base coefficients are all powers of
`d`; its stable-letter list is the list of occurrences of `c^{±1}`. -/
structure LeftContext (datum : UniversalGroup.SupportedRules)
    (hfree : RankFiveFree datum) where
  word : CReducedWord datum hfree
  head_mem : word.head ∈ dCyclic
  coeff_mem : ∀ p ∈ word.toList, p.2 ∈ dCyclic

/-- An HNN-reduced word on `{c,e}`. -/
structure RightContext (datum : UniversalGroup.SupportedRules)
    (hfree : RankFiveFree datum) where
  word : CReducedWord datum hfree
  head_mem : word.head ∈ eCyclic
  coeff_mem : ∀ p ∈ word.toList, p.2 ∈ eCyclic

def leftValue (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum)
    (L : LeftContext datum hfree) : Gamma2 datum hfree :=
  L.word.prod (cEquiv datum hfree)

def rightValue (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum)
    (R : RightContext datum hfree) : Gamma2 datum hfree :=
  R.word.prod (cEquiv datum hfree)

def positive2 (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum)
    (w : List (Fin 2)) : Gamma2 datum hfree :=
  of3 datum hfree (positive3 w)

/-- The published hypothesis `P⁻¹ L Q R = 1`, with `L` and `R` already in
the irreducible forms used in Borisov's induction. -/
def sLift2 (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum) :
    FreeGroup (Fin 2) →* Gamma2 datum hfree := (of3 datum hfree).comp sLift3

def Lemma4Equation (datum : UniversalGroup.SupportedRules)
    (hfree : RankFiveFree datum) (P : FreeGroup (Fin 2)) (Q : List (Fin 2))
    (L : LeftContext datum hfree) (R : RightContext datum hfree) : Prop :=
  (sLift2 datum hfree P)⁻¹ * leftValue datum hfree L *
      positive2 datum hfree Q * rightValue datum hfree R = 1

/-- Exact c-stage separation theorem needed by the converse direction.

This is Borisov 1969, Lemma 4, specialized to `N = 2`, `M = 3`, `α = 4`.
The induction measure in the paper is the number of positive occurrences of
`c` in `L.word.toList ++ R.word.toList` (equivalently one half of its length).
-/
def BorisovLemma4 (datum : UniversalGroup.SupportedRules)
    (hfree : RankFiveFree datum) : Prop :=
  ∀ (P : FreeGroup (Fin 2)) (Q : List (Fin 2))
    (L : LeftContext datum hfree) (R : RightContext datum hfree),
    Lemma4Equation datum hfree P Q L R →
      ∃ Q' : List (Fin 2), P = positiveFree Q' ∧ UniversalGroup.PositiveEq datum.rules Q Q'

/-- The `m = 0` branch of the published induction in the iterated HNN model. -/
theorem lemma4_of_context_lists_nil
    (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum)
    (P : FreeGroup (Fin 2)) (Q : List (Fin 2))
    (L : LeftContext datum hfree) (R : RightContext datum hfree)
    (hLnil : L.word.toList = []) (hRnil : R.word.toList = [])
    (heq : Lemma4Equation datum hfree P Q L R) :
    P = positiveFree Q := by
  have hbase :
      (sLift3 P)⁻¹ * L.word.head * positive3 Q * R.word.head = 1 := by
    apply of3_injective datum hfree
    simpa [Lemma4Equation, positive2, sLift2, leftValue, rightValue,
      HNNExtension.NormalWord.ReducedWord.prod, hLnil, hRnil,
      map_mul, map_inv, of3] using heq
  exact lemma4_zero_c P Q L.word.head R.word.head
    (dCyclic_le_DE3 L.head_mem) (eCyclic_le_DE3 R.head_mem) hbase

/-! ## Context subgroups and factorization -/

def CD (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum) :
    Subgroup (Gamma2 datum hfree) :=
  Subgroup.closure
    ({c datum hfree, of3 datum hfree d3} : Set (Gamma2 datum hfree))

def CE (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum) :
    Subgroup (Gamma2 datum hfree) :=
  Subgroup.closure
    ({c datum hfree, of3 datum hfree e3} : Set (Gamma2 datum hfree))

theorem equation_iff_factorization
    {G : Type*} [Group G] (P L Q R : G) :
    P⁻¹ * L * Q * R = 1 ↔ P = L * Q * R := by
  constructor
  · intro h
    apply inv_mul_eq_one.mp
    simpa only [mul_assoc] using h
  · intro h
    rw [h]
    group

/-! ## Isolating the positive-`c` induction step -/

def contextComplexity
    (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum)
    (L : LeftContext datum hfree) (R : RightContext datum hfree) : ℕ :=
  L.word.toList.length + R.word.toList.length

/-- The local reduction statement in Borisov's Lemma 4.

If the context is nonempty, Britton reduction plus Assertions IV--V must
exhibit one semigroup rule in `Q` and new irreducible contexts with strictly
fewer occurrences of `c^{±1}`. For adjustments to Borisov's case analysis,
see Tancer, arXiv:2310.07421v2, Appendix A.
-/
def PinchReduction (datum : UniversalGroup.SupportedRules)
    (hfree : RankFiveFree datum) : Prop :=
  ∀ (P : FreeGroup (Fin 2)) (Q : List (Fin 2))
    (L : LeftContext datum hfree) (R : RightContext datum hfree),
    Lemma4Equation datum hfree P Q L R →
      contextComplexity datum hfree L R = 0 ∨
        ∃ (Q' : List (Fin 2))
          (L' : LeftContext datum hfree) (R' : RightContext datum hfree),
          UniversalGroup.PositiveEq datum.rules Q Q' ∧
          Lemma4Equation datum hfree P Q' L' R' ∧
          contextComplexity datum hfree L' R' <
            contextComplexity datum hfree L R

/-- Once the local pinch-reduction statement is available, well-founded
induction gives all of Borisov's Lemma 4. -/
theorem borisovLemma4_of_pinchReduction
    (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum)
    (hpinch : PinchReduction datum hfree) :
    BorisovLemma4 datum hfree := by
  intro P Q L R heq
  generalize hn : contextComplexity datum hfree L R = n
  induction n using Nat.strong_induction_on generalizing Q L R with
  | h n ih =>
      rcases hpinch P Q L R heq with hzero | hstep
      · have hsum : L.word.toList.length + R.word.toList.length = 0 := by
          simpa [contextComplexity] using hzero
        have hlens := Nat.add_eq_zero_iff.mp hsum
        have hLnil : L.word.toList = [] :=
          List.eq_nil_of_length_eq_zero hlens.1
        have hRnil : R.word.toList = [] :=
          List.eq_nil_of_length_eq_zero hlens.2
        exact ⟨Q, lemma4_of_context_lists_nil datum hfree P Q L R hLnil hRnil heq,
          Relation.ReflTransGen.refl⟩
      · rcases hstep with ⟨Q', L', R', hQQ', heq', hlt⟩
        have hlt' : contextComplexity datum hfree L' R' < n := by
          simpa [hn] using hlt
        obtain ⟨Q'', hW, hQ'Q''⟩ := ih (contextComplexity datum hfree L' R') hlt'
          Q' L' R' heq' rfl
        exact ⟨Q'', hW, hQQ'.trans hQ'Q''⟩


end
end BorisovCStage
end UniversalGroup
