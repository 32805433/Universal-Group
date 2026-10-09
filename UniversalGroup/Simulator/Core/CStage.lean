module

public import UniversalGroup.Simulator.Core.PowerHNNModel
public import UniversalGroup.Foundations.HNN.NormalForms
public import UniversalGroup.Simulator.Core.SupportedRules

@[expose] public section

open Function

namespace UniversalGroup
namespace BorisovCStage

noncomputable section

open BorisovHNNModel
open HNNLemmas

/-!
This file isolates Borisov's `c`-stage (his group `Γ₂`) in the actual
iterated-HNN model of `Γ₃`.

Literature: V. V. Borisov, *Simple examples of groups with unsolvable word
problem* (1969), Assertions IV--V and Lemma 4, English translation
pp. 769--772. Adjustments to these arguments are discussed in
M. Tancer, *Simpler algorithmically unrecognizable 4-manifolds*,
arXiv:2310.07421v2 (2025), Appendix A, pp. 25--27.

The construction needs the two displayed rank-five systems to be free.  The
structure below packages exactly this freeness input.
-/

/-- Indices for `s₁,s₂,A₁,A₂,A₃` and `s₁,s₂,B₁,B₂,B₃`. -/
abbrev RuleBasis := Fin 2 ⊕ Fin 3

def stable3 (beta : Fin 2) : Gamma3 :=
  if beta = 0 then s1_3 else s2_3

def positive3 (w : List (Fin 2)) : Gamma3 :=
  UniversalGroup.evalPositive s1_3 s2_3 w

/-- `A_i = d^i F_i e^i`, with Lean's `i` zero-based. -/
def a3 (datum : UniversalGroup.SupportedRules) (i : Fin 3) : Gamma3 :=
  d3 ^ (i.val + 1) * positive3 (datum.F i) * e3 ^ (i.val + 1)

/-- `B_i = d^i E_i e^i`, with Lean's `i` zero-based. -/
def b3 (datum : UniversalGroup.SupportedRules) (i : Fin 3) : Gamma3 :=
  d3 ^ (i.val + 1) * positive3 (datum.E i) * e3 ^ (i.val + 1)

def uBasis (datum : UniversalGroup.SupportedRules) : RuleBasis → Gamma3
  | .inl beta => stable3 beta
  | .inr i => a3 datum i

def vBasis (datum : UniversalGroup.SupportedRules) : RuleBasis → Gamma3
  | .inl beta => stable3 beta
  | .inr i => b3 datum i

def uLift (datum : UniversalGroup.SupportedRules) : FreeGroup RuleBasis →* Gamma3 :=
  FreeGroup.lift (uBasis datum)

def vLift (datum : UniversalGroup.SupportedRules) : FreeGroup RuleBasis →* Gamma3 :=
  FreeGroup.lift (vBasis datum)

/-- Borisov's Assertion IV in the exact form required to build the `c`-HNN
extension. -/
structure RankFiveFree (datum : UniversalGroup.SupportedRules) : Prop where
  u_injective : Function.Injective (uLift datum)
  v_injective : Function.Injective (vLift datum)

abbrev U (datum : UniversalGroup.SupportedRules) : Subgroup Gamma3 :=
  MonoidHom.range (uLift datum)

abbrev V (datum : UniversalGroup.SupportedRules) : Subgroup Gamma3 :=
  MonoidHom.range (vLift datum)

/-- The letterwise correspondence `s_beta ↦ s_beta`, `A_i ↦ B_i`. -/
def cEquiv (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum) :
    U datum ≃* V datum :=
  rangeEquiv (uLift datum) (vLift datum)
    hfree.u_injective hfree.v_injective

@[simp]
theorem cEquiv_on_basis (datum : UniversalGroup.SupportedRules)
    (hfree : RankFiveFree datum) (q : RuleBasis) :
    ((cEquiv datum hfree
        ⟨uBasis datum q, ⟨FreeGroup.of q, by simp [uLift]⟩⟩ : V datum) : Gamma3) =
      vBasis datum q := by
  let source : U datum :=
    ⟨uBasis datum q, ⟨FreeGroup.of q, by simp [uLift]⟩⟩
  let canonical : U datum :=
    ⟨uLift datum (FreeGroup.of q), ⟨FreeGroup.of q, rfl⟩⟩
  have hsource : source = canonical := by
    apply Subtype.ext
    simp [source, canonical, uLift]
  change ((cEquiv datum hfree source : V datum) : Gamma3) = _
  rw [hsource]
  change vLift datum
      ((equivRangeOfInjective (uLift datum) hfree.u_injective).symm canonical) =
    vBasis datum q
  have hy :
      (equivRangeOfInjective (uLift datum) hfree.u_injective).symm canonical =
        FreeGroup.of q := by
    apply hfree.u_injective
    exact congrArg Subtype.val
      ((equivRangeOfInjective (uLift datum) hfree.u_injective).apply_symm_apply
        canonical)
  rw [hy]
  simp [vLift]

/-- Borisov's `Γ₂`, with Mathlib's stable letter equal to `c⁻¹`. -/
abbrev Gamma2 (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum) :=
  HNNExtension Gamma3 (U datum) (V datum) (cEquiv datum hfree)

def of3 (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum) :
    Gamma3 →* Gamma2 datum hfree :=
  HNNExtension.of

/-- Borisov's generator `c`; Mathlib's HNN stable letter is `c⁻¹`. -/
def c (datum : UniversalGroup.SupportedRules) (hfree : RankFiveFree datum) :
    Gamma2 datum hfree :=
  (HNNExtension.t : Gamma2 datum hfree)⁻¹

theorem of3_injective (datum : UniversalGroup.SupportedRules)
    (hfree : RankFiveFree datum) :
    Function.Injective (of3 datum hfree) :=
  HNNExtension.of_injective (cEquiv datum hfree)

/-- The defining `c`-conjugation law on all five displayed basis elements. -/
theorem c_conjugates_basis (datum : UniversalGroup.SupportedRules)
    (hfree : RankFiveFree datum) (q : RuleBasis) :
    (c datum hfree)⁻¹ * of3 datum hfree (uBasis datum q) * c datum hfree =
      of3 datum hfree (vBasis datum q) := by
  let uq : U datum :=
    ⟨uBasis datum q, ⟨FreeGroup.of q, by simp [uLift]⟩⟩
  have ht := HNNExtension.t_mul_of (φ := cEquiv datum hfree) uq
  change HNNExtension.t * HNNExtension.of (uBasis datum q) * HNNExtension.t⁻¹ =
    HNNExtension.of (vBasis datum q)
  rw [ht]
  simp [uq, cEquiv_on_basis]

theorem c_commutes_stable (datum : UniversalGroup.SupportedRules)
    (hfree : RankFiveFree datum) (beta : Fin 2) :
    Commute (of3 datum hfree (stable3 beta)) (c datum hfree) := by
  rw [commute_iff_eq]
  have h := c_conjugates_basis datum hfree (Sum.inl beta)
  change (c datum hfree)⁻¹ * of3 datum hfree (stable3 beta) * c datum hfree =
    of3 datum hfree (stable3 beta) at h
  have hc := congrArg (fun x => c datum hfree * x) h
  simpa [mul_assoc] using hc

/-- The three simulator relations `c⁻¹ A_i c = B_i`. -/
theorem c_simulation (datum : UniversalGroup.SupportedRules)
    (hfree : RankFiveFree datum) (i : Fin 3) :
    (c datum hfree)⁻¹ * of3 datum hfree (a3 datum i) * c datum hfree =
      of3 datum hfree (b3 datum i) := by
  simpa [uBasis, vBasis] using
    c_conjugates_basis datum hfree (Sum.inr i)

/-! ## The stable-letter projection and the zero-`c` case of Lemma 4 -/

/-- Kill `d,e` and retain the first HNN stable letter as the first free
generator. -/
def stableProjection1 : Stage1 →* FreeGroup (Fin 2) :=
  HNNExtension.lift (1 : Base →* FreeGroup (Fin 2)) (FreeGroup.of 0) (by
    intro a
    simp)

@[simp]
theorem stableProjection1_of0 (x : Base) :
    stableProjection1 (of0 x) = 1 := by
  simp [stableProjection1, of0]

@[simp]
theorem stableProjection1_s1 :
    stableProjection1 s1 = FreeGroup.of (0 : Fin 2) := by
  simp [stableProjection1, s1]

/-- Kill `d,e` and remember `s₁,s₂` as a free basis.  This is the projection
used in Borisov's `m = 0` argument. -/
def stableProjection3 : Gamma3 →* FreeGroup (Fin 2) :=
  HNNExtension.lift stableProjection1 (FreeGroup.of 1) (by
    intro a
    let a0 : A0 := inA1.symm a
    have ha : a = inA1 a0 := (inA1.apply_symm_apply a).symm
    rw [ha, phi1_inA1]
    simp [stableProjection1, of0, coe_inA1, coe_inB1])

@[simp]
theorem stableProjection3_d : stableProjection3 d3 = 1 := by
  simp [stableProjection3, d3, of1]

@[simp]
theorem stableProjection3_e : stableProjection3 e3 = 1 := by
  simp [stableProjection3, e3, of1]

@[simp]
theorem stableProjection3_s1 :
    stableProjection3 s1_3 = FreeGroup.of (0 : Fin 2) := by
  simp [stableProjection3, s1_3, of1]

@[simp]
theorem stableProjection3_s2 :
    stableProjection3 s2_3 = FreeGroup.of (1 : Fin 2) := by
  simp [stableProjection3, s2_3]

/-- The positive monoid on two letters, embedded in its free group. -/
def positiveFree (w : List (Fin 2)) : FreeGroup (Fin 2) :=
  FreeGroup.mk (w.map fun i => (i, true))

theorem positiveFree_eq_eval (w : List (Fin 2)) :
    positiveFree w =
      UniversalGroup.evalPositive (FreeGroup.of 0) (FreeGroup.of 1) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      calc
        positiveFree (i :: w) = FreeGroup.of i * positiveFree w := by
          simp only [positiveFree, List.map_cons]
          change FreeGroup.mk ((i, true) :: w.map fun k => (k, true)) =
            FreeGroup.mk [(i, true)] * FreeGroup.mk (w.map fun k => (k, true))
          rw [FreeGroup.mul_mk]
          rfl
        _ = FreeGroup.of i *
              UniversalGroup.evalPositive (FreeGroup.of 0) (FreeGroup.of 1) w := by
          rw [ih]
        _ = UniversalGroup.evalPositive (FreeGroup.of 0) (FreeGroup.of 1) (i :: w) := by
          fin_cases i <;> simp [UniversalGroup.evalPositive]

theorem stableProjection3_positive (w : List (Fin 2)) :
    stableProjection3 (positive3 w) = positiveFree w := by
  induction w with
  | nil => exact FreeGroup.one_eq_mk
  | cons i w ih =>
      have hcons : positive3 (i :: w) =
          (if i = 0 then s1_3 else s2_3) * positive3 w := by
        simp [positive3, UniversalGroup.evalPositive]
      rw [hcons, map_mul, ih]
      rw [positiveFree_eq_eval, positiveFree_eq_eval]
      fin_cases i <;> simp [UniversalGroup.evalPositive]

private theorem positiveLetters_reduced (w : List (Fin 2)) :
    FreeGroup.IsReduced (w.map fun i => (i, true)) := by
  induction w with
  | nil => simp [FreeGroup.IsReduced]
  | cons i w ih =>
      cases w with
      | nil => simp [FreeGroup.IsReduced]
      | cons j w =>
          change List.IsChain (fun a b : Fin 2 × Bool =>
            a.1 = b.1 → a.2 = b.2)
              ((i, true) :: (j, true) :: w.map fun k => (k, true))
          rw [List.isChain_cons]
          exact ⟨by simp, ih⟩

theorem positiveFree_injective : Function.Injective positiveFree := by
  intro u v huv
  have hreduce := FreeGroup.reduce.sound huv
  have hu := (positiveLetters_reduced u).reduce_eq
  have hv := (positiveLetters_reduced v).reduce_eq
  rw [hu, hv] at hreduce
  have hinj : Function.Injective (fun i : Fin 2 => (i, true)) := by
    intro i j h
    exact congrArg Prod.fst h
  exact hinj.list_map hreduce

/-- The base subgroup `<d,e>` of `Γ₃`. -/
def DE3 : Subgroup Gamma3 :=
  Subgroup.closure ({d3, e3} : Set Gamma3)

theorem DE3_le_projection_ker :
    DE3 ≤ MonoidHom.ker stableProjection3 := by
  rw [DE3, Subgroup.closure_le]
  intro x hx
  rcases hx with (rfl | hx)
  · simp
  · simpa only [Set.mem_singleton_iff] using hx ▸ stableProjection3_e

end

end BorisovCStage
end UniversalGroup
