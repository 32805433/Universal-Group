module

public import UniversalGroup.Foundations.HNN.NormalForms
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# Removing a first syllable from a reduced HNN word

The first-head comparison is Mathlib's Britton comparison. Once a subgroup
calculation identifies an admissible prefixElement, the following induction removes
one stable letter without introducing a new reduction problem.
-/

namespace UniversalGroup.ReducedWordPeel

noncomputable section

variable {G : Type*} [Group G] {A B : Subgroup G} (φ : A ≃* B)

abbrev Word (G : Type*) [Group G] (A B : Subgroup G) :=
  HNNExtension.NormalWord.ReducedWord G A B
abbrev Host := HNNExtension G A B φ

def tail (w : Word G A B) (u : ℤˣ) (a : G) (rest : List (ℤˣ × G))
    (h : w.toList = (u, a) :: rest) (z : G) : Word G A B where
  head := z * a
  toList := rest
  chain := List.IsChain.tail (h ▸ w.chain)

def prefixElement (g : G) (u : ℤˣ) (z : G) : Host φ :=
  HNNExtension.of g * HNNExtension.t ^ (u : ℤ) * HNNExtension.of z⁻¹

theorem prod_eq_prefix_mul_tail (w : Word G A B) (u : ℤˣ) (a : G)
    (rest : List (ℤˣ × G)) (h : w.toList = (u, a) :: rest) (z : G) :
    w.prod φ = prefixElement φ w.head u z * (tail w u a rest h z).prod φ := by
  simp only [prefixElement, tail, HNNExtension.NormalWord.ReducedWord.prod,
    h, List.map_cons, List.prod_cons, map_mul, map_inv]
  group

theorem tail_length_lt (w : Word G A B) (u : ℤˣ) (a : G)
    (rest : List (ℤˣ × G)) (h : w.toList = (u, a) :: rest) (z : G) :
    (tail w u a rest h z).toList.length < w.toList.length := by
  simp [tail, h]

/-- Equal reduced words have the same first stable sign and their heads
lie in the same coset of the appropriate attaching subgroup. -/
theorem first_comparison (w v : Word G A B) (heq : w.prod φ = v.prod φ)
    (u : ℤˣ) (a : G) (rest : List (ℤˣ × G))
    (hw : w.toList = (u, a) :: rest) :
    ∃ (b : G) (more : List (ℤˣ × G)),
      v.toList = (u, b) :: more ∧
      w.head⁻¹ * v.head ∈ HNNExtension.toSubgroup A B (-u) ∧
      rest.map Prod.fst = more.map Prod.fst := by
  have hc := HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq φ heq
  have hm : w.head⁻¹ * v.head ∈ HNNExtension.toSubgroup A B (-u) :=
    hc.2 u (by simp [hw])
  cases hv : v.toList with
  | nil => simp [hw, hv] at hc
  | cons first more =>
      have hs : u = first.1 ∧ rest.map Prod.fst = more.map Prod.fst := by
        simpa [hw, hv] using hc.1
      refine ⟨first.2, more, ?_, hm, hs.2⟩
      simp only [hs.1, Prod.mk.eta]

/-- Strip equal positive Mathlib stable letters, transporting the head
coset discrepancy to the other side of that letter. -/
theorem tail_comparison_one (w v : Word G A B)
    (a b : G) (rest more : List (ℤˣ × G))
    (hw : w.toList = (1, a) :: rest) (hv : v.toList = (1, b) :: more)
    (heq : w.prod φ = v.prod φ) (hcoset : w.head⁻¹ * v.head ∈ B) :
    (tail w 1 a rest hw 1).prod φ =
      (tail v 1 b more hv (φ.symm ⟨w.head⁻¹ * v.head, hcoset⟩ : G)).prod φ := by
  let c : B := ⟨w.head⁻¹ * v.head, hcoset⟩
  have hcarry : (HNNExtension.of v.head : Host φ) * HNNExtension.t =
      HNNExtension.of w.head * HNNExtension.t * HNNExtension.of (φ.symm c : G) := by
    have hh := congrArg (fun x : Host φ => HNNExtension.of w.head * x)
      (HNNExtension.of_mul_t (φ := φ) c)
    simpa only [c, map_mul, map_inv, mul_assoc, mul_inv_cancel_left] using hh
  have hvprod : (tail v 1 b more hv (φ.symm c : G)).prod φ =
      HNNExtension.of (φ.symm c : G) * (tail v 1 b more hv 1).prod φ := by
    simp [tail, HNNExtension.NormalWord.ReducedWord.prod, map_mul, mul_assoc]
  change (tail w 1 a rest hw 1).prod φ = (tail v 1 b more hv (φ.symm c : G)).prod φ
  rw [hvprod]
  apply mul_left_cancel (a := (HNNExtension.of w.head : Host φ) * HNNExtension.t)
  calc
    HNNExtension.of w.head * HNNExtension.t * (tail w 1 a rest hw 1).prod φ =
        w.prod φ := by
      simpa [prefixElement] using (prod_eq_prefix_mul_tail φ w 1 a rest hw 1).symm
    _ = v.prod φ := heq
    _ = HNNExtension.of v.head * HNNExtension.t * (tail v 1 b more hv 1).prod φ := by
      simpa [prefixElement] using prod_eq_prefix_mul_tail φ v 1 b more hv 1
    _ = HNNExtension.of w.head * HNNExtension.t *
        (HNNExtension.of (φ.symm c : G) * (tail v 1 b more hv 1).prod φ) := by
      rw [hcarry, mul_assoc]

/-- A reusable subgroup intersection induction. `J` contains the base
coefficients, `K` is the other subgroup, and `N` is the proposed intersection.
The only substantive input is that each first syllable admits a prefixElement in
`N`; the remainder has one fewer stable letter and still has coefficients
in `J`. -/
theorem mem_of_recognized_prefix
    (J : Subgroup G) (K N : Subgroup (Host φ)) (hNK : N ≤ K)
    (hbase : ∀ g ∈ J, HNNExtension.of g ∈ K → HNNExtension.of g ∈ N)
    (hstep : ∀ (w : Word G A B) (u : ℤˣ) (a : G) (rest : List (ℤˣ × G)),
      w.toList = (u, a) :: rest → w.head ∈ J →
      (∀ p ∈ w.toList, p.2 ∈ J) → w.prod φ ∈ K →
      ∃ z ∈ J, prefixElement φ w.head u z ∈ N)
    (w : Word G A B) (hhead : w.head ∈ J)
    (hcoeff : ∀ p ∈ w.toList, p.2 ∈ J) (hK : w.prod φ ∈ K) :
    w.prod φ ∈ N := by
  generalize hn : w.toList.length = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
      cases hw : w.toList with
      | nil =>
          have hprod : w.prod φ = HNNExtension.of w.head := by
            simp [HNNExtension.NormalWord.ReducedWord.prod, hw]
          exact hprod ▸ hbase w.head hhead (hprod ▸ hK)
      | cons first rest =>
          rcases first with ⟨u, a⟩
          rcases hstep w u a rest hw hhead hcoeff hK with ⟨z, hz, hpref⟩
          let v := tail w u a rest hw z
          have hvhead : v.head ∈ J := J.mul_mem hz (hcoeff (u, a) (by simp [hw]))
          have hvcoeff : ∀ p ∈ v.toList, p.2 ∈ J := by
            intro p hp
            exact hcoeff p (by simp only [hw, List.mem_cons]; exact Or.inr hp)
          have heq : w.prod φ = prefixElement φ w.head u z * v.prod φ :=
            prod_eq_prefix_mul_tail φ w u a rest hw z
          have hvK : v.prod φ ∈ K := by
            have hm := K.mul_mem (K.inv_mem (hNK hpref)) hK
            rwa [heq, inv_mul_cancel_left] at hm
          have hvlt : v.toList.length < n := by
            rw [← hn]
            exact tail_length_lt w u a rest hw z
          have hvN := ih v.toList.length hvlt v hvhead hvcoeff hvK rfl
          rw [heq]
          exact N.mul_mem hpref hvN

end

end UniversalGroup.ReducedWordPeel
