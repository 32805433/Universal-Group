module

public import UniversalGroup.Foundations.HNN.NormalForms
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.Algebra.Group.Commute.Basic

@[expose] public section

/-!
# Two conjugate factors inside a centralizer extension

The abstract amalgam identifies the same subgroup `E` of two subgroups
`A,B ≤ L`. Its canonical map into a centralizer HNN extension sends `A`
into the base group and `B` into its conjugate by the stable letter.
-/

namespace UniversalGroup.ConjugatedAmalgam

open HNNLemmas

variable {L : Type*} [Group L]

abbrev Factor (A B : Subgroup L) : Bool → Type _
  | false => A
  | true => B

instance (A B : Subgroup L) (i : Bool) : Group (Factor A B i) := by
  cases i <;> dsimp [Factor] <;> infer_instance

def inclusions (A B E : Subgroup L) (hEA : E ≤ A) (hEB : E ≤ B) :
    ∀ i, E →* Factor A B i
  | false => Subgroup.inclusion hEA
  | true => Subgroup.inclusion hEB

/-- The abstract amalgamated free product `A *_E B`. -/
abbrev Amalgam (A B E : Subgroup L) (hEA : E ≤ A) (hEB : E ≤ B) :=
  Monoid.PushoutI (inclusions A B E hEA hEB)

variable (A B E : Subgroup L) (hEA : E ≤ A) (hEB : E ≤ B)

def inA : A →* Amalgam A B E hEA hEB :=
  Monoid.PushoutI.of (φ := inclusions A B E hEA hEB) false
def inB : B →* Amalgam A B E hEA hEB :=
  Monoid.PushoutI.of (φ := inclusions A B E hEA hEB) true

theorem inclusions_injective (i : Bool) :
    Function.Injective (inclusions A B E hEA hEB i) := by
  cases i
  · exact Subgroup.inclusion_injective hEA
  · exact Subgroup.inclusion_injective hEB

theorem identify (e : E) :
    inA A B E hEA hEB ⟨e, hEA e.property⟩ =
      inB A B E hEA hEB ⟨e, hEB e.property⟩ := by
  exact (Monoid.PushoutI.of_apply_eq_base (inclusions A B E hEA hEB) false e).trans
    (Monoid.PushoutI.of_apply_eq_base (inclusions A B E hEA hEB) true e).symm

variable {H : Type*} [Group H]

/-- Extend homomorphisms of the two factors agreeing on the common subgroup. -/
def lift (fA : A →* H) (fB : B →* H)
    (h : ∀ e : E, fA ⟨e, hEA e.property⟩ = fB ⟨e, hEB e.property⟩) :
    Amalgam A B E hEA hEB →* H :=
  Monoid.PushoutI.lift (fun i => match i with | false => fA | true => fB)
    (fA.comp (Subgroup.inclusion hEA)) (by
      intro i
      cases i
      · rfl
      · ext e
        exact (h e).symm)

@[simp] theorem lift_inA (fA : A →* H) (fB : B →* H)
    (h : ∀ e : E, fA ⟨e, hEA e.property⟩ = fB ⟨e, hEB e.property⟩) (a : A) :
    lift A B E hEA hEB fA fB h (inA A B E hEA hEB a) = fA a := by
  exact Monoid.PushoutI.lift_of (φ := inclusions A B E hEA hEB)
    (fun i => match i with | false => fA | true => fB)
    (fA.comp (Subgroup.inclusion hEA)) _ (i := false) a

@[simp] theorem lift_inB (fA : A →* H) (fB : B →* H)
    (h : ∀ e : E, fA ⟨e, hEA e.property⟩ = fB ⟨e, hEB e.property⟩) (b : B) :
    lift A B E hEA hEB fA fB h (inB A B E hEA hEB b) = fB b := by
  exact Monoid.PushoutI.lift_of (φ := inclusions A B E hEA hEB)
    (fun i => match i with | false => fA | true => fB)
    (fA.comp (Subgroup.inclusion hEA)) _ (i := true) b

theorem hom_ext {f g : Amalgam A B E hEA hEB →* H}
    (hA : ∀ a, f (inA A B E hEA hEB a) = g (inA A B E hEA hEB a))
    (hB : ∀ b, f (inB A B E hEA hEB b) = g (inB A B E hEA hEB b)) : f = g := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  cases i
  · exact MonoidHom.ext hA
  · exact MonoidHom.ext hB

variable (D : Subgroup L) (hED : E ≤ D)

def toHNN : Amalgam A B E hEA hEB →* CentralizerHNN L D :=
  lift A B E hEA hEB ((centralizerOf D).comp A.subtype)
    ((MulAut.conj (centralizerStable D)⁻¹).toMonoidHom.comp
      ((centralizerOf D).comp B.subtype)) (by
        intro e
        have h := (centralizerOf_commute_stable_iff D (e : L)).mpr (hED e.property)
        exact h.symm.inv_mul_cancel.symm)

@[simp] theorem toHNN_inA (a : A) :
    toHNN A B E hEA hEB D hED (inA A B E hEA hEB a) = centralizerOf D (a : L) := by
  exact lift_inA A B E hEA hEB _ _ _ a

@[simp] theorem toHNN_inB (b : B) :
    toHNN A B E hEA hEB D hED (inB A B E hEA hEB b) =
      (centralizerStable D)⁻¹ * centralizerOf D (b : L) * centralizerStable D := by
  calc
    _ = MulAut.conj (centralizerStable D)⁻¹ (centralizerOf D (b : L)) :=
      lift_inB A B E hEA hEB _ _ _ b
    _ = _ := by simp

private def factorVal : ∀ i, Factor A B i →* L
  | false => A.subtype
  | true => B.subtype

private def letterVal (x : Σ i, Factor A B i) : L := factorVal A B x.1 x.2

private def listHead : List (Σ i, Factor A B i) → L
  | [] => 1
  | ⟨false, a⟩ :: xs => (a : L) * listHead xs
  | ⟨true, _⟩ :: _ => 1

private def listTail : List (Σ i, Factor A B i) → List (ℤˣ × L)
  | [] => []
  | ⟨false, _⟩ :: xs => listTail xs
  | ⟨true, b⟩ :: xs => (-1, (b : L)) :: (1, listHead A B xs) :: listTail xs

private theorem toSubgroup_self (u : ℤˣ) : HNNExtension.toSubgroup D D u = D := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

private theorem listHead_eq_one (xs : List (Σ i, Factor A B i))
    (h : ∀ x ∈ xs.head?, x.1 = true) : listHead A B xs = 1 := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      rcases x with ⟨i, x⟩
      cases i
      · have := h ⟨false, x⟩ (by simp)
        contradiction
      · rfl

private theorem listTail_chain (xs : List (Σ i, Factor A B i))
    (hc : xs.IsChain (fun x y => x.1 ≠ y.1))
    (hn : ∀ x ∈ xs, letterVal A B x ∉ D) :
    (listTail A B xs).IsChain (fun x y => x.2 ∈ D → x.1 = y.1) ∧
      ((∀ x ∈ xs.head?, x.1 = false) →
        ((1, listHead A B xs) :: listTail A B xs).IsChain
          (fun x y => x.2 ∈ D → x.1 = y.1)) := by
  induction xs with
  | nil => exact ⟨List.isChain_nil, fun _ => List.isChain_singleton _⟩
  | cons x xs ih =>
      have hct := (List.isChain_cons.mp hc).2
      have hnt : ∀ y ∈ xs, letterVal A B y ∉ D := fun y hy => hn y (by simp [hy])
      have hi := ih hct hnt
      rcases x with ⟨i, x⟩
      cases i
      · have hh : listHead A B xs = 1 := by
          apply listHead_eq_one
          intro y hy
          have hneq := (List.isChain_cons.mp hc).1 y hy
          cases h : y.1 <;> simp_all
        refine ⟨hi.1, fun _ => ?_⟩
        change ((1, (x : L) * listHead A B xs) :: listTail A B xs).IsChain _
        rw [hh, mul_one]
        apply List.IsChain.cons hi.1
        intro y hy hm
        exact False.elim (hn ⟨false, x⟩ (by simp) hm)
      · have ht : ∀ y ∈ xs.head?, y.1 = false := by
          intro y hy
          have hneq := (List.isChain_cons.mp hc).1 y hy
          cases h : y.1 <;> simp_all
        refine ⟨?_, ?_⟩
        · change ((-1, (x : L)) :: (1, listHead A B xs) :: listTail A B xs).IsChain _
          apply List.IsChain.cons (hi.2 ht)
          intro y hy hm
          exact False.elim (hn ⟨true, x⟩ (by simp) hm)
        · intro hf
          have := hf ⟨true, x⟩ (by simp)
          contradiction

private def listProd (xs : List (Σ i, Factor A B i)) : Amalgam A B E hEA hEB :=
  (xs.map fun (x : Σ i, Factor A B i) =>
    Monoid.PushoutI.of (φ := inclusions A B E hEA hEB) x.1 x.2).prod

private theorem toHNN_factor (i : Bool) (x : Factor A B i) :
    toHNN A B E hEA hEB D hED
      (Monoid.PushoutI.of (φ := inclusions A B E hEA hEB) i x) =
      if i then (centralizerStable D)⁻¹ * centralizerOf D (factorVal A B i x) *
        centralizerStable D else centralizerOf D (factorVal A B i x) := by
  cases i
  · exact toHNN_inA A B E hEA hEB D hED x
  · exact toHNN_inB A B E hEA hEB D hED x

private theorem encoded_product (xs : List (Σ i, Factor A B i)) :
    centralizerOf D (listHead A B xs) *
      ((listTail A B xs).map
        (fun p => centralizerStable D ^ (p.1 : ℤ) * centralizerOf D p.2)).prod =
      toHNN A B E hEA hEB D hED (listProd A B E hEA hEB xs) := by
  induction xs with
  | nil => simp [listHead, listTail, listProd]
  | cons x xs ih =>
      simp only [listProd] at ih
      rcases x with ⟨i, x⟩
      cases i
      · simp only [listHead, listTail, listProd, List.map_cons, List.prod_cons,
          map_mul]
        rw [toHNN_factor A B E hEA hEB D hED false x]
        simp only [Bool.false_eq_true, ite_false, factorVal]
        rw [mul_assoc, ih]
        rfl
      · simp only [listHead, listTail, listProd, List.map_cons, List.prod_cons,
          map_mul, map_one, one_mul]
        rw [toHNN_factor A B E hEA hEB D hED true x]
        simp only [ite_true, factorVal]
        simp only [Units.val_neg, Units.val_one, zpow_neg, zpow_one]
        rw [← ih]
        simp only [mul_assoc]
        rfl

@[simp] theorem toHNN_base (e : E) :
    toHNN A B E hEA hEB D hED
      (Monoid.PushoutI.base (inclusions A B E hEA hEB) e) =
        centralizerOf D (e : L) := by
  rw [← Monoid.PushoutI.of_apply_eq_base (inclusions A B E hEA hEB) false e]
  exact toHNN_inA A B E hEA hEB D hED _

private def encodedWord (e : E) (xs : List (Σ i, Factor A B i))
    (hc : xs.IsChain (fun x y => x.1 ≠ y.1))
    (hn : ∀ x ∈ xs, letterVal A B x ∉ D) :
    HNNExtension.NormalWord.ReducedWord L D D where
  head := (e : L) * listHead A B xs
  toList := listTail A B xs
  chain := by
    simpa only [toSubgroup_self] using (listTail_chain A B D xs hc hn).1

private theorem encodedWord_prod (e : E) (xs : List (Σ i, Factor A B i))
    (hc : xs.IsChain (fun x y => x.1 ≠ y.1))
    (hn : ∀ x ∈ xs, letterVal A B x ∉ D) :
    (encodedWord A B E D e xs hc hn).prod (MulEquiv.refl D) =
      toHNN A B E hEA hEB D hED
        (Monoid.PushoutI.base (inclusions A B E hEA hEB) e * listProd A B E hEA hEB xs) := by
  change centralizerOf D ((e : L) * listHead A B xs) *
    ((listTail A B xs).map
      (fun p => centralizerStable D ^ (p.1 : ℤ) * centralizerOf D p.2)).prod = _
  rw [map_mul, mul_assoc, encoded_product A B E hEA hEB D hED, map_mul, toHNN_base]

private theorem normalWord_not_mem_D
    (hA : D ⊓ A = E) (hB : D ⊓ B = E)
    (τ : Monoid.PushoutI.NormalWord.Transversal (inclusions A B E hEA hEB))
    (w : Monoid.PushoutI.NormalWord τ) :
    ∀ x ∈ w.toList, letterVal A B x ∉ D := by
  intro x hx hD
  have hnot : x.2 ∉ (inclusions A B E hEA hEB x.1).range := by
    intro hr
    have hn := w.normalized x.1 x.2 hx
    have hs := congrArg Subtype.val
      ((τ.compl x.1).equiv_snd_eq_self_of_mem_of_one_mem
        (Subgroup.one_mem _) hn)
    have hz := congrArg Subtype.val
      ((τ.compl x.1).equiv_snd_eq_one_of_mem_of_one_mem (τ.one_mem x.1) hr)
    exact w.ne_one x hx (hs.symm.trans hz)
  rcases x with ⟨i, x⟩
  cases i
  · have he : (x : L) ∈ E := by
      rw [← hA]
      exact ⟨hD, x.property⟩
    exact hnot ⟨⟨(x : L), he⟩, Subtype.ext rfl⟩
  · have he : (x : L) ∈ E := by
      rw [← hB]
      exact ⟨hD, x.property⟩
    exact hnot ⟨⟨(x : L), he⟩, Subtype.ext rfl⟩

private theorem normalWord_prod
    (τ : Monoid.PushoutI.NormalWord.Transversal (inclusions A B E hEA hEB))
    (w : Monoid.PushoutI.NormalWord τ) :
    w.prod = Monoid.PushoutI.base (inclusions A B E hEA hEB) w.head *
      listProd A B E hEA hEB w.toList := by
  simp only [Monoid.PushoutI.NormalWord.prod, Monoid.CoprodI.Word.prod,
    listProd, map_list_prod, List.map_map]
  congr 2

private theorem listProd_mem_range_inA (xs : List (Σ i, Factor A B i))
    (h : listTail A B xs = []) :
    listProd A B E hEA hEB xs ∈ (inA A B E hEA hEB).range := by
  induction xs with
  | nil => simp [listProd]
  | cons x xs ih =>
      rcases x with ⟨i, x⟩
      cases i
      · change inA A B E hEA hEB x * listProd A B E hEA hEB xs ∈ _
        exact Subgroup.mul_mem _ ⟨x, rfl⟩ (ih h)
      · simp only [listTail, List.cons_ne_nil] at h

/-- An element of the amalgam whose image belongs to the old HNN base
already lies in the first factor. This is the required base-intersection
part of the conjugated-amalgam normal-form theorem. -/
theorem toHNN_preimage_base (hA : D ⊓ A = E) (hB : D ⊓ B = E)
    (x : Amalgam A B E hEA hEB)
    (hx : toHNN A B E hEA hEB D hED x ∈ (centralizerOf D).range) :
    x ∈ (inA A B E hEA hEB).range := by
  classical
  obtain ⟨τ⟩ := Monoid.PushoutI.NormalWord.transversal_nonempty
    (inclusions A B E hEA hEB) (inclusions_injective A B E hEA hEB)
  let w : Monoid.PushoutI.NormalWord τ := Monoid.PushoutI.NormalWord.equiv x
  have hw : w.prod = x := (Monoid.PushoutI.NormalWord.equiv.symm_apply_apply x)
  have hn := normalWord_not_mem_D A B E hEA hEB D hA hB τ w
  let v := encodedWord A B E D w.head w.toList w.chain_ne hn
  have hv : v.prod (MulEquiv.refl D) = toHNN A B E hEA hEB D hED x := by
    rw [← hw, normalWord_prod A B E hEA hEB τ w]
    exact encodedWord_prod A B E hEA hEB D hED w.head w.toList w.chain_ne hn
  have hvbase : v.prod (MulEquiv.refl D) ∈ (centralizerOf D).range := hv ▸ hx
  have hvnil := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
    (MulEquiv.refl D) v hvbase
  rw [← hw, normalWord_prod A B E hEA hEB τ w]
  apply Subgroup.mul_mem
  · exact ⟨⟨(w.head : L), hEA w.head.property⟩,
      Monoid.PushoutI.of_apply_eq_base (inclusions A B E hEA hEB) false w.head⟩
  · exact listProd_mem_range_inA A B E hEA hEB w.toList hvnil

/-- The canonical map of the abstract amalgam into the centralizer HNN
extension is injective under the two exact intersection hypotheses. -/
theorem toHNN_injective (hA : D ⊓ A = E) (hB : D ⊓ B = E) :
    Function.Injective (toHNN A B E hEA hEB D hED) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hxbase : toHNN A B E hEA hEB D hED x ∈ (centralizerOf D).range := by
    rw [hx]
    exact Subgroup.one_mem _
  obtain ⟨a, rfl⟩ := toHNN_preimage_base A B E hEA hEB D hED hA hB x hxbase
  rw [toHNN_inA] at hx
  have ha : a = 1 := by
    apply Subtype.ext
    exact HNNExtension.of_injective (MulEquiv.refl D) (by simpa [centralizerOf] using hx)
  rw [ha, map_one]

/-- Conjugate the old base by the inverse stable letter. -/
def conjugatedOf : L →* CentralizerHNN L D :=
  (MulAut.conj (centralizerStable D)⁻¹).toMonoidHom.comp (centralizerOf D)

/-- The concrete subgroup generated by the old `A` and the conjugate of `B`. -/
def subgroup : Subgroup (CentralizerHNN L D) :=
  A.map (centralizerOf D) ⊔ B.map (conjugatedOf D)

/-- The abstract amalgam maps onto precisely the indicated concrete subgroup. -/
theorem toHNN_range :
    (toHNN A B E hEA hEB D hED).range = subgroup A B D := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    induction x using Monoid.PushoutI.induction_on with
    | of i g =>
        cases i
        · rw [show Monoid.PushoutI.of false g = inA A B E hEA hEB g from rfl, toHNN_inA]
          apply (show A.map (centralizerOf D) ≤ subgroup A B D from le_sup_left)
          exact ⟨g, g.property, rfl⟩
        · rw [show Monoid.PushoutI.of true g = inB A B E hEA hEB g from rfl, toHNN_inB]
          apply (show B.map (conjugatedOf D) ≤ subgroup A B D from le_sup_right)
          exact ⟨g, g.property, by simp [conjugatedOf]⟩
    | base e =>
        rw [toHNN_base]
        apply (show A.map (centralizerOf D) ≤ subgroup A B D from le_sup_left)
        exact ⟨e, hEA e.property, rfl⟩
    | mul x y hx hy =>
        rw [map_mul]
        exact Subgroup.mul_mem _ hx hy
  · apply sup_le
    · rintro y ⟨a, ha, rfl⟩
      exact ⟨inA A B E hEA hEB ⟨a, ha⟩, toHNN_inA A B E hEA hEB D hED _⟩
    · rintro y ⟨b, hb, rfl⟩
      refine ⟨inB A B E hEA hEB ⟨b, hb⟩, ?_⟩
      simp [conjugatedOf]

include hEA hEB hED in
/-- The generated subgroup meets the original HNN base exactly in `A`. -/
theorem subgroup_inf_base (hA : D ⊓ A = E) (hB : D ⊓ B = E) :
    subgroup A B D ⊓ (centralizerOf D).range = A.map (centralizerOf D) := by
  rw [← toHNN_range A B E hEA hEB D hED]
  apply le_antisymm
  · rintro x ⟨⟨y, hy⟩, hx⟩
    have hybase : toHNN A B E hEA hEB D hED y ∈ (centralizerOf D).range := hy ▸ hx
    obtain ⟨a, rfl⟩ := toHNN_preimage_base A B E hEA hEB D hED hA hB y hybase
    rw [toHNN_inA] at hy
    exact ⟨a, a.property, hy⟩
  · rintro x ⟨a, ha, rfl⟩
    exact ⟨⟨inA A B E hEA hEB ⟨a, ha⟩, toHNN_inA A B E hEA hEB D hED _⟩,
      ⟨a, rfl⟩⟩

end UniversalGroup.ConjugatedAmalgam
