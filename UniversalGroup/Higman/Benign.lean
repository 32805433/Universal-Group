module

public import UniversalGroup.Foundations.FinitePresentation.Products
public import UniversalGroup.Foundations.Amalgam.Conjugated

@[expose] public section

/-!
# Benign subgroups and Higman's final embedding construction

The double formulation of benignity is condition (iii) of Higman (1961),
Lemma 3.5. The final construction below is the argument on pages 474–475:
the quotient by a benign normal subgroup embeds in a finitely presented
group because its infinitely many defining relations follow from finitely
many conjugation relations.
-/

namespace UniversalGroup.HigmanBenign

noncomputable section

universe u
variable {F : Type u} [Group F]

/-- The amalgamated double of a group over one of its subgroups. -/
abbrev Double (N : Subgroup F) :=
  Monoid.PushoutI (fun (_ : Bool) => N.subtype)

/-- The two factors of the amalgamated double. -/
def factor (N : Subgroup F) (i : Bool) : F →* Double N :=
  Monoid.PushoutI.of (φ := fun (_ : Bool) => N.subtype) i

theorem factors_agree (N : Subgroup F) (a : N) :
    factor N false a = factor N true a :=
  (Monoid.PushoutI.of_apply_eq_base (fun (_ : Bool) => N.subtype) false a).trans
    (Monoid.PushoutI.of_apply_eq_base (fun (_ : Bool) => N.subtype) true a).symm

/-- Higman's double formulation of benignity (Lemma 3.5(iii)). -/
def Benign (N : Subgroup F) : Prop :=
  ∃ (K : Type u) (_ : Group K), Group.IsFinitelyPresented K ∧
    ∃ e : Double N →* K, Function.Injective e


/-- Intersecting a finitely generated subgroup of a finitely presented
overgroup with an embedded group gives a benign subgroup. This is the
implication (i) ⇒ (iii) in Higman (1961), Lemma 3.5. -/
theorem benign_comap {K : Type u} [Group K] [Group.IsFinitelyPresented K]
    (f : F →* K) (hf : Function.Injective f) (V : Subgroup K) [Group.FG V] :
    Benign (V.comap f) := by
  let N := V.comap f
  let A := f.range
  let E : Subgroup K := V ⊓ A
  let hEA : E ≤ A := inf_le_right
  let hEV : E ≤ V := inf_le_left
  let D := ConjugatedAmalgam.Amalgam A A E hEA hEA
  let e : F ≃* A := equivRangeOfInjective f hf
  let common : N →* E :=
    { toFun := fun a => ⟨f a, ⟨a.property, ⟨a, rfl⟩⟩⟩
      map_one' := by apply Subtype.ext; exact map_one f
      map_mul' := by intros; apply Subtype.ext; exact map_mul f _ _ }
  have he (a : F) : (e a : K) = f a := rfl
  let maps : ∀ i : Bool, F →* D := fun i => match i with
    | false => (ConjugatedAmalgam.inA A A E hEA hEA).comp e.toMonoidHom
    | true => (ConjugatedAmalgam.inB A A E hEA hEA).comp e.toMonoidHom
  have hmaps : ∀ i, (maps i).comp N.subtype =
      (ConjugatedAmalgam.inA A A E hEA hEA).comp
        ((Subgroup.inclusion hEA).comp common) := by
    intro i
    cases i
    · rfl
    · ext a
      exact (ConjugatedAmalgam.identify A A E hEA hEA (common a)).symm
  let forward : Double N →* D := Monoid.PushoutI.lift maps _ hmaps
  have hback (a : E) :
      factor N false (e.symm ⟨a, hEA a.property⟩) =
        factor N true (e.symm ⟨a, hEA a.property⟩) := by
    have ha : e.symm ⟨a, hEA a.property⟩ ∈ N := by
      change f (e.symm ⟨a, hEA a.property⟩) ∈ V
      rw [← he, e.apply_symm_apply]
      exact a.property.1
    exact factors_agree N ⟨_, ha⟩
  let backward : D →* Double N :=
    ConjugatedAmalgam.lift A A E hEA hEA
      ((factor N false).comp e.symm.toMonoidHom)
      ((factor N true).comp e.symm.toMonoidHom) hback
  have hbackforward : backward.comp forward = MonoidHom.id (Double N) := by
    apply Monoid.PushoutI.hom_ext_nonempty
    intro i
    ext a
    cases i
    · change backward (forward (factor N false a)) = factor N false a
      rw [show forward (factor N false a) = ConjugatedAmalgam.inA A A E hEA hEA (e a) from
        Monoid.PushoutI.lift_of (φ := fun (_ : Bool) => N.subtype) _ _ _ (i := false) a]
      change ConjugatedAmalgam.lift A A E hEA hEA _ _ hback
        (ConjugatedAmalgam.inA A A E hEA hEA (e a)) = _
      exact (ConjugatedAmalgam.lift_inA A A E hEA hEA _ _ hback (e a)).trans
        (congrArg (factor N false) (e.symm_apply_apply a))
    · change backward (forward (factor N true a)) = factor N true a
      rw [show forward (factor N true a) = ConjugatedAmalgam.inB A A E hEA hEA (e a) from
        Monoid.PushoutI.lift_of (φ := fun (_ : Bool) => N.subtype) _ _ _ (i := true) a]
      change ConjugatedAmalgam.lift A A E hEA hEA _ _ hback
        (ConjugatedAmalgam.inB A A E hEA hEA (e a)) = _
      exact (ConjugatedAmalgam.lift_inB A A E hEA hEA _ _ hback (e a)).trans
        (congrArg (factor N true) (e.symm_apply_apply a))
  have hforward : Function.Injective forward := by
    intro x y hxy
    have h := congrArg backward hxy
    simpa only [← MonoidHom.comp_apply, hbackforward, MonoidHom.id_apply] using h
  let into : D →* HNNLemmas.CentralizerHNN K V :=
    ConjugatedAmalgam.toHNN A A E hEA hEA V hEV
  have hinto : Function.Injective into :=
    ConjugatedAmalgam.toHNN_injective A A E hEA hEA V hEV rfl rfl
  refine ⟨HNNLemmas.CentralizerHNN K V, inferInstance, ?_, into.comp forward,
    hinto.comp hforward⟩
  exact PreparationFinite.hnnExtension V V (MulEquiv.refl V)

/-- The intersection formulation with a separately named subgroup. -/
theorem benign_of_intersection {K : Type u} [Group K] [Group.IsFinitelyPresented K]
    (f : F →* K) (hf : Function.Injective f) (V : Subgroup K) [Group.FG V]
    (N : Subgroup F) (hN : V.comap f = N) : Benign N := by
  rw [← hN]
  exact benign_comap f hf V

section Model

variable (N : Subgroup F)
variable {K : Type u} [Group K] (e : Double N →* K) (he : Function.Injective e)

def quotientFactors (i : Bool) : F →* F ⧸ Subgroup.normalClosure (N : Set F) :=
  if i then 1 else QuotientGroup.mk' (Subgroup.normalClosure (N : Set F))

/-- Retain the quotient on the first copy of the double and kill the second. -/
def quotientDouble : Double N →* F ⧸ Subgroup.normalClosure (N : Set F) :=
  Monoid.PushoutI.lift (quotientFactors N) 1 (by
    intro i
    cases i
    · ext a
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure a.property)
    · rfl)

@[simp] theorem quotientDouble_false (a : F) :
    quotientDouble N (factor N false a) = QuotientGroup.mk' (Subgroup.normalClosure (N : Set F)) a := by
  exact Monoid.PushoutI.lift_of (φ := fun (_ : Bool) => N.subtype) _ _ _ (i := false) a

@[simp] theorem quotientDouble_true (a : F) :
    quotientDouble N (factor N true a) = 1 := by
  exact Monoid.PushoutI.lift_of (φ := fun (_ : Bool) => N.subtype) _ _ _ (i := true) a

/-- The unchanged copy of the double in `K × (F/N)`. -/
def plain : Double N →* K × (F ⧸ Subgroup.normalClosure (N : Set F)) := e.prod 1

/-- The twisted copy, with the quotient recorded in its second coordinate. -/
def twisted : Double N →* K × (F ⧸ Subgroup.normalClosure (N : Set F)) := e.prod (quotientDouble N)

include he in
theorem plain_injective : Function.Injective (plain N e) := by
  intro x y h
  exact he (congrArg Prod.fst h)

include he in
theorem twisted_injective : Function.Injective (twisted N e) := by
  intro x y h
  exact he (congrArg Prod.fst h)

/-- The group containing the quotient, used to verify the finite presentation. -/
abbrev Model := IdentifyingHNN (plain N e) (twisted N e)
  (plain_injective N e he) (twisted_injective N e he)

def modelBase : K × (F ⧸ Subgroup.normalClosure (N : Set F)) →* Model N e he :=
  IdentifyingHNN.of _ _ _ _

def modelStable : Model N e he := IdentifyingHNN.stable _ _ _ _

def modelInput : F ⧸ Subgroup.normalClosure (N : Set F) →* Model N e he :=
  (modelBase N e he).comp (MonoidHom.inr K (F ⧸ Subgroup.normalClosure (N : Set F)))

theorem modelInput_injective : Function.Injective (modelInput N e he) := by
  intro x y h
  exact congrArg Prod.snd (IdentifyingHNN.of_injective _ _ _ _ h)

theorem model_conjugates (a : F) (i : Bool) :
    (modelStable N e he)⁻¹ * modelBase N e he (e (factor N i a), 1) *
      modelStable N e he =
    modelBase N e he (e (factor N i a), if i then 1 else QuotientGroup.mk' (Subgroup.normalClosure (N : Set F)) a) := by
  have h := IdentifyingHNN.conjugates (plain N e) (twisted N e)
    (plain_injective N e he) (twisted_injective N e he) (factor N i a)
  change (modelStable N e he)⁻¹ * modelBase N e he (e (factor N i a), 1) *
    modelStable N e he = modelBase N e he
      (e (factor N i a), quotientDouble N (factor N i a)) at h
  cases i <;> simpa only [Bool.false_eq_true, ↓reduceIte,
    quotientDouble_false, quotientDouble_true] using h

end Model

/-- Conjugating every value of a homomorphism gives a homomorphism. -/
private def conjugateHom {G H : Type*} [Group G] [Group H]
    (z : H) (f : G →* H) : G →* H where
  toFun a := z⁻¹ * f a * z
  map_one' := by simp
  map_mul' a b := by simp [mul_assoc]

/-- An abstract group embeds in some finitely presented group of the same universe. -/
def EmbedsInFP (G : Type u) [Group G] : Prop :=
  ∃ (K : Type u) (_ : Group K), Group.IsFinitelyPresented K ∧
    ∃ e : G →* K, Function.Injective e

/-- The HNN formulation of benignity implies the double formulation.
A conjugate of the finitely generated base group supplies the subgroup in
the intersection formulation of Lemma 3.5. -/
theorem benign_of_centralizer [Group.FG F] (N : Subgroup F)
    (h : EmbedsInFP (HNNLemmas.CentralizerHNN F N)) : Benign N := by
  obtain ⟨K, instK, hK, e, he⟩ := h
  let : Group K := instK
  let : Group.IsFinitelyPresented K := hK
  let base : F →* HNNLemmas.CentralizerHNN F N := HNNLemmas.centralizerOf N
  let t := HNNLemmas.centralizerStable N
  let conjugated : F →* HNNLemmas.CentralizerHNN F N :=
    (MulAut.conj t⁻¹).toMonoidHom.comp base
  let retraction : HNNLemmas.CentralizerHNN F N →* F :=
    HNNExtension.lift (MonoidHom.id F) 1 (by intro a; simp)
  have retract_base (x : F) : retraction (base x) = x :=
    HNNExtension.lift_of _ _ _ _
  have retract_t : retraction t = 1 := HNNExtension.lift_t _ _ _
  let f : F →* K := e.comp base
  have hf : Function.Injective f := he.comp (HNNExtension.of_injective _)
  let V := (e.comp conjugated).range
  have hVN : V.comap f = N := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      change e (conjugated y) = e (base x) at hy
      have hxy := he hy
      change t⁻¹ * base y * t = base x at hxy
      have h := congrArg retraction hxy
      rw [map_mul, map_mul, map_inv, retract_t, retract_base, retract_base] at h
      have hyx : y = x := by simpa using h
      subst y
      apply (HNNLemmas.centralizerOf_commute_stable_iff N x).mp
      change Commute (base x) t
      apply (commute_iff_eq _ _).mpr
      have hh := congrArg (fun z => t * z) hxy
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh
    · intro hx
      refine ⟨x, ?_⟩
      change e (t⁻¹ * base x * t) = e (base x)
      apply congrArg e
      exact ((HNNLemmas.centralizerOf_commute_stable_iff N x).mpr hx).symm.inv_mul_cancel
  exact benign_of_intersection f hf V N hVN

set_option backward.isDefEq.respectTransparency false in
/-- Higman's final construction: a quotient of a finitely presented group
by the normal closure of a benign subgroup embeds in a finitely presented group.
This is the last argument of Higman (1961), pages 474–475. -/
theorem normalClosure_quotient_embedsInFP [Group.IsFinitelyPresented F]
    (N : Subgroup F) (hN : Benign N) : EmbedsInFP (F ⧸ Subgroup.normalClosure (N : Set F)) := by
  classical
  obtain ⟨K, instK, hK, e, he⟩ := hN
  let : Group K := instK
  let : Group.IsFinitelyPresented K := hK
  let : Group.IsFinitelyPresented (K × F) := PreparationFinite.prod K F
  obtain ⟨_, fF, hfF, _⟩ := (inferInstance : Group.IsFinitelyPresented F).out
  let : Group.FG F := Group.fg_of_surjective hfF
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG F)
  let B := Monoid.Coprod (K × F) (Multiplicative ℤ)
  let z : B := Monoid.Coprod.inr (Multiplicative.ofAdd 1)
  let left (i : Bool) : F →* B :=
    Monoid.Coprod.inl.comp ((e.comp (factor N i)).prod 1)
  let right (i : Bool) : F →* B :=
    Monoid.Coprod.inl.comp ((e.comp (factor N i)).prod
      (if i then 1 else MonoidHom.id F))
  let rel (p : Bool × F) : B :=
    z⁻¹ * left p.1 p.2 * z * (right p.1 p.2)⁻¹
  let T : Set B := rel '' (Set.univ ×ˢ S)
  let M := Subgroup.normalClosure T
  let H := B ⧸ M
  let q : B →* H := QuotientGroup.mk' M
  let input : F →* H := q.comp (Monoid.Coprod.inl.comp (MonoidHom.inr K F))
  have conjugates (i : Bool) : conjugateHom (q z) (q.comp (left i)) =
      q.comp (right i) := by
    apply MonoidHom.eq_of_eqOn_dense hS
    intro a ha
    have hm : rel (i, a) ∈ M :=
      Subgroup.subset_normalClosure ⟨(i, a), ⟨Set.mem_univ _, ha⟩, rfl⟩
    have hq : q (rel (i, a)) = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    change (q z)⁻¹ * q (left i a) * q z * (q (right i a))⁻¹ = 1 at hq
    exact mul_inv_eq_one.mp hq
  have kills : N ≤ input.ker := by
    intro a ha
    have hl := DFunLike.congr_fun (conjugates false) a
    have hr := DFunLike.congr_fun (conjugates true) a
    change (q z)⁻¹ * q (left false a) * q z = q (right false a) at hl
    change (q z)⁻¹ * q (left true a) * q z = q (right true a) at hr
    have heq : q (left false a) = q (left true a) := by
      apply congrArg q
      change Monoid.Coprod.inl (e (factor N false a), 1) =
        Monoid.Coprod.inl (e (factor N true a), 1)
      rw [factors_agree N ⟨a, ha⟩]
    have hp : q (right false a) = q (left false a) * input a := by
      change q (right false a) = q (left false a) * q (Monoid.Coprod.inl (1, a))
      rw [← map_mul]
      apply congrArg q
      change Monoid.Coprod.inl (e (factor N false a), a) =
        Monoid.Coprod.inl (e (factor N false a), 1) * Monoid.Coprod.inl (1, a)
      rw [← map_mul]
      simp
    have ht : q (right true a) = q (left true a) := rfl
    change input a = 1
    apply mul_left_cancel (a := q (left false a))
    rw [mul_one, ← hp, ← hl, heq, hr, ht]
  let embedding : F ⧸ Subgroup.normalClosure (N : Set F) →* H := QuotientGroup.lift (Subgroup.normalClosure (N : Set F)) input
    (Subgroup.normalClosure_le_normal kills)
  let baseMap : K × F →* Model N e he :=
    (modelBase N e he).comp ((MonoidHom.id K).prodMap (QuotientGroup.mk' (Subgroup.normalClosure (N : Set F))))
  let detect : B →* Model N e he :=
    Monoid.Coprod.lift baseMap (zpowersHom _ (modelStable N e he))
  have detect_z : detect z = modelStable N e he := by
    change Monoid.Coprod.lift baseMap (zpowersHom _ (modelStable N e he))
      (Monoid.Coprod.inr (Multiplicative.ofAdd 1)) = _
    rw [Monoid.Coprod.lift_apply_inr]
    change (modelStable N e he) ^ (1 : ℤ) = modelStable N e he
    exact zpow_one (modelStable N e he)
  have detect_left (i : Bool) (a : F) :
      detect (left i a) = modelBase N e he (e (factor N i a), 1) := by
    change Monoid.Coprod.lift baseMap (zpowersHom _ (modelStable N e he))
      (Monoid.Coprod.inl (e (factor N i a), 1)) = _
    rw [Monoid.Coprod.lift_apply_inl]
    change modelBase N e he (e (factor N i a), QuotientGroup.mk' (Subgroup.normalClosure (N : Set F)) 1) = _
    rw [map_one]
  have detect_right (i : Bool) (a : F) :
      detect (right i a) = modelBase N e he
        (e (factor N i a), if i then 1 else QuotientGroup.mk' (Subgroup.normalClosure (N : Set F)) a) := by
    cases i
    · change Monoid.Coprod.lift baseMap (zpowersHom _ (modelStable N e he))
        (Monoid.Coprod.inl (e (factor N false a), a)) = _
      rw [Monoid.Coprod.lift_apply_inl]
      rfl
    · change Monoid.Coprod.lift baseMap (zpowersHom _ (modelStable N e he))
        (Monoid.Coprod.inl (e (factor N true a), 1)) = _
      rw [Monoid.Coprod.lift_apply_inl]
      change modelBase N e he (e (factor N true a), QuotientGroup.mk' (Subgroup.normalClosure (N : Set F)) 1) = _
      rw [map_one]
      rfl
  have detect_kills : M ≤ detect.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨⟨i, a⟩, _, rfl⟩
    change detect (rel (i, a)) = 1
    change detect (z⁻¹ * left i a * z * (right i a)⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, detect_z, detect_left, detect_right]
    rw [model_conjugates]
    exact mul_inv_cancel _
  let detector : H →* Model N e he := QuotientGroup.lift M detect detect_kills
  have detects (a : F ⧸ Subgroup.normalClosure (N : Set F)) : detector (embedding a) = modelInput N e he a := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.normalClosure (N : Set F)) a
    change detector (input a) = modelInput N e he (QuotientGroup.mk' (Subgroup.normalClosure (N : Set F)) a)
    change detect (Monoid.Coprod.inl (1, a)) =
      modelBase N e he (1, QuotientGroup.mk' (Subgroup.normalClosure (N : Set F)) a)
    change Monoid.Coprod.lift baseMap (zpowersHom _ (modelStable N e he))
      (Monoid.Coprod.inl (1, a)) = _
    rw [Monoid.Coprod.lift_apply_inl]
    rfl
  have hi : Function.Injective embedding := by
    intro a b hab
    apply modelInput_injective N e he
    rw [← detects a, ← detects b, hab]
  have hM : M.IsFinitelyNormallyGenerated :=
    ⟨T, (Set.toFinite (Set.univ : Set Bool) |>.prod hSfin).image rel, rfl⟩
  exact ⟨H, inferInstance, Group.IsFinitelyPresented.quotient M hM, embedding, hi⟩

/-- The usual normal-subgroup form of Higman's final construction. -/
theorem quotient_embedsInFP [Group.IsFinitelyPresented F]
    (N : Subgroup F) [N.Normal] (hN : Benign N) : EmbedsInFP (F ⧸ N) := by
  obtain ⟨K, instK, hK, e, he⟩ := normalClosure_quotient_embedsInFP N hN
  let q : (F ⧸ N) ≃* (F ⧸ Subgroup.normalClosure (N : Set F)) :=
    QuotientGroup.quotientMulEquivOfEq (Subgroup.normalClosure_eq_self N).symm
  exact ⟨K, instK, hK, e.comp q.toMonoidHom, he.comp q.injective⟩

end
end UniversalGroup.HigmanBenign
