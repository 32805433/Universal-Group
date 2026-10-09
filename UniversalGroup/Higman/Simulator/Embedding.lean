module

public import UniversalGroup.Simulator.Recognition.FiniteRank.Intersection
public import UniversalGroup.Higman.Diagonal

@[expose] public section

/-! The free diagonal group embeds in the simulator; its recognized subgroup is benign. -/
namespace UniversalGroup.HigmanSimulatorB
noncomputable section
open HNNLemmas
set_option maxHeartbeats 1000000
variable {k : ℕ} (D : Data k)

private theorem codeCore_injective : Function.Injective (codeCore D) :=
  (SimulatorFreeLetters.coreLetters_injective D.words D.F_support D.E_support).comp D.code_injective

private theorem codeCore_inf_CD : (codeCore D).range ⊓ CD D = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨⟨g,rfl⟩,hg⟩
  have h : codeCore D g ∈ (SimulatorFreeLetters.coreLetters D.words D.F_support D.E_support).range ⊓ CD D :=
    ⟨codeCore_mem_letters D g,hg⟩
  rwa [SimulatorFreeLetters.coreLetters_inf_CD] at h

private theorem baseLift_injective : Function.Injective (baseLift D) :=
  AdjoinFree.hom_injective _ _ (codeCore_injective D) (codeCore_inf_CD D)

private abbrev Restricted :=
  HNNExtension (Base D) (restrictedA (A := (left D).range) (Base D))
    (restrictedB (B := (right D).range) (Base D))
    (restrictedPhi (phi := phi D) (Base D) (preserves_B D))

private def baseEquiv : FreeGroup (Fin (k+1)) ≃* Base D :=
  MonoidHom.ofInjective (baseLift_injective D)

private def inputBase : FreeGroup (Fin k) →* Base D :=
  (baseEquiv D).toMonoidHom.comp (FreeGroup.map Fin.castSucc)

private theorem inputBase_val (g : FreeGroup (Fin k)) :
    (inputBase D g : FStage D) = codeValue D g :=
  DFunLike.congr_fun (AdjoinFree.hom_comp_old (CD D) (codeCore D)) g

private def fBase : Base D := ⟨f D,f_mem_base D⟩

private theorem baseEquiv_last : baseEquiv D (FreeGroup.of (Fin.last k)) = fBase D := by
  apply Subtype.ext
  exact baseLift_f D

private def toRestricted : HigmanDelta.Base (FreeGroup (Fin k)) →* Restricted D :=
  Monoid.Coprod.lift (HNNExtension.of.comp (inputBase D))
    (FreeGroup.lift ![HNNExtension.of (fBase D),HNNExtension.t⁻¹])

private def decodeBase : Base D →* HigmanDelta.Base (FreeGroup (Fin k)) :=
  (FreeGroup.lift (Fin.lastCases (HigmanDelta.letter 0)
    (fun i => HigmanDelta.of (FreeGroup.of i)))).comp (baseEquiv D).symm.toMonoidHom

private theorem leftBase_eq_one
    (a : restrictedA (A := (left D).range) (Base D)) : a = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  rcases a.property with ⟨c,hc⟩
  rcases c.property with ⟨v,hv,hvc⟩
  have hc' : ofCore D (pCore D * v * (pCore D)⁻¹) = ((a : Base D) : FStage D) := by
    simpa only [left, TwistedCentralizer.left_apply, marker, SimulatorDModel.marker,
      ← hvc, map_mul, map_inv, Subgroup.subtype_apply] using hc
  have hvone := attaching_left_disjoint D v hv (hc' ▸ (a : Base D).property)
  simpa [hvone] using hc'.symm

private def fromRestricted : Restricted D →* HigmanDelta.Base (FreeGroup (Fin k)) :=
  HNNExtension.lift (decodeBase D) (HigmanDelta.letter 1)⁻¹ (by
    intro a
    rw [leftBase_eq_one D a]
    simp)

private theorem toRestricted_injective : Function.Injective (toRestricted D) := by
  have h : (fromRestricted D).comp (toRestricted D) = MonoidHom.id _ := by
    apply Monoid.Coprod.hom_ext
    · apply FreeGroup.ext_hom
      intro i
      simp [toRestricted, fromRestricted, decodeBase, inputBase, HigmanDelta.of]
    · apply FreeGroup.ext_hom
      intro i
      fin_cases i
      · simp only [MonoidHom.comp_apply, toRestricted, Monoid.Coprod.lift_apply_inr,
          FreeGroup.lift_apply_of, fromRestricted]
        rw [← baseEquiv_last D]
        simp [decodeBase, HigmanDelta.letter]
      · simp [toRestricted, fromRestricted, HigmanDelta.letter]
  exact Function.LeftInverse.injective (fun x => DFunLike.congr_fun h x)

/-- The literal copy of the free group on the input codes, f and T. -/
def embedding : HigmanDelta.Base (FreeGroup (Fin k)) →* (simulatorL D.words).Group :=
  Monoid.Coprod.lift (literalCode D)
    (FreeGroup.lift ![SimulatorRelations.f D.words,SimulatorRecognitionForward.target D.words])

@[simp] theorem embedding_of (g : FreeGroup (Fin k)) :
    embedding D (HigmanDelta.of g) = literalCode D g := Monoid.Coprod.lift_apply_inl _ _ _

@[simp] theorem embedding_letter (i : Fin 2) :
    embedding D (HigmanDelta.letter i) =
      ![SimulatorRelations.f D.words,SimulatorRecognitionForward.target D.words] i := by
  change Monoid.Coprod.lift _ _ (Monoid.Coprod.inr (FreeGroup.of i)) = _
  rw [Monoid.Coprod.lift_apply_inr,FreeGroup.lift_apply_of]

@[simp] theorem embedding_delta (g : FreeGroup (Fin k)) :
    embedding D (HigmanDelta.delta g) = delta D g := by
  simp [HigmanDelta.delta,delta]

theorem embedding_injective : Function.Injective (embedding D) := by
  let j := restrictedEmbedding (phi := phi D) (Base D) (preserves_B D)
  have h : (toLiteral D).comp (j.comp (toRestricted D)) = embedding D := by
    apply Monoid.Coprod.hom_ext
    · apply MonoidHom.ext
      intro g
      simp only [MonoidHom.comp_apply, toRestricted, Monoid.Coprod.lift_apply_inl,
        restrictedEmbedding_of, j]
      rw [inputBase_val]
      exact SimulatorDModel.toLiteral_of D.words D.F_support D.E_support _
    · apply FreeGroup.ext_hom
      intro i
      fin_cases i
      · simp only [MonoidHom.comp_apply, toRestricted, Monoid.Coprod.lift_apply_inr,
          FreeGroup.lift_apply_of]
        change toLiteral D (TwistedCentralizer.of (attaching D) (marker D) (f D) (f D)) = _
        rw [SimulatorDModel.toLiteral_of,SimulatorModel.fromF_stable]
        rfl
      · simp [toRestricted, embedding, j, toLiteral_t]
  rw [← h]
  exact (SimulatorDModel.toLiteral_injective D.words D.F_support D.E_support).comp
    ((restrictedEmbedding_injective (phi := phi D) (Base D) (preserves_B D)).comp
      (toRestricted_injective D))

private theorem literalCode_mem_B (g : FreeGroup (Fin k)) : literalCode D g ∈ B D := by
  apply Subgroup.subset_closure
  exact Or.inl ⟨codeValue D g,(ofCore_mem_base_iff D _).2 ⟨g,rfl⟩,rfl⟩

private theorem f_mem_B : SimulatorRelations.f D.words ∈ B D := by
  apply Subgroup.subset_closure
  exact Or.inl ⟨f D,f_mem_base D,SimulatorModel.fromF_stable D.words D.F_support D.E_support⟩

private theorem target_mem_B : SimulatorRecognitionForward.target D.words ∈ B D :=
  Subgroup.subset_closure (Or.inr rfl)

theorem embedding_range_le_B : (embedding D).range ≤ B D := by
  rintro x ⟨g,rfl⟩
  induction g using Monoid.Coprod.induction_on with
  | inl g => exact literalCode_mem_B D g
  | inr g =>
    induction g using FreeGroup.induction_on with
    | one => simp
    | of i =>
        change embedding D (HigmanDelta.letter i) ∈ B D
        rw [embedding_letter]
        fin_cases i
        · exact f_mem_B D
        · exact target_mem_B D
    | inv_of i ih => simpa only [map_inv] using (B D).inv_mem ih
    | mul a b ha hb => simpa only [map_mul] using (B D).mul_mem ha hb
  | mul a b ha hb => simpa only [map_mul] using (B D).mul_mem ha hb

/-- The preimage of the finitely generated simulator subgroup is exactly
its recognized diagonal subgroup. -/
theorem diagonal_eq_comap : HigmanDelta.subgroup {g | Accepted D g} =
    (simulatorD D.words).comap (embedding D) := by
  have hm : (HigmanDelta.subgroup {g | Accepted D g}).map (embedding D) = recognition D := by
    rw [HigmanDelta.subgroup, MonoidHom.map_closure, Set.image_image]
    simp only [embedding_delta,recognition]
  apply le_antisymm
  · intro x hx
    exact recognition_le_D D (hm ▸ (show embedding D x ∈
      (HigmanDelta.subgroup {g | Accepted D g}).map (embedding D) from ⟨x,hx,rfl⟩))
  · intro x hx
    have hrec := intersection_le D ⟨hx,embedding_range_le_B D ⟨x,rfl⟩⟩
    rw [← hm] at hrec
    rcases hrec with ⟨y,hy,hyx⟩
    exact embedding_injective D hyx ▸ hy

/-- Every arbitrary-rank signed-code recognition set gives a benign diagonal subgroup. -/
theorem diagonal_benign : HigmanBenign.Benign (HigmanDelta.subgroup {g | Accepted D g}) := by
  rw [diagonal_eq_comap]
  let : Finite (simulatorL D.words).relSet := (Set.finite_range _).to_subtype
  let : Group.FG (simulatorD D.words) := (Group.fg_iff_subgroup_fg _).2 ((Subgroup.fg_iff _).2 ⟨_,rfl,Set.finite_range _⟩)
  apply HigmanBenign.benign_comap (embedding D) (embedding_injective D)

end
end UniversalGroup.HigmanSimulatorB
