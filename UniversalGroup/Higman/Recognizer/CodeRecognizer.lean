module

public import UniversalGroup.Higman.Recognizer.Code
public import UniversalGroup.Simulator.Recognition.FiniteRank.Intersection
public import UniversalGroup.Higman.PositiveKernel

@[expose] public section

/-! The fixed-boundary code recognizer supplies the simulator's exact accepted set. -/
namespace UniversalGroup.HigmanCodeRecognizer
noncomputable section

variable {k r : ℕ} (I : HigmanCode.Input (Fin k) r) (u : ℕ)
  (W : CodeWords) (hF : ∀ i,ContainsBoth (W.F i)) (hE : ∀ i,ContainsBoth (W.E i))

def words : CodeWords := { W with P := I.marker u }

@[simp] theorem words_rules : (words I u W).rules=W.rules := rfl
@[simp] theorem words_marker : (words I u W).P=I.marker u := rfl

/-- The three compiler rules, the fixed-boundary marker, and the injected
conjugated input code form the simulator's full input data. -/
def data : HigmanSimulatorB.Data k where
  words := words I u W
  F_support := hF
  E_support := hE
  code := I.hom
  code_injective := I.hom_injective

theorem positive_eq (w : List (Fin k)) : HigmanCode.positive w=PositiveKernel.positive w :=
  (PositiveKernel.positive_eq_mk w).symm

/-- The group-theoretic accepted predicate has exactly the desired positive
fixed-boundary word interpretation. -/
theorem accepted_iff (g : FreeGroup (Fin k)) :
    HigmanSimulatorB.Accepted (data I u W hF hE) g ↔
      ∃ w : List (Fin k),g=PositiveKernel.positive w ∧
        PositiveEq W.rules (I.spelling u w) (I.marker u) := by
  constructor
  · rintro ⟨Q,hQ,hrec⟩
    have hQ' : I.hom g*CodeSubgroups.positiveFree (I.marker u)=CodeSubgroups.positiveFree Q := by
      simpa only [data,words,BorisovCStage.positiveFree_eq_eval,CodeSubgroups.positiveFree] using hQ
    obtain ⟨w,hg,hw⟩ := I.hom_mul_marker_positive u g Q hQ'
    refine ⟨w,hg.trans (positive_eq w),?_⟩
    simpa only [data,words,hw,CodeWords.rules] using hrec
  · rintro ⟨w,hg,hrec⟩
    refine ⟨I.spelling u w,?_,hrec⟩
    have h := I.positive_spelling u w
    rw [positive_eq,←hg] at h
    simpa only [data,words,BorisovCStage.positiveFree_eq_eval,CodeSubgroups.positiveFree] using h

/-- A literal recognizer for the positive word problem recognizes exactly
the positive elements of the kernel, including arbitrary signed outer inputs. -/
theorem accepted_iff_elements {G : Type*} [Group G] (π : FreeGroup (Fin k) →* G)
    (hrec : ∀ w : List (Fin k),
      PositiveEq W.rules (I.spelling u w) (I.marker u) ↔ π (PositiveKernel.positive w)=1)
    (g : FreeGroup (Fin k)) :
    HigmanSimulatorB.Accepted (data I u W hF hE) g ↔ g∈PositiveKernel.elements π := by
  rw [accepted_iff]
  constructor
  · rintro ⟨w,rfl,hw⟩
    exact ⟨w,rfl,(hrec w).mp hw⟩
  · rintro ⟨w,hw,hg⟩
    exact ⟨w,hw.symm,(hrec w).mpr (hw ▸ hg)⟩

end
end UniversalGroup.HigmanCodeRecognizer
