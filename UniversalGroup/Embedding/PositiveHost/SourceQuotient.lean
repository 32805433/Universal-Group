module

public import UniversalGroup.Embedding.PositiveHost.SourceFree
public import UniversalGroup.Embedding.PositiveHost.HStage

@[expose] public section

/-! A quotient of the positive h-stage that detects `f,k,h²` and kills `c,d`.
The input and the `ell` letter are killed before adjoining `h`. -/
namespace UniversalGroup.Embedding.PositiveHost.SourceQuotient

open HNNLemmas SimulatorSymmetry
open UniversalGroup.SymmetrySubgroups
noncomputable section

abbrev Q := SourceFree.Model
abbrev qf := SourceFree.qf
abbrev qh := SourceFree.qh
abbrev qk := SourceFree.qk
def qt : Q := qf * (qh⁻¹*qf*qh)

def lValues : Fin 7 → Q := ![1,1,1,1,1,qf,qt]
def kValues : Fin 8 → Q := ![1,1,1,1,1,qf,qt,qk]

def ofL (D : CodeWords) : (simulatorL D).Group →* Q :=
  (simulatorL D).homOfRelators lValues (by
    intro i
    fin_cases i <;>
      simp [simulatorL,simulatorLRelators,simulatorLWords,lValues,SimulatorWords.positive])

def ofK (D : CodeWords) : (simulatorK D).Group →* Q :=
  (simulatorK D).homOfRelators kValues (by
    intro i
    refine Fin.addCases (m := 13) (n := 3) (fun j => ?_) (fun j => ?_) i
    · simp only [simulatorK,Fin.append_left,Word.eval_mapGenerators]
      have he : kValues ∘ Fin.castAdd 1 = lValues := by
        funext i
        fin_cases i <;> rfl
      rw [he]
      have hh := congrArg (ofL D) ((simulatorL D).relator_eq_one j)
      simpa only [ofL,FP.homOfRelators_evalWord,map_one] using hh
    · simp only [simulatorK,Fin.append_right]
      fin_cases j
      · have hc : qt * qk = qk * qt := SourceFree.commute_relation.symm.eq
        simp [SimulatorWords.T,Word.eval_mapGenerators,kValues,simulatorLWords,
          SimulatorWords.positive]
        rw [mul_assoc (qt⁻¹*qk⁻¹), hc]
        group
      · simp [kValues]
      · simp [kValues])

@[simp] theorem ofK_generator (D : CodeWords) (i : Fin 8) :
    ofK D (generators (simulatorK D) i) = kValues i := by
  simp [ofK,generators]

@[simp] theorem ofK_inclusion (D : CodeWords) (x : (simulatorL D).Group) :
    ofK D (simulatorInclusion D x) = ofL D x := by
  have he : (ofK D).comp (simulatorInclusion D) = ofL D := by
    apply PresentedGroup.ext
    intro i
    fin_cases i <;> simp [simulatorInclusion,ofL,generators,ofK,kValues,lValues]
  exact DFunLike.congr_fun he x

@[simp] theorem ofL_generator (D : CodeWords) (i : Fin 7) :
    ofL D (generators (simulatorL D) i) = lValues i := by simp [ofL,generators]

variable (G : PreparedInput) (D : ValievDatum G) (hi : ValievIntersections G D)

/-- Killing `ell` preserves the simulator projection because both attaching
maps have the same simulator component. -/
def ellProjection : EllStage.Model G D hi →* (simulatorK D.toCodeWords).Group :=
  IdentifyingHNN.lift (A := EllStage.Domain G D hi)
    (EllStage.left G D hi) (EllStage.right G D hi)
    (EllStage.left_injective G D hi) (EllStage.right_injective G D hi)
    (EllStage.rho G D) 1 (by
      intro a
      have hl := DFunLike.congr_fun (EllStage.rho_comp_left G D hi) a
      have hr := DFunLike.congr_fun (EllStage.rho_comp_right G D hi) a
      simpa only [MonoidHom.comp_apply,inv_one,one_mul,mul_one] using hl.trans hr.symm)

@[simp] theorem ellProjection_ofM (x : InputAmalgam G D.toCodeWords) :
    ellProjection G D hi (EllStage.ofM G D hi x) = EllStage.rho G D x := by
  exact IdentifyingHNN.lift_of _ _ _ _ _ _ _ x

@[simp] theorem ellProjection_ell :
    ellProjection G D hi (EllStage.ell G D hi) = 1 := by
  exact IdentifyingHNN.lift_stable _ _ _ _ _ _ _

@[simp] theorem ellProjection_simulator (x : (simulatorK D.toCodeWords).Group) :
    ellProjection G D hi ((EllStage.simulatorEmbedding G D hi).hom x) = x := by
  change ellProjection G D hi (EllStage.ofM G D hi (EllStage.ofK G D x)) = x
  rw [ellProjection_ofM,EllStage.rho_ofK]

@[simp] theorem ellProjection_input (x : G.presentation.Group) :
    ellProjection G D hi ((EllStage.inputEmbedding G D hi).hom x) = 1 := by
  change ellProjection G D hi (EllStage.ofM G D hi _) = 1
  rw [ellProjection_ofM]
  exact CentralizingAmalgam.toBase_ofInput _ _ x

def ofEll : EllStage.Model G D hi →* Q :=
  (ofK D.toCodeWords).comp (ellProjection G D hi)

@[simp] theorem ofEll_simulator (x : (simulatorK D.toCodeWords).Group) :
    ofEll G D hi ((EllStage.simulatorEmbedding G D hi).hom x) = ofK D.toCodeWords x := by
  simp [ofEll]

@[simp] theorem ofEll_input (x : G.presentation.Group) :
    ofEll G D hi ((EllStage.inputEmbedding G D hi).hom x) = 1 := by simp [ofEll]

@[simp] theorem ofEll_ell : ofEll G D hi (EllStage.ell G D hi) = 1 := by simp [ofEll]

/-- The five displayed elements generate the actual minus attaching subgroup. -/
theorem minus_hom_ext {N : Type*} [Group N] (C : CodeWords)
    {u v : HMinus C →* N}
    (he : ∀ i, u (minusElement C i) = v (minusElement C i)) : u = v := by
  apply MonoidHom.ext
  rintro ⟨x,hx⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => obtain ⟨i,rfl⟩ := hx; exact he i
  | one => change u 1 = v 1; simp
  | mul x y hx hy ihx ihy =>
      change u (⟨x,hx⟩ * ⟨y,hy⟩) = v (⟨x,hx⟩ * ⟨y,hy⟩)
      rw [map_mul,map_mul,ihx,ihy]
  | inv x hx ih =>
      change u (⟨x,hx⟩ : HMinus C)⁻¹ = v (⟨x,hx⟩ : HMinus C)⁻¹
      rw [map_inv,map_inv,ih]

/-- The positive simulator symmetry descends to conjugation by `qh`. -/
theorem symmetry_relation (x : minusH G D) :
    qh⁻¹ * ofK D.toCodeWords x * qh =
      ofK D.toCodeWords (HStage.symmetryK G D x) := by
  let u : minusH G D →* Q :=
    (MulAut.conj qh⁻¹).toMonoidHom.comp
      ((ofK D.toCodeWords).comp (minusH G D).subtype)
  let v : minusH G D →* Q :=
    (ofK D.toCodeWords).comp
      ((plusH G D).subtype.comp (HStage.symmetryK G D).toMonoidHom)
  have he : u.comp (minusMapK D.toCodeWords).toMonoidHom =
      v.comp (minusMapK D.toCodeWords).toMonoidHom := by
    apply minus_hom_ext
    intro i
    change qh⁻¹ * ofK D.toCodeWords (minusElementK D.toCodeWords i) * qh =
      ofK D.toCodeWords (HStage.symmetryK G D (minusElementK D.toCodeWords i))
    fin_cases i <;>
      simp [HStage.symmetryK,minusValues,plusValues,SimulatorRelations.d,
        SimulatorRelations.c,SimulatorRelations.f,e0,q0,SimulatorSymmetry.x,SimulatorRelations.s,
        SimulatorRelations.e,SimulatorRelations.q,SimulatorRelations.t,lValues,qt,mul_assoc]
  obtain ⟨y,rfl⟩ := (minusMapK D.toCodeWords).surjective x
  exact DFunLike.congr_fun he y

/-- The attaching relation can be checked on simulator, input, and `ell`. -/
theorem h_relation (z : HStage.Domain G D) :
    qh⁻¹ * ofEll G D hi (HStage.left G D hi z) * qh =
      ofEll G D hi (HStage.right G D hi z) := by
  let u : HStage.Domain G D →* Q :=
    (MulAut.conj qh⁻¹).toMonoidHom.comp ((ofEll G D hi).comp (HStage.left G D hi))
  let v : HStage.Domain G D →* Q := (ofEll G D hi).comp (HStage.right G D hi)
  have he : u = v := by
    apply HNNExtension.hom_ext
    · apply AmalgamRestriction.amalgam_hom_ext
      · intro x
        change qh⁻¹ * ofEll G D hi (HStage.left G D hi (HStage.base G D x)) * qh =
          ofEll G D hi (HStage.right G D hi (HStage.base G D x))
        rw [HStage.left_base,HStage.right_base,ofEll_simulator,ofEll_simulator]
        exact symmetry_relation G D x
      · intro x
        change qh⁻¹ * ofEll G D hi (HStage.left G D hi (HStage.input G D x)) * qh =
          ofEll G D hi (HStage.right G D hi (HStage.input G D x))
        rw [HStage.left_input,HStage.right_input,ofEll_input]
        simp
    · have hs : u (HStage.ellParameter G D) = v (HStage.ellParameter G D) := by
        change qh⁻¹ * ofEll G D hi (HStage.left G D hi (HStage.ellParameter G D)) * qh =
          ofEll G D hi (HStage.right G D hi (HStage.ellParameter G D))
        rw [HStage.left_ellParameter,HStage.right_ellParameter,ofEll_ell]
        simp
      simpa only [HStage.ellParameter,centralizerStable,map_inv,inv_inj] using hs
  exact DFunLike.congr_fun he z

/-- The detecting quotient homomorphism from the positive h-stage. -/
def hom : HStage.Model G D hi →* Q :=
  IdentifyingHNN.lift (A := HStage.Domain G D)
    (HStage.left G D hi) (HStage.right G D hi)
    (HStage.left_injective G D hi) (HStage.right_injective G D hi)
    (ofEll G D hi) qh (h_relation G D hi)

@[simp] theorem hom_ofEll (x : EllStage.Model G D hi) :
    hom G D hi (HStage.ofEll G D hi x) = ofEll G D hi x := by
  exact IdentifyingHNN.lift_of _ _ _ _ _ _ _ x

@[simp] theorem hom_h : hom G D hi (HStage.stable G D hi) = qh := by
  exact IdentifyingHNN.lift_stable _ _ _ _ _ _ _

@[simp] theorem hom_simulator (x : (simulatorK D.toCodeWords).Group) :
    hom G D hi ((HStage.simulatorEmbedding G D hi).hom x) = ofK D.toCodeWords x := by
  change hom G D hi (HStage.ofEll G D hi ((EllStage.simulatorEmbedding G D hi).hom x)) = _
  rw [hom_ofEll,ofEll_simulator]


end
end UniversalGroup.Embedding.PositiveHost.SourceQuotient
