module

public import UniversalGroup.Embedding.PositiveHost.SourceQuotient
public import UniversalGroup.Embedding.PositiveHost.ModelComparison
public import UniversalGroup.Simulator.Subgroups

@[expose] public section

/-! The source subgroup `(c,d;f,k,h²)` is exactly `F₂ × F₃`.
The simulator detects the first factor, and `SourceQuotient` detects the
second while killing the first. Both survive the later proper extensions. -/
namespace UniversalGroup.Embedding.PositiveHost.Source

noncomputable section
abbrev Pair := FreeGroup (Fin 2)
abbrev Triple := FreeGroup (Fin 3)
abbrev Domain := Pair × Triple

variable (G : PreparedInput) (D : ValievDatum G) (hi : ValievIntersections G D)

abbrev sim := (HStage.simulatorEmbedding G D hi).hom

def first : Pair →* HStage.Model G D hi :=
  (sim G D hi).comp (SimulatorSubgroups.kPairD D.toCodeWords)

def second : Triple →* HStage.Model G D hi :=
  FreeGroup.lift ![sim G D hi (generators (simulatorK D.toCodeWords) 5),
    sim G D hi (generators (simulatorK D.toCodeWords) 7),HStage.stable G D hi ^ 2]

theorem first_of (i : Fin 2) : first G D hi (FreeGroup.of i) =
    ![sim G D hi (generators (simulatorK D.toCodeWords) 0),
      sim G D hi (generators (simulatorK D.toCodeWords) 1)] i := by
  fin_cases i <;> simp [first]

theorem second_of (i : Fin 3) : second G D hi (FreeGroup.of i) =
    ![sim G D hi (generators (simulatorK D.toCodeWords) 5),
      sim G D hi (generators (simulatorK D.toCodeWords) 7),HStage.stable G D hi ^ 2] i := by
  simp [second]

theorem first_injective : Function.Injective (first G D hi) :=
  (HStage.simulatorEmbedding G D hi).injective.comp
    (SimulatorSubgroups.kPairD_injective D.toCodeWords D.F_support D.E_support)

theorem quotient_first : (SourceQuotient.hom G D hi).comp (first G D hi) = 1 := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> simp [first_of,SourceQuotient.kValues,sim]

theorem quotient_second :
    (SourceQuotient.hom G D hi).comp (second G D hi) = SourceFree.freeTriple := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> simp [second_of,SourceQuotient.kValues,SourceFree.freeTriple,sim]

theorem generator_commute (i : Fin 2) (j : Fin 3) :
    Commute (first G D hi (FreeGroup.of i)) (second G D hi (FreeGroup.of j)) := by
  have hfk (i j : Fin 2) : Commute
      (first G D hi (FreeGroup.of i))
      (sim G D hi (SimulatorCentralizer.fk D.toCodeWords (FreeGroup.of j))) :=
    (SimulatorSubgroups.source_commute D.toCodeWords (FreeGroup.of i) (FreeGroup.of j)).map
      (sim G D hi)
  fin_cases j
  · simpa [second_of,SimulatorCentralizer.fk] using hfk i 0
  · simpa [second_of,SimulatorCentralizer.fk] using hfk i 1
  · fin_cases i
    · simpa [first_of,second_of] using (HStage.commutes_c G D hi).symm.pow_right 2
    · have hd := HStage.commutes_d_square G D hi
      simpa [first_of,second_of,HStage.ofL,SimulatorRelations.d,simulatorInclusion,generators] using hd

theorem commute (u : Pair) (v : Triple) :
    Commute (first G D hi u) (second G D hi v) := by
  have hgen (i : Fin 2) (w : Triple) :
      Commute (first G D hi (FreeGroup.of i)) (second G D hi w) := by
    induction w using FreeGroup.induction_on with
    | one => simp
    | of j => exact generator_commute G D hi i j
    | inv_of j hj => simpa only [map_inv] using hj.inv_right
    | mul w z hw hz => simpa only [map_mul] using hw.mul_right hz
  induction u using FreeGroup.induction_on with
  | one => simp
  | of i => exact hgen i v
  | inv_of i hu => simpa only [map_inv] using hu.inv_left
  | mul w z hw hz => simpa only [map_mul] using hw.mul_left hz

def product : Domain →* HStage.Model G D hi :=
  (first G D hi).noncommCoprod (second G D hi) (commute G D hi)

theorem product_injective : Function.Injective (product G D hi) := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨u,v⟩ huv
  have hh := congrArg (SourceQuotient.hom G D hi) huv
  change SourceQuotient.hom G D hi (first G D hi u * second G D hi v) = _ at hh
  simp only [map_mul,map_one,← MonoidHom.comp_apply,quotient_first,quotient_second,
    MonoidHom.one_apply,one_mul] at hh
  have hv : v = 1 := SourceFree.freeTriple_injective (hh.trans (map_one _).symm)
  have hu : u = 1 := by
    apply first_injective G D hi
    simpa [product,hv] using huv
  simp [hu,hv]

/-- The source product inside the complete positive host model. -/
def modelProduct : Domain →* BaseModel.Model G D hi :=
  (BaseModel.ofH G D hi).comp (product G D hi)

theorem modelProduct_injective : Function.Injective (modelProduct G D hi) :=
  (BaseModel.ofH_injective G D hi).comp (product_injective G D hi)

theorem modelProduct_first (i : Fin 2) :
    modelProduct G D hi (FreeGroup.of i,1) = ![BaseModel.c G D hi,BaseModel.d G D hi] i := by
  fin_cases i <;> simp [modelProduct,product,first_of,BaseModel.c,BaseModel.d,BaseModel.sim]

theorem modelProduct_second (i : Fin 3) :
    modelProduct G D hi (1,FreeGroup.of i) =
      ![BaseModel.f G D hi,BaseModel.k G D hi,BaseModel.h G D hi ^ 2] i := by
  fin_cases i <;>
    simp [modelProduct,product,second_of,BaseModel.f,BaseModel.k,BaseModel.h,BaseModel.sim]

/-- Homomorphisms on this product are determined by the five basis images. -/
theorem hom_ext {N : Type*} [Group N] {u v : Domain →* N}
    (hl : ∀ i : Fin 2, u (FreeGroup.of i,1) = v (FreeGroup.of i,1))
    (hr : ∀ i : Fin 3, u (1,FreeGroup.of i) = v (1,FreeGroup.of i)) : u = v := by
  have hleft : u.comp (MonoidHom.inl Pair Triple) = v.comp (MonoidHom.inl Pair Triple) := by
    apply FreeGroup.ext_hom
    exact hl
  have hright : u.comp (MonoidHom.inr Pair Triple) = v.comp (MonoidHom.inr Pair Triple) := by
    apply FreeGroup.ext_hom
    exact hr
  apply MonoidHom.ext
  rintro ⟨a,b⟩
  have he : (a,b) = (a,1) * (1,b) := by simp
  rw [he,map_mul,map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun hleft a) (DFunLike.congr_fun hright b)

/-- A marked map to the complete model is injective when its five images
are the source coordinates. This is the interface used by the literal host. -/
theorem injective_of_coordinates (s : Domain →* BaseModel.Model G D hi)
    (hl : ∀ i : Fin 2, s (FreeGroup.of i,1) = ![BaseModel.c G D hi,BaseModel.d G D hi] i)
    (hr : ∀ i : Fin 3, s (1,FreeGroup.of i) =
      ![BaseModel.f G D hi,BaseModel.k G D hi,BaseModel.h G D hi ^ 2] i) :
    Function.Injective s := by
  have he : s = modelProduct G D hi := hom_ext
    (fun i => (hl i).trans (modelProduct_first G D hi i).symm)
    (fun i => (hr i).trans (modelProduct_second G D hi i).symm)
  rw [he]
  exact modelProduct_injective G D hi

end
end UniversalGroup.Embedding.PositiveHost.Source
