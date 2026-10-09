module

public import UniversalGroup.Host.InputFreeSubgroup

@[expose] public section

/-! The free triples needed for the final `b` compression. -/

namespace UniversalGroup.InputTriples
noncomputable section

abbrev Z := Multiplicative ℤ

inductive Side
  | c | input | ell
  deriving DecidableEq

def Factor (H : Type) : Side → Type _
  | .c => Z
  | .input => H
  | .ell => Z

instance {H : Type} [Group H] (i : Side) : Group (Factor H i) := by
  cases i <;> dsimp [Factor] <;> infer_instance

variable {H : Type} [Group H]

def toNestedFactors : (i : Side) → Factor H i →* Monoid.Coprod (Monoid.Coprod Z H) Z
  | .c => Monoid.Coprod.inl.comp Monoid.Coprod.inl
  | .input => Monoid.Coprod.inl.comp Monoid.Coprod.inr
  | .ell => Monoid.Coprod.inr

def toNested : Monoid.CoprodI (Factor H) →* Monoid.Coprod (Monoid.Coprod Z H) Z :=
  Monoid.CoprodI.lift (M := Factor H) (N := Monoid.Coprod (Monoid.Coprod Z H) Z)
    (toNestedFactors (H := H))

def fromNested : Monoid.Coprod (Monoid.Coprod Z H) Z →* Monoid.CoprodI (Factor H) :=
  Monoid.Coprod.lift
    (Monoid.Coprod.lift (Monoid.CoprodI.of (M := Factor H) (i := Side.c))
      (Monoid.CoprodI.of (M := Factor H) (i := Side.input)))
    (Monoid.CoprodI.of (M := Factor H) (i := Side.ell))

theorem fromNested_comp_toNested : (fromNested (H := H)).comp toNested = MonoidHom.id _ := by
  apply Monoid.CoprodI.ext_hom
  intro i
  apply MonoidHom.ext
  intro x
  cases i <;> rfl

theorem toNested_injective : Function.Injective (toNested (H := H)) :=
  Function.LeftInverse.injective (fun x => DFunLike.congr_fun fromNested_comp_toNested x)

def cyclicMaps (g : H) : (i : Side) → Z →* Factor H i
  | .c => MonoidHom.id _
  | .input => zpowersHom H g
  | .ell => MonoidHom.id _

theorem cyclicMaps_injective (g : H) (hg : ∀ z : ℤ, g ^ z = 1 → z = 0) (i : Side) :
    Function.Injective (cyclicMaps g i) := by
  cases i
  · exact Function.injective_id
  · apply (injective_iff_map_eq_one (zpowersHom H g)).mpr
    intro z hz
    exact congrArg Multiplicative.ofAdd (hg _ hz)
  · exact Function.injective_id

def index : Fin 3 → Side := ![.c, .input, .ell]

theorem index_injective : Function.Injective index := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [index]

def param (g : H) : FreeGroup (Fin 3) →* Monoid.Coprod (Monoid.Coprod Z H) Z :=
  toNested.comp ((Monoid.CoprodI.familyMap (cyclicMaps g)).comp
    ((Monoid.CoprodI.intOfFree Side).comp (FreeGroup.map index)))

theorem param_injective (g : H) (hg : ∀ z : ℤ, g ^ z = 1 → z = 0) :
    Function.Injective (param g) := by
  classical
  exact toNested_injective.comp
    ((Monoid.CoprodI.familyMap_injective _ (cyclicMaps_injective g hg)).comp
      ((Monoid.CoprodI.intOfFree_injective Side).comp (FreeGroup.map_injective index_injective)))

@[simp] theorem param_zero (g : H) : param g (FreeGroup.of 0) =
    Monoid.Coprod.inl (Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ℤ))) := by
  simp [param, index, Monoid.CoprodI.intOfFree, Monoid.CoprodI.familyMap,
    cyclicMaps, toNested]
  rfl

@[simp] theorem param_one (g : H) : param g (FreeGroup.of 1) =
    Monoid.Coprod.inl (Monoid.Coprod.inr g) := by
  simp [param, index, Monoid.CoprodI.intOfFree, Monoid.CoprodI.familyMap,
    cyclicMaps, toNested]
  change Monoid.Coprod.inl (Monoid.Coprod.inr (g ^ (1 : ℤ))) = _
  rw [zpow_one]

@[simp] theorem param_two (g : H) : param g (FreeGroup.of 2) =
    Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ)) := by
  simp [param, index, Monoid.CoprodI.intOfFree, Monoid.CoprodI.familyMap,
    cyclicMaps, toNested]
  rfl

variable (G : PreparedInput)

/-- Canonical free triple `(c,uᵢ,ell)` in the already identified group `U`. -/
def triple (i : Fin 2) : FreeGroup (Fin 3) →* InputFreeSubgroup.Domain G :=
  param (generators G.presentation i)

theorem triple_injective (i : Fin 2) : Function.Injective (triple G i) :=
  param_injective _ (G.infiniteOrder i)

def c : InputFreeSubgroup.Domain G :=
  Monoid.Coprod.inl (Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ℤ)))
def input (i : Fin 2) : InputFreeSubgroup.Domain G :=
  Monoid.Coprod.inl (Monoid.Coprod.inr (generators G.presentation i))
def ell : InputFreeSubgroup.Domain G := Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))

@[simp] theorem triple_of (i : Fin 2) (j : Fin 3) :
    triple G i (FreeGroup.of j) = ![c G, input G i, ell G] j := by
  fin_cases j <;> simp [triple, c, input, ell]

def left : FreeGroup (Fin 3) →* InputFreeSubgroup.Domain G :=
  (triple G 0).comp (FreeGroup.map ![1, 2, 0])

def right : FreeGroup (Fin 3) →* InputFreeSubgroup.Domain G :=
  (triple G 1).comp (FreeGroup.map ![2, 0, 1])

theorem left_injective : Function.Injective (left G) := by
  apply (triple_injective G 0).comp
  apply FreeGroup.map_injective
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

theorem right_injective : Function.Injective (right G) := by
  apply (triple_injective G 1).comp
  apply FreeGroup.map_injective
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem left_of (j : Fin 3) :
    left G (FreeGroup.of j) = ![input G 0, ell G, c G] j := by
  fin_cases j <;> simp [left]

@[simp] theorem right_of (j : Fin 3) :
    right G (FreeGroup.of j) = ![ell G, c G, input G 1] j := by
  fin_cases j <;> simp [right]

end
end UniversalGroup.InputTriples
