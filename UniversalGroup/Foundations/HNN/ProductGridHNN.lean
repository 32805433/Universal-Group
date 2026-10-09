module

public import UniversalGroup.Foundations.HNN.Identifying
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Eliminating one grid letter in a product HNN extension

Adjoining `h` to `U × F(x₀,x₁,x₂,x₃)` with `h` centralizing `U` and
`h⁻¹ x₁ h = x₂⁻¹` preserves a free product grid `U × F(x₀,x₁,h,x₃)`.
-/

namespace UniversalGroup.ProductGridHNN

noncomputable section

abbrev F := FreeGroup (Fin 4)
abbrev Z := FreeGroup (Fin 1)

def positive (i : Fin 4) : Z →* F := FreeGroup.lift (fun _ => FreeGroup.of i)
def negative (i : Fin 4) : Z →* F := FreeGroup.lift (fun _ => (FreeGroup.of i)⁻¹)

theorem positive_injective (i : Fin 4) : Function.Injective (positive i) := by
  let r : F →* Z := FreeGroup.lift (fun _ => FreeGroup.of 0)
  have h : r.comp (positive i) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro j
    fin_cases j
    simp [r, positive]
  exact Function.LeftInverse.injective (fun w => DFunLike.congr_fun h w)

theorem negative_injective (i : Fin 4) : Function.Injective (negative i) := by
  let r : F →* Z := FreeGroup.lift (fun _ => (FreeGroup.of 0)⁻¹)
  have h : r.comp (negative i) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro j
    fin_cases j
    simp [r, negative]
  exact Function.LeftInverse.injective (fun w => DFunLike.congr_fun h w)

variable (U : Type*) [Group U]

def left : U × Z →* U × F := (MonoidHom.id U).prodMap (positive 1)
def right : U × Z →* U × F := (MonoidHom.id U).prodMap (negative 2)

theorem left_injective : Function.Injective (left U) := by
  rintro ⟨u, w⟩ ⟨v, z⟩ h
  change (u, positive 1 w) = (v, positive 1 z) at h
  exact Prod.ext (congrArg (fun p : U × F => p.1) h) (positive_injective 1 (congrArg (fun p : U × F => p.2) h))

theorem right_injective : Function.Injective (right U) := by
  rintro ⟨u, w⟩ ⟨v, z⟩ h
  change (u, negative 2 w) = (v, negative 2 z) at h
  exact Prod.ext (congrArg (fun p : U × F => p.1) h) (negative_injective 2 (congrArg (fun p : U × F => p.2) h))

abbrev Model := IdentifyingHNN (left U) (right U) (left_injective U) (right_injective U)
abbrev of : U × F →* Model U := IdentifyingHNN.of _ _ _ _
abbrev stable : Model U := IdentifyingHNN.stable _ _ _ _

/-- Replace `x₂` by `h⁻¹ x₁⁻¹ h`. -/
def eliminate : F →* F := FreeGroup.lift
  ![FreeGroup.of 0, FreeGroup.of 1,
    (FreeGroup.of 2)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 2, FreeGroup.of 3]

private theorem eliminate_conjugacy (w : Z) :
    (FreeGroup.of 2)⁻¹ * eliminate (positive 1 w) * FreeGroup.of 2 =
      eliminate (negative 2 w) := by
  have h : (MulAut.conj (FreeGroup.of 2)⁻¹).toMonoidHom.comp (eliminate.comp (positive 1)) =
      eliminate.comp (negative 2) := by
    apply FreeGroup.ext_hom
    intro j
    fin_cases j
    simp [positive, negative, eliminate, mul_assoc]
  exact DFunLike.congr_fun h w

def forwardBase : U × F →* U × F := (MonoidHom.id U).prodMap eliminate

theorem forward_relation (a : U × Z) :
    ((1, FreeGroup.of 2) : U × F)⁻¹ * forwardBase U (left U a) * (1, FreeGroup.of 2) =
      forwardBase U (right U a) := by
  apply Prod.ext
  · simp [forwardBase, left, right]
  · exact eliminate_conjugacy a.2

/-- A retraction obtained by eliminating `x₂`. -/
def forward : Model U →* U × F :=
  IdentifyingHNN.lift _ _ _ _ (forwardBase U) (1, FreeGroup.of 2) (forward_relation U)

@[simp] theorem forward_of (a : U × F) : forward U (of U a) = forwardBase U a :=
  IdentifyingHNN.lift_of _ _ _ _ _ _ _ a
@[simp] theorem forward_stable : forward U (stable U) = (1, FreeGroup.of 2) :=
  IdentifyingHNN.lift_stable _ _ _ _ _ _ _

def input : U →* Model U := (of U).comp (MonoidHom.inl U F)
def old : F →* Model U := (of U).comp (MonoidHom.inr U F)
def letters : F →* Model U := FreeGroup.lift
  ![old U (FreeGroup.of 0), old U (FreeGroup.of 1), stable U, old U (FreeGroup.of 3)]

@[simp] theorem letters_x0 : letters U (FreeGroup.of 0) = old U (FreeGroup.of 0) := by simp [letters]
@[simp] theorem letters_x1 : letters U (FreeGroup.of 1) = old U (FreeGroup.of 1) := by simp [letters]
@[simp] theorem letters_h : letters U (FreeGroup.of 2) = stable U := by simp [letters]
@[simp] theorem letters_x3 : letters U (FreeGroup.of 3) = old U (FreeGroup.of 3) := by simp [letters]

private theorem input_commute_old (u : U) (w : F) : Commute (input U u) (old U w) := by
  change Commute (of U (u, 1)) (of U (1, w))
  have h : Commute ((u, 1) : U × F) (1, w) := by simp [Commute, SemiconjBy]
  exact h.map (of U)

private theorem input_commute_stable (u : U) : Commute (input U u) (stable U) := by
  have h := IdentifyingHNN.conjugates (left U) (right U) (left_injective U) (right_injective U) (u, 1)
  have hl : left U (u, 1) = (u, 1) := by simp [left]
  have hr : right U (u, 1) = (u, 1) := by simp [right]
  rw [hl, hr] at h
  have h' : (stable U)⁻¹ * input U u * stable U = input U u := h
  have hh := congrArg (fun z => stable U * z) h'
  change input U u * stable U = stable U * input U u
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh

theorem input_commute_letters (u : U) (w : F) : Commute (input U u) (letters U w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i =>
    fin_cases i
    · simpa using input_commute_old U u (FreeGroup.of 0)
    · simpa using input_commute_old U u (FreeGroup.of 1)
    · simpa using input_commute_stable U u
    · simpa using input_commute_old U u (FreeGroup.of 3)
  | inv_of w hw => simpa only [map_inv] using hw.inv_right
  | mul w z hw hz => simpa only [map_mul] using hw.mul_right hz

/-- The new product grid, with basis order `x₀,x₁,h,x₃`. -/
def product : U × F →* Model U := (input U).noncommCoprod (letters U) (input_commute_letters U)

@[simp] theorem product_left (u : U) : product U (u, 1) = input U u := by simp [product]
@[simp] theorem product_right (w : F) : product U (1, w) = letters U w := by simp [product]

@[simp] theorem forward_input (u : U) : forward U (input U u) = (u, 1) := by
  simp [input, forwardBase]

private theorem forward_comp_letters : (forward U).comp (letters U) = MonoidHom.inr U F := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> simp [old, forwardBase, eliminate]

theorem forward_product (a : U × F) : forward U (product U a) = a := by
  rcases a with ⟨u, w⟩
  change forward U (input U u * letters U w) = _
  rw [map_mul, forward_input, show forward U (letters U w) = (1, w) from
    DFunLike.congr_fun (forward_comp_letters U) w]
  simp

/-- The product grid is faithful. -/
theorem product_injective : Function.Injective (product U) :=
  Function.LeftInverse.injective (forward_product U)

@[simp] theorem positive_range (i : Fin 4) : (positive i).range =
    Subgroup.closure ({FreeGroup.of i} : Set F) := by
  rw [positive, FreeGroup.range_lift_eq_closure]
  simp

@[simp] theorem negative_range (i : Fin 4) : (negative i).range =
    Subgroup.closure ({FreeGroup.of i} : Set F) := by
  rw [negative, FreeGroup.range_lift_eq_closure]
  simp [Subgroup.closure_singleton_inv]

theorem mem_left_range (a : U × F) : a ∈ (left U).range ↔
    a.2 ∈ Subgroup.closure ({FreeGroup.of 1} : Set F) := by
  rw [← positive_range]
  constructor
  · rintro ⟨⟨u, w⟩, hw⟩
    exact ⟨w, congrArg (fun z : U × F => z.2) hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨(a.1, w), Prod.ext rfl hw⟩

theorem mem_right_range (a : U × F) : a ∈ (right U).range ↔
    a.2 ∈ Subgroup.closure ({FreeGroup.of 2} : Set F) := by
  rw [← negative_range]
  constructor
  · rintro ⟨⟨u, w⟩, hw⟩
    exact ⟨w, congrArg (fun z : U × F => z.2) hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨(a.1, w), Prod.ext rfl hw⟩

end
end UniversalGroup.ProductGridHNN
