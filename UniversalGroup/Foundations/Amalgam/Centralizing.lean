module

public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.NoncommCoprod

@[expose] public section

/-!
# Centralizing amalgams

The amalgam `K *_[V] (V × G)` embeds both factors and retracts onto `K`.
Its universal property adjoins exactly the commutations between `V` and the
input group `G`.
-/

namespace UniversalGroup
namespace CentralizingAmalgam

universe u

inductive Side
  | base
  | product

variable {K : Type u} [Group K] (V : Subgroup K) (G : Type u) [Group G]

def Factor : Side → Type u
  | .base => K
  | .product => V × G

instance factorGroup (s : Side) : Group (Factor V G s) := by
  cases s <;> dsimp [Factor] <;> infer_instance

def diagram : (s : Side) → V →* Factor V G s
  | .base => V.subtype
  | .product => MonoidHom.inl V G

theorem diagram_injective (s : Side) : Function.Injective (diagram V G s) := by
  cases s
  · exact Subtype.val_injective
  · intro x y h
    exact congrArg Prod.fst h

abbrev Model := Monoid.PushoutI (diagram V G)

def ofBase : K →* Model V G :=
  Monoid.PushoutI.of (φ := diagram V G) Side.base

def ofProduct : V × G →* Model V G :=
  Monoid.PushoutI.of (φ := diagram V G) Side.product

def ofInput : G →* Model V G := (ofProduct V G).comp (MonoidHom.inr V G)

theorem ofBase_injective : Function.Injective (ofBase V G) :=
  Monoid.PushoutI.of_injective (diagram_injective V G) Side.base

theorem ofProduct_injective : Function.Injective (ofProduct V G) :=
  Monoid.PushoutI.of_injective (diagram_injective V G) Side.product

theorem ofInput_injective : Function.Injective (ofInput V G) := by
  intro x y h
  exact congrArg Prod.snd (ofProduct_injective V G h)

theorem identifies (x : V) : ofBase V G x = ofProduct V G (x, 1) := by
  exact (Monoid.PushoutI.of_apply_eq_base (diagram V G) Side.base x).trans
    (Monoid.PushoutI.of_apply_eq_base (diagram V G) Side.product x).symm

theorem commute (x : V) (g : G) : Commute (ofBase V G x) (ofInput V G g) := by
  rw [identifies]
  exact (show Commute (x, (1 : G)) ((1 : V), g) by
    simp [commute_iff_eq]).map (ofProduct V G)

def baseProjectionFactors : (s : Side) → Factor V G s →* K
  | .base => MonoidHom.id K
  | .product => V.subtype.comp (MonoidHom.fst V G)

/-- The retraction retaining `K` and killing the input. -/
def toBase : Model V G →* K :=
  Monoid.PushoutI.lift (baseProjectionFactors V G) V.subtype (by
    intro s
    cases s <;> ext x <;> rfl)

@[simp] theorem toBase_ofBase (x : K) : toBase V G (ofBase V G x) = x := by
  exact Monoid.PushoutI.lift_of (φ := diagram V G) _ _ _ (i := Side.base) x

@[simp] theorem toBase_ofProduct (x : V × G) :
    toBase V G (ofProduct V G x) = x.1 := by
  exact Monoid.PushoutI.lift_of (φ := diagram V G) _ _ _ (i := Side.product) x

@[simp] theorem toBase_ofInput (x : G) : toBase V G (ofInput V G x) = 1 := by
  simp [ofInput]

variable {L : Type*} [Group L]

def liftFactors (f : K →* L) (g : G →* L)
    (h : ∀ x : V, ∀ y, Commute (f x) (g y)) : (s : Side) → Factor V G s →* L
  | .base => f
  | .product => (f.comp V.subtype).noncommCoprod g h

/-- The universal property: maps out of `K` and `G` extend precisely when
the image of `G` commutes with the image of `V`. -/
def lift (f : K →* L) (g : G →* L)
    (h : ∀ x : V, ∀ y, Commute (f x) (g y)) : Model V G →* L :=
  Monoid.PushoutI.lift (liftFactors V G f g h) (f.comp V.subtype) (by
    intro s
    cases s
    · rfl
    · exact MonoidHom.noncommCoprod_comp_inl _ _ h)

@[simp] theorem lift_ofBase (f : K →* L) (g : G →* L)
    (h : ∀ x : V, ∀ y, Commute (f x) (g y)) (x : K) :
    lift V G f g h (ofBase V G x) = f x := by
  exact Monoid.PushoutI.lift_of (φ := diagram V G) _ _ _ (i := Side.base) x

@[simp] theorem lift_ofProduct (f : K →* L) (g : G →* L)
    (h : ∀ x : V, ∀ y, Commute (f x) (g y)) (x : V × G) :
    lift V G f g h (ofProduct V G x) = f x.1 * g x.2 := by
  exact Monoid.PushoutI.lift_of (φ := diagram V G) _ _ _ (i := Side.product) x

@[simp] theorem lift_ofInput (f : K →* L) (g : G →* L)
    (h : ∀ x : V, ∀ y, Commute (f x) (g y)) (x : G) :
    lift V G f g h (ofInput V G x) = g x := by
  simp [ofInput]

end CentralizingAmalgam
end UniversalGroup
