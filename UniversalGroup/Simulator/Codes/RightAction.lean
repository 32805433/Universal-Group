module

public import UniversalGroup.Simulator.Codes.LeftIntersection

@[expose] public section

/-!
# A rotated decoder for the second single-letter intersection

There are three coding states and one ordinary state. The marker's endpoint
chooses the rotation of the coding labels. After conjugating the subgroup
basis, its first two generators act by a simultaneous conjugate of two free
basis letters; its other three generators act by independent translations.
That simultaneous conjugation is an automorphism of the code free factor.

The ambient letters `s₂,q` preserve all states with coordinates in the cyclic
subgroup on the fourth target letter. This forces the exact intersection
proved in `new_intersection`, without a hypothesis on the marker word.
-/

namespace UniversalGroup.CodeSubgroups.RightAction

noncomputable section

abbrev State (H : Type*) := Option (Fin 3) × H

variable {H : Type*} [Group H]

def step : Equiv.Perm (Fin 3) where
  toFun i := ![1, 2, 0] i
  invFun i := ![2, 0, 1] i
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def fiber (v : Option (Fin 3) → H) : Equiv.Perm (State H) where
  toFun p := (p.1, v p.1 * p.2)
  invFun p := (p.1, (v p.1)⁻¹ * p.2)
  left_inv := by intro ⟨i, w⟩; simp
  right_inv := by intro ⟨i, w⟩; simp

@[simp] theorem fiber_apply (v : Option (Fin 3) → H) (i : Option (Fin 3)) (w : H) :
    fiber v (i, w) = (i, v i * w) := rfl

@[simp] theorem fiber_pow_apply (v : Option (Fin 3) → H) (n : ℕ)
    (i : Option (Fin 3)) (w : H) :
    (fiber v ^ n) (i, w) = (i, v i ^ n * w) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih => simp [pow_succ, Equiv.Perm.mul_apply, ih, mul_assoc]

def turn (z : H) : Equiv.Perm (State H) where
  toFun p := match p.1 with
    | none => (none, z * p.2)
    | some i => (some (step i), p.2)
  invFun p := match p.1 with
    | none => (none, z⁻¹ * p.2)
    | some i => (some (step⁻¹ i), p.2)
  left_inv := by intro ⟨i, w⟩; cases i <;> simp
  right_inv := by intro ⟨i, w⟩; cases i <;> simp

@[simp] theorem turn_none (z w : H) : turn z (none, w) = (none, z * w) := rfl
@[simp] theorem turn_some (z w : H) (i : Fin 3) :
    turn z (some i, w) = (some (step i), w) := rfl

def label (k : Fin 3) (x y : H) (i : Fin 3) : H :=
  if i = k then 1 else if i = step k then x⁻¹ * y else x * ((x⁻¹ * y) ^ 2)⁻¹

def letterA (k : Fin 3) (x y z : H) : Equiv.Perm (State H) :=
  fiber (fun i => match i with | none => z | some j => label k x y j)

def letterB (z : H) : Equiv.Perm (State H) := turn z

theorem code_action (k : Fin 3) (x y z t : H) (r : ℕ) (i : Fin 2) (w : H) :
    evalPositive (letterA k x y z) (letterB t) (valievCode r i) (some k, w) =
      (some k, ![x, y] i * w) := by
  fin_cases k <;> fin_cases i <;>
    simp [valievCode, evalPositive, letterA, letterB, label, step,
      Equiv.Perm.mul_apply, mul_assoc, pow_succ]

def swapOrdinary : Equiv.Perm (State H) where
  toFun p := match p.1 with
    | none => (some 0, p.2)
    | some i => if i = 0 then (none, p.2) else p
  invFun p := match p.1 with
    | none => (some 0, p.2)
    | some i => if i = 0 then (none, p.2) else p
  left_inv := by intro ⟨i, w⟩; cases i with | none => rfl | some i => fin_cases i <;> rfl
  right_inv := by intro ⟨i, w⟩; cases i with | none => rfl | some i => fin_cases i <;> rfl

omit [Group H] in
@[simp] theorem swap_none (w : H) : swapOrdinary (none, w) = (some 0, w) := rfl
omit [Group H] in
@[simp] theorem swap_zero (w : H) : swapOrdinary (some 0, w) = (none, w) := rfl
omit [Group H] in
@[simp] theorem swap_inv_none (w : H) : swapOrdinary⁻¹ (none, w) = (some 0, w) := rfl
omit [Group H] in
@[simp] theorem swap_inv_zero (w : H) : swapOrdinary⁻¹ (some 0, w) = (none, w) := rfl

def phase : PositiveWord → Fin 3 → Fin 3
  | [], i => i
  | j :: w, i => if j = 0 then phase w i else step (phase w i)

def Tracks (p : Equiv.Perm (State H)) (i j : Option (Fin 3)) (x : H) : Prop :=
  ∀ w, p (i, w) = (j, x * w)

theorem Tracks.inv {p : Equiv.Perm (State H)} {i j : Option (Fin 3)} {x : H}
    (hp : Tracks p i j x) : Tracks p⁻¹ j i x⁻¹ := by
  intro w
  apply p.injective
  rw [hp (x⁻¹ * w)]
  simp

/-- The free factor used for the two coded generator labels. -/
def codeFactor : Subgroup (FreeGroup (Fin 5)) :=
  Subgroup.closure ({FreeGroup.of 0, FreeGroup.of 1} : Set (FreeGroup (Fin 5)))

private theorem label_mem (k i : Fin 3) :
    label k (FreeGroup.of (0 : Fin 5)) (FreeGroup.of 1) i ∈ codeFactor := by
  have hx : (FreeGroup.of 0 : FreeGroup (Fin 5)) ∈ codeFactor :=
    Subgroup.subset_closure (by simp)
  have hy : (FreeGroup.of 1 : FreeGroup (Fin 5)) ∈ codeFactor :=
    Subgroup.subset_closure (by simp)
  unfold label
  split
  · exact codeFactor.one_mem
  · split
    · exact codeFactor.mul_mem (codeFactor.inv_mem hx) hy
    · exact codeFactor.mul_mem hx
        (codeFactor.inv_mem (codeFactor.pow_mem (codeFactor.mul_mem (codeFactor.inv_mem hx) hy) 2))

def A (k : Fin 3) : Equiv.Perm (State (FreeGroup (Fin 5))) :=
  letterA k (FreeGroup.of 0) (FreeGroup.of 1) (FreeGroup.of 2)
def B : Equiv.Perm (State (FreeGroup (Fin 5))) := letterB (FreeGroup.of 3)

theorem AB_code_action (k : Fin 3) (r : ℕ) (i : Fin 2) (w : FreeGroup (Fin 5)) :
    evalPositive (A k) B (valievCode r i) (some k, w) =
      (some k, ![FreeGroup.of 0, FreeGroup.of 1] i * w) :=
  code_action k (FreeGroup.of 0) (FreeGroup.of 1) (FreeGroup.of 2) (FreeGroup.of 3) r i w

theorem positive_tracks (k : Fin 3) (w : PositiveWord) (i : Fin 3) :
    ∃ p ∈ codeFactor, Tracks (evalPositive (A k) B w) (some i) (some (phase w i)) p := by
  induction w with
  | nil => exact ⟨1, codeFactor.one_mem, by intro z; simp [evalPositive, phase]⟩
  | cons j w ih =>
      obtain ⟨p, hp, ht⟩ := ih
      fin_cases j
      · refine ⟨label k (FreeGroup.of 0) (FreeGroup.of 1) (phase w i) * p,
          codeFactor.mul_mem (label_mem k (phase w i)) hp, ?_⟩
        intro z
        simp only [evalPositive, List.map_cons, List.prod_cons] at ht ⊢
        rw [Equiv.Perm.mul_apply, ht z]
        simp [A, letterA, phase, mul_assoc]
      · refine ⟨p, hp, ?_⟩
        intro z
        simp only [evalPositive, List.map_cons, List.prod_cons] at ht ⊢
        rw [Equiv.Perm.mul_apply, ht z]
        simp [B, letterB, phase]

def targetValues (p : FreeGroup (Fin 5)) : Fin 5 → FreeGroup (Fin 5) :=
  ![p⁻¹ * FreeGroup.of 0 * p, p⁻¹ * FreeGroup.of 1 * p,
    FreeGroup.of 2, FreeGroup.of 3, FreeGroup.of 4]

def partialConj (p : FreeGroup (Fin 5)) : FreeGroup (Fin 5) →* FreeGroup (Fin 5) :=
  FreeGroup.lift (targetValues p)

@[simp] theorem partialConj_of (p : FreeGroup (Fin 5)) (i : Fin 5) :
    partialConj p (FreeGroup.of i) = targetValues p i := by simp [partialConj]

theorem partialConj_on_code (p : FreeGroup (Fin 5)) {w : FreeGroup (Fin 5)}
    (hw : w ∈ codeFactor) : partialConj p w = p⁻¹ * w * p := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
      rcases hw with rfl | hw
      · simp [targetValues]
      · rcases hw with rfl
        simp [targetValues]
  | one => simp
  | mul w z _ _ hw hz => simp [hw, hz, mul_assoc]
  | inv w _ hw => simp [hw, mul_assoc]

theorem partialConj_injective (p : FreeGroup (Fin 5)) (hp : p ∈ codeFactor) :
    Function.Injective (partialConj p) := by
  have hfix : partialConj p⁻¹ p = p := by
    simpa using partialConj_on_code p⁻¹ hp
  have hcomp : (partialConj p⁻¹).comp (partialConj p) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [targetValues, hfix, mul_assoc]
  intro u v huv
  have h := congrArg (partialConj p⁻¹) huv
  simpa only [← MonoidHom.comp_apply, hcomp, MonoidHom.id_apply] using h

def secondCoordinates : Subgroup (FreeGroup (Fin 5)) :=
  Subgroup.closure ({FreeGroup.of 3} : Set (FreeGroup (Fin 5)))

theorem partialConj_mem_second (p : FreeGroup (Fin 5)) (hp : p ∈ codeFactor)
    {w : FreeGroup (Fin 5)} (hw : partialConj p w ∈ secondCoordinates) :
    w ∈ secondCoordinates := by
  obtain ⟨n, hn⟩ := Subgroup.mem_closure_singleton.mp hw
  have hw' : w = (FreeGroup.of 3) ^ n := by
    apply partialConj_injective p hp
    simpa [targetValues] using hn.symm
  rw [hw']
  exact secondCoordinates.zpow_mem (Subgroup.subset_closure (Set.mem_singleton _)) n

def P (D : CodeWords) : Equiv.Perm (State (FreeGroup (Fin 5))) :=
  evalPositive (A (phase D.P 0)) B D.P

def U : Equiv.Perm (State (FreeGroup (Fin 5))) :=
  fiber (fun i => match i with | none => FreeGroup.of 4 | some _ => 1)

def repValues (D : CodeWords) : Fin 4 → Equiv.Perm (State (FreeGroup (Fin 5))) :=
  ![A (phase D.P 0), B, U * (P D * swapOrdinary)⁻¹, swapOrdinary]

def rep (D : CodeWords) : FreeGroup (Fin 4) →* Equiv.Perm (State (FreeGroup (Fin 5))) :=
  FreeGroup.lift (repValues D)

@[simp] theorem rep_s1 (D : CodeWords) : rep D (FreeGroup.of 0) = A (phase D.P 0) := by
  simp [rep, repValues]
@[simp] theorem rep_s2 (D : CodeWords) : rep D (FreeGroup.of 1) = B := by
  simp [rep, repValues]
@[simp] theorem rep_f (D : CodeWords) :
    rep D (FreeGroup.of 2) = U * (P D * swapOrdinary)⁻¹ := by
  simp [rep, repValues]
@[simp] theorem rep_q (D : CodeWords) : rep D (FreeGroup.of 3) = swapOrdinary := by
  simp [rep, repValues]

theorem rep_positive (D : CodeWords) (w : PositiveWord) :
    rep D (positiveFour w) = evalPositive (A (phase D.P 0)) B w := by
  rw [positiveFour, map_positive, rep_s1, rep_s2]

/-- A convenient basis after conjugating the original subgroup by `f`. -/
def newValues (D : CodeWords) : Fin 5 → FreeGroup (Fin 4) :=
  ![(FreeGroup.of 3)⁻¹ * (positiveFour D.P)⁻¹ * positiveFour (D.code 0) *
      positiveFour D.P * FreeGroup.of 3,
    (FreeGroup.of 3)⁻¹ * (positiveFour D.P)⁻¹ * positiveFour (D.code 1) *
      positiveFour D.P * FreeGroup.of 3,
    FreeGroup.of 0, FreeGroup.of 1, FreeGroup.of 2 * positiveFour D.P * FreeGroup.of 3]

def newLift (D : CodeWords) : FreeGroup (Fin 5) →* FreeGroup (Fin 4) :=
  FreeGroup.lift (newValues D)

theorem generator_actions (D : CodeWords) (r : ℕ) (hcode : D.code = valievCode r)
    (p : FreeGroup (Fin 5)) (ht : Tracks (P D) (some 0) (some (phase D.P 0)) p)
    (i : Fin 5) :
    Tracks (rep D (newValues D i)) none none (targetValues p i) := by
  intro w
  fin_cases i
  · simp only [newValues, Matrix.cons_val_zero', map_mul, map_inv, rep_q, rep_positive,
      Equiv.Perm.mul_apply, swap_none]
    change swapOrdinary⁻¹ ((P D)⁻¹
      (evalPositive (A (phase D.P 0)) B (D.code 0) ((P D) (some 0, w)))) = _
    rw [ht w, hcode, AB_code_action, ht.inv, swap_inv_zero]
    simp [targetValues, mul_assoc]
  · simp only [newValues, Matrix.cons_val_zero', Matrix.cons_val_succ', map_mul, map_inv,
      rep_q, rep_positive, Equiv.Perm.mul_apply, swap_none]
    change swapOrdinary⁻¹ ((P D)⁻¹
      (evalPositive (A (phase D.P 0)) B (D.code 1) ((P D) (some 0, w)))) = _
    rw [ht w, hcode, AB_code_action, ht.inv, swap_inv_zero]
    simp [targetValues, mul_assoc]
  · simp [newValues, targetValues, A, letterA]
  · simp [newValues, targetValues, B, letterB]
  · simp [newValues, targetValues, rep_positive, P, mul_assoc, U]

theorem Tracks.mul {p q : Equiv.Perm (State H)} {i : Option (Fin 3)} {x y : H}
    (hp : Tracks p i i x) (hq : Tracks q i i y) : Tracks (p * q) i i (x * y) := by
  intro w
  rw [Equiv.Perm.mul_apply, hq w, hp (y * w), mul_assoc]

theorem word_actions (D : CodeWords) (r : ℕ) (hcode : D.code = valievCode r)
    (p : FreeGroup (Fin 5)) (ht : Tracks (P D) (some 0) (some (phase D.P 0)) p)
    (w : FreeGroup (Fin 5)) :
    Tracks (rep D (newLift D w)) none none (partialConj p w) := by
  induction w using FreeGroup.induction_on with
  | one => intro z; simp
  | of i => simpa [newLift] using generator_actions D r hcode p ht i
  | inv_of i hi => simpa only [map_inv] using hi.inv
  | mul w z hw hz => simpa only [map_mul] using hw.mul hz

def ambient : Subgroup (FreeGroup (Fin 4)) :=
  Subgroup.closure ({FreeGroup.of 1, FreeGroup.of 3} : Set (FreeGroup (Fin 4)))

def allowed : Set (State (FreeGroup (Fin 5))) := {p | p.2 ∈ secondCoordinates}

private theorem second_generator_mem :
    (FreeGroup.of 3 : FreeGroup (Fin 5)) ∈ secondCoordinates :=
  Subgroup.subset_closure (Set.mem_singleton _)

theorem ambient_le_preserver (D : CodeWords) :
    ambient ≤ (preserves allowed).comap (rep D) := by
  rw [ambient, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · change ∀ p, p ∈ allowed ↔ rep D (FreeGroup.of 1) p ∈ allowed
    intro ⟨i, w⟩
    cases i with
    | none =>
        simpa [allowed, B, letterB] using
          (secondCoordinates.mul_mem_cancel_left (y := w) second_generator_mem).symm
    | some i => simp [allowed, B, letterB]
  · rcases hx with rfl
    change ∀ p, p ∈ allowed ↔ rep D (FreeGroup.of 3) p ∈ allowed
    intro ⟨i, w⟩
    cases i with
    | none => simp [allowed]
    | some i => fin_cases i <;> simp [allowed, swapOrdinary]

theorem newLift_mem_ambient_iff (D : CodeWords) (r : ℕ) (hcode : D.code = valievCode r)
    (w : FreeGroup (Fin 5)) :
    newLift D w ∈ ambient ↔ w ∈ secondCoordinates := by
  constructor
  · intro hw
    obtain ⟨p, hp, ht⟩ := positive_tracks (phase D.P 0) D.P 0
    have ht' : Tracks (P D) (some 0) (some (phase D.P 0)) p := ht
    have hpres := ambient_le_preserver D hw
    have hbase : (none, (1 : FreeGroup (Fin 5))) ∈ allowed := by simp [allowed]
    have himage := (hpres (none, 1)).mp hbase
    rw [word_actions D r hcode p ht' w 1] at himage
    apply partialConj_mem_second p hp
    simpa [allowed] using himage
  · intro hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.mp hw
    rw [map_zpow]
    apply ambient.zpow_mem
    change newValues D 3 ∈ ambient
    exact Subgroup.subset_closure (by simp [newValues])

theorem new_intersection (D : CodeWords) (r : ℕ) (hcode : D.code = valievCode r) :
    (newLift D).range ⊓ ambient =
      Subgroup.closure ({FreeGroup.of 1} : Set (FreeGroup (Fin 4))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨w, rfl⟩ := hx.1
    have hw := (newLift_mem_ambient_iff D r hcode w).mp hx.2
    obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.mp hw
    rw [map_zpow]
    apply Subgroup.zpow_mem
    exact Subgroup.subset_closure (by simp [newLift, newValues])
  · rw [Subgroup.closure_le, Set.singleton_subset_iff]
    refine ⟨⟨FreeGroup.of 3, by simp [newLift, newValues]⟩, ?_⟩
    exact Subgroup.subset_closure (by simp)

end
end UniversalGroup.CodeSubgroups.RightAction
