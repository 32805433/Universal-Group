module

public import UniversalGroup.Coding.Thue.FinalStage
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.NatCast

@[expose] public section

namespace UniversalGroup
namespace Thue
namespace Matiyasevich1993
namespace Priority

/-!
Transposition and priority normalization from Sections 2.3--2.4 of
Matiyasevich (1993). The normalizer preserves the priority-letter count;
a quantitative run estimate constrains the context of a transposed rule.
These are the invariants consumed by the Boone–Collins compiler.
-/

abbrev A₂ := Fin 3

def a : A₂ := 0
def b : A₂ := 1
def e : A₂ := 2

/-- A column of a rectangular family of words. -/
def column {t : ℕ} (rows : Fin t → List (Fin 2)) (j : ℕ) : List (Fin 2) :=
  List.ofFn fun i => (rows i).getD j 0

/-- Consecutive columns, starting at column `j`. -/
def columnsFrom {t : ℕ} (rows : Fin t → List (Fin 2)) : ℕ → ℕ → List (Fin 2)
  | _, 0 => []
  | j, k + 1 => column rows j ++ columnsFrom rows (j + 1) k

/-- The column-major words `L` and `M` displayed at the bottom of page 48. -/
def transpose {t : ℕ} (width : ℕ)
    (rows : Fin t → List (Fin 2)) : List (Fin 2) :=
  columnsFrom rows 0 width

@[simp] theorem columnsFrom_succ {t : ℕ} (rows : Fin t → List (Fin 2))
    (j k : ℕ) :
    columnsFrom rows j (k + 1) =
      column rows j ++ columnsFrom rows (j + 1) k := rfl

theorem column_length {t : ℕ} (rows : Fin t → List (Fin 2)) (j : ℕ) :
    (column rows j).length = t := by
  simp [column]

theorem columnsFrom_length {t width : ℕ}
    (rows : Fin t → List (Fin 2)) (start : ℕ) :
    (columnsFrom rows start width).length = width * t := by
  induction width generalizing start with
  | zero => simp [columnsFrom]
  | succ width ih =>
      simp [columnsFrom, column_length, ih, Nat.succ_mul, Nat.add_comm]

theorem transpose_length {t width : ℕ}
    (rows : Fin t → List (Fin 2)) :
    (transpose width rows).length = width * t :=
  columnsFrom_length rows 0

theorem column_zero_of_starts_aa {t : ℕ}
    (rows : Fin t → List (Fin 2))
    (hrows : ∀ i, ∃ tail, rows i = (0 : Fin 2) :: 0 :: tail) :
    column rows 0 = List.replicate t 0 := by
  unfold column
  have hfun :
      (fun i : Fin t => (rows i).getD 0 0) = fun _ => (0 : Fin 2) := by
    funext i
    obtain ⟨tail, hi⟩ := hrows i
    simp [hi]
  rw [hfun, List.ofFn_const]

theorem column_one_of_starts_aa {t : ℕ}
    (rows : Fin t → List (Fin 2))
    (hrows : ∀ i, ∃ tail, rows i = (0 : Fin 2) :: 0 :: tail) :
    column rows 1 = List.replicate t 0 := by
  unfold column
  have hfun :
      (fun i : Fin t => (rows i).getD 1 0) = fun _ => (0 : Fin 2) := by
    funext i
    obtain ⟨tail, hi⟩ := hrows i
    simp [hi]
  rw [hfun, List.ofFn_const]

/-- The long word begins with `2t` copies of `a`, the fact used on page 50. -/
theorem transpose_starts_two_columns {t width : ℕ}
    (rows : Fin t → List (Fin 2)) (hwidth : 2 ≤ width)
    (hrows : ∀ i, ∃ tail, rows i = (0 : Fin 2) :: 0 :: tail) :
    ∃ tail,
      transpose width rows = List.replicate (2 * t) 0 ++ tail := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hwidth
  refine ⟨columnsFrom rows 2 k, ?_⟩
  simp only [transpose, Nat.add_comm 2 k, columnsFrom]
  rw [column_zero_of_starts_aa rows hrows,
    column_one_of_starts_aa rows hrows]
  change List.replicate t 0 ++
      (List.replicate t 0 ++ columnsFrom rows 2 k) =
    List.replicate (2 * t) 0 ++ columnsFrom rows 2 k
  rw [← List.append_assoc]
  rw [← List.replicate_add]
  congr 2
  omega

/-! ### The first priority block -/

/-- Move one `e` rightwards through pairs of binary letters.  On a binary
word this retains every second letter and leaves the `e` at the end. -/
def pushE : List A₂ → List A₂
  | x :: y :: rest =>
      if x ≠ e ∧ y ≠ e then y :: pushE rest else e :: x :: y :: rest
  | rest => e :: rest

/-- Canonical normalization for rules (20)--(23), processing from right to
left. -/
def firstNormal : List A₂ → List A₂
  | [] => []
  | x :: rest =>
      if x = e then pushE (firstNormal rest)
      else x :: firstNormal rest

@[simp] theorem firstNormal_a_cons (W : List A₂) :
    firstNormal (a :: W) = a :: firstNormal W := by
  simp [firstNormal, a, e]

@[simp] theorem firstNormal_b_cons (W : List A₂) :
    firstNormal (b :: W) = b :: firstNormal W := by
  simp [firstNormal, b, e]

@[simp] theorem firstNormal_e_cons (W : List A₂) :
    firstNormal (e :: W) = pushE (firstNormal W) := by
  simp [firstNormal]

@[simp] theorem pushE_aa (W : List A₂) :
    pushE (a :: a :: W) = a :: pushE W := by
  simp [pushE, a, e]

@[simp] theorem pushE_ab (W : List A₂) :
    pushE (a :: b :: W) = b :: pushE W := by
  simp [pushE, a, b, e]

@[simp] theorem pushE_ba (W : List A₂) :
    pushE (b :: a :: W) = a :: pushE W := by
  simp [pushE, a, b, e]

@[simp] theorem pushE_bb (W : List A₂) :
    pushE (b :: b :: W) = b :: pushE W := by
  simp [pushE, b, e]

theorem firstNormal_prefix_congr (l : List A₂) {X Y : List A₂}
    (h : firstNormal X = firstNormal Y) :
    firstNormal (l ++ X) = firstNormal (l ++ Y) := by
  induction l with
  | nil => simpa
  | cons x l ih =>
      rw [List.cons_append, List.cons_append]
      unfold firstNormal
      split <;> simp_all

/-- The four left sides (20)--(23), using the local names for `a,b,e`. -/
def housekeepingF : Fin 4 → List A₂ := ![
  [e, a, a], [e, a, b], [e, b, a], [e, b, b]
]

/-- The four right sides (20)--(23). -/
def housekeepingE : Fin 4 → List A₂ := ![
  [a, e], [b, e], [a, e], [b, e]
]

/-- One use of a housekeeping rule in any two-sided context preserves the
first priority normal form. -/
theorem firstNormal_housekeeping
    (l r : List A₂) (i : Fin 4) :
    firstNormal (l ++ housekeepingF i ++ r) =
      firstNormal (l ++ housekeepingE i ++ r) := by
  rw [List.append_assoc, List.append_assoc]
  apply firstNormal_prefix_congr l
  fin_cases i <;> simp [housekeepingF, housekeepingE]

/-- One directed rewrite from the first priority block. -/
def FirstStep (X Y : List A₂) : Prop :=
  ∃ l r i,
    X = l ++ housekeepingF i ++ r ∧
    Y = l ++ housekeepingE i ++ r

abbrev FirstEq := Relation.ReflTransGen FirstStep

private theorem firstStep_rule (i : Fin 4) (l r : List A₂) :
    FirstStep (l ++ housekeepingF i ++ r) (l ++ housekeepingE i ++ r) :=
  ⟨l, r, i, rfl, rfl⟩

theorem firstStep_prefix (l : List A₂) {X Y : List A₂}
    (h : FirstStep X Y) : FirstStep (l ++ X) (l ++ Y) := by
  rcases h with ⟨l', r, i, rfl, rfl⟩
  refine ⟨l ++ l', r, i, ?_, ?_⟩ <;> simp [List.append_assoc]

theorem firstEq_prefix (l : List A₂) {X Y : List A₂}
    (h : FirstEq X Y) : FirstEq (l ++ X) (l ++ Y) :=
  h.lift (l ++ ·) (fun _ _ hstep => firstStep_prefix l hstep)

/-- Greedily moving one `e` is itself a directed derivation. -/
theorem pushE_reachable (W : List A₂) : FirstEq (e :: W) (pushE W) := by
  induction W using List.twoStepInduction with
  | nil => exact Relation.ReflTransGen.refl
  | singleton x => exact Relation.ReflTransGen.refl
  | cons_cons x y rest ih _ =>
      fin_cases x <;> fin_cases y
      · exact (Relation.ReflTransGen.single
          (firstStep_rule 0 [] rest)).trans (firstEq_prefix [a] ih)
      · exact (Relation.ReflTransGen.single
          (firstStep_rule 1 [] rest)).trans (firstEq_prefix [b] ih)
      · exact Relation.ReflTransGen.refl
      · exact (Relation.ReflTransGen.single
          (firstStep_rule 2 [] rest)).trans (firstEq_prefix [a] ih)
      · exact (Relation.ReflTransGen.single
          (firstStep_rule 3 [] rest)).trans (firstEq_prefix [b] ih)
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.refl

/-- Every word reduces to the canonical value computed by `firstNormal`. -/
theorem firstNormal_reachable (W : List A₂) : FirstEq W (firstNormal W) := by
  induction W with
  | nil => exact Relation.ReflTransGen.refl
  | cons x W ih =>
      have htail : FirstEq (x :: W) (x :: firstNormal W) := by
        simpa only [List.singleton_append] using firstEq_prefix [x] ih
      by_cases hx : x = e
      · subst x
        exact htail.trans (by simpa using pushE_reachable (firstNormal W))
      · simpa [firstNormal, hx] using htail

/-! ### The `e`-count and the final alignment argument -/

def eCount (W : List A₂) : ℕ := W.count e

@[simp] theorem eCount_nil : eCount [] = 0 := rfl

@[simp] theorem eCount_append (X Y : List A₂) :
    eCount (X ++ Y) = eCount X + eCount Y := by
  simp [eCount]

@[simp] theorem eCount_replicate_a (n : ℕ) :
    eCount (List.replicate n a) = 0 := by
  unfold eCount
  rw [List.count_eq_zero]
  simp [a, e]

@[simp] theorem eCount_ae : eCount [a, e] = 1 := by decide

theorem firstStep_eCount {X Y : List A₂} (h : FirstStep X Y) :
    eCount X = eCount Y := by
  rcases h with ⟨l, r, i, rfl, rfl⟩
  fin_cases i <;> simp [housekeepingF, housekeepingE, eCount, a, b, e]

theorem firstEq_eCount {X Y : List A₂} (h : FirstEq X Y) :
    eCount X = eCount Y := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (firstStep_eCount hstep)

theorem firstNormal_eCount (W : List A₂) :
    eCount (firstNormal W) = eCount W :=
  (firstEq_eCount (firstNormal_reachable W)).symm

/-- Include a binary word into the alphabet `{a,b,e}`. -/
def liftBit (x : Fin 2) : A₂ := Fin.castLE (by omega) x

def liftBinary (W : List (Fin 2)) : List A₂ := W.map liftBit

@[simp] theorem liftBinary_cons (x : Fin 2) (W : List (Fin 2)) :
    liftBinary (x :: W) = liftBit x :: liftBinary W := rfl

@[simp] theorem liftBinary_append (X Y : List (Fin 2)) :
    liftBinary (X ++ Y) = liftBinary X ++ liftBinary Y := by
  simp [liftBinary]

@[simp] theorem eCount_liftBinary (W : List (Fin 2)) :
    eCount (liftBinary W) = 0 := by
  unfold eCount
  rw [List.count_eq_zero]
  simp [liftBinary, liftBit, e]

theorem liftBit_injective : Function.Injective liftBit := by
  intro x y h
  apply Fin.ext
  exact congrArg (fun z : A₂ => z.val) h

theorem liftBinary_injective : Function.Injective liftBinary :=
  liftBit_injective.list_map

@[simp] theorem pushE_replicate_e (u : ℕ) :
    pushE (List.replicate u e) = e :: List.replicate u e := by
  cases u with
  | zero => rfl
  | succ u =>
      cases u with
      | zero => rfl
      | succ u =>
          rw [List.replicate_succ, List.replicate_succ]
          simp [pushE, e]

theorem firstNormal_replicate_e (u : ℕ) :
    firstNormal (List.replicate u e) = List.replicate u e := by
  induction u with
  | zero => rfl
  | succ u ih =>
      rw [List.replicate_succ, firstNormal_e_cons, ih]
      exact pushE_replicate_e u

theorem firstNormal_liftBinary_append (W : List (Fin 2)) (T : List A₂) :
    firstNormal (liftBinary W ++ T) =
      liftBinary W ++ firstNormal T := by
  induction W with
  | nil => rfl
  | cons x W ih =>
      rw [liftBinary_cons, List.cons_append]
      fin_cases x
      · change firstNormal (a :: (liftBinary W ++ T)) =
          a :: (liftBinary W ++ firstNormal T)
        rw [firstNormal_a_cons, ih]
      · change firstNormal (b :: (liftBinary W ++ T)) =
          b :: (liftBinary W ++ firstNormal T)
        rw [firstNormal_b_cons, ih]

/-- Absence of a run `aaa`. -/
def NoAAA (W : List A₂) : Prop :=
  ¬ ∃ l r, W = l ++ [a, a, a] ++ r

/-- A word contains `k` consecutive copies of `a`. -/
def HasARun (k : ℕ) (W : List A₂) : Prop :=
  ∃ l r, W = l ++ List.replicate k a ++ r

theorem hasARun_prefix (p : List A₂) {k : ℕ} {W : List A₂}
    (h : HasARun k W) : HasARun k (p ++ W) := by
  obtain ⟨l, r, rfl⟩ := h
  refine ⟨p ++ l, r, ?_⟩
  simp only [List.append_assoc]

theorem hasARun_of_le {m n : ℕ} {W : List A₂} (hmn : m ≤ n)
    (h : HasARun n W) : HasARun m W := by
  obtain ⟨l, r, rfl⟩ := h
  refine ⟨l, List.replicate (n - m) a ++ r, ?_⟩
  calc
    l ++ List.replicate n a ++ r =
        l ++ List.replicate (m + (n - m)) a ++ r := by
          rw [Nat.add_sub_of_le hmn]
    _ = l ++ List.replicate m a ++
        (List.replicate (n - m) a ++ r) := by
          simp only [List.replicate_add, List.append_assoc]

/-- On a binary run, `pushE` keeps every second letter. -/
theorem pushE_replicate_even (k : ℕ) (W : List A₂) :
    pushE (List.replicate (2 * k) a ++ W) =
      List.replicate k a ++ pushE W := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by omega,
        List.replicate_add]
      change pushE (a :: a :: (List.replicate (2 * k) a ++ W)) =
        a :: (List.replicate k a ++ pushE W)
      rw [pushE_aa, ih]

/-- A possible one-letter parity offset before an even run does not affect
the sharp halving estimate. -/
theorem pushE_singleton_hasARun (x : A₂) (k : ℕ) (W : List A₂) :
    HasARun k (pushE (x :: List.replicate (2 * k) a ++ W)) := by
  cases k with
  | zero =>
      exact ⟨[], pushE (x :: W), by simp⟩
  | succ k =>
      have hrep :
          List.replicate (2 * (k + 1)) a ++ W =
            a :: (List.replicate (2 * k) a ++ (a :: W)) := by
        rw [show 2 * (k + 1) = 1 + 2 * k + 1 by omega,
          List.replicate_add, List.replicate_add]
        simp only [List.replicate_one,
          List.append_assoc, List.cons_append, List.nil_append]
      change HasARun (k + 1)
        (pushE (x :: (List.replicate (2 * (k + 1)) a ++ W)))
      by_cases hx : x = e
      · subst x
        apply hasARun_of_le (by omega : k + 1 ≤ 2 * (k + 1))
        refine ⟨[e, e], W, ?_⟩
        calc
          pushE (e :: (List.replicate (2 * (k + 1)) a ++ W)) =
              e :: e :: (List.replicate (2 * (k + 1)) a ++ W) := by
                rw [hrep]
                simp [pushE, a, e]
          _ = [e, e] ++ List.replicate (2 * (k + 1)) a ++ W := by
                simp
      · rw [hrep]
        have hpush : ∀ Z : List A₂,
            pushE (x :: a :: Z) = a :: pushE Z := by
          intro Z
          have hxe : x ≠ (2 : A₂) := by simpa [e] using hx
          simp [pushE, hxe, a, e]
        rw [hpush, pushE_replicate_even]
        refine ⟨[], pushE (a :: W), ?_⟩
        simp only [List.nil_append]
        rw [show k + 1 = Nat.succ k by omega, List.replicate_succ]
        simp only [List.cons_append]

/-- The sharp run estimate for one first-priority normalization step: one
`e` can at most halve the length of an `a`-run. -/
theorem pushE_hasARun_half {k : ℕ} {W : List A₂}
    (h : HasARun (2 * k) W) : HasARun k (pushE W) := by
  obtain ⟨l, r, rfl⟩ := h
  induction l using List.twoStepInduction with
  | nil =>
      simp only [List.nil_append]
      rw [pushE_replicate_even]
      exact ⟨[], pushE r, by simp⟩
  | singleton x =>
      exact pushE_singleton_hasARun x k r
  | cons_cons x y l ih _ =>
      by_cases hxy : x ≠ e ∧ y ≠ e
      · rw [show x :: y :: l ++ List.replicate (2 * k) a ++ r =
            x :: y :: (l ++ List.replicate (2 * k) a ++ r) by simp]
        change HasARun k (if x ≠ e ∧ y ≠ e then
          y :: pushE (l ++ List.replicate (2 * k) a ++ r)
          else e :: x :: y :: (l ++ List.replicate (2 * k) a ++ r))
        rw [ite_eq_left hxy]
        exact hasARun_prefix [y] ih
      · rw [show x :: y :: l ++ List.replicate (2 * k) a ++ r =
            x :: y :: (l ++ List.replicate (2 * k) a ++ r) by simp]
        change HasARun k (if x ≠ e ∧ y ≠ e then
          y :: pushE (l ++ List.replicate (2 * k) a ++ r)
          else e :: x :: y :: (l ++ List.replicate (2 * k) a ++ r))
        rw [ite_eq_right hxy]
        apply hasARun_of_le (by omega : k ≤ 2 * k)
        exact ⟨[e, x, y] ++ l, r, by simp [List.append_assoc]⟩

theorem firstNormal_replicate_a_append (n : ℕ) (W : List A₂) :
    firstNormal (List.replicate n a ++ W) =
      List.replicate n a ++ firstNormal W := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [List.cons_append, firstNormal_a_cons, ih]

/-- After normalizing a prefix `X`, every one of its `e` letters can have
halved a following run at most once. -/
theorem firstNormal_hasARun_scaled (X Y : List A₂) (k : ℕ) :
    HasARun k (firstNormal
      (X ++ List.replicate (2 ^ eCount X * k) a ++ Y)) := by
  induction X generalizing k with
  | nil =>
      rw [eCount_nil, pow_zero, one_mul, List.nil_append,
        firstNormal_replicate_a_append]
      exact ⟨[], firstNormal Y, by simp⟩
  | cons x X ih =>
      by_cases hx : x = e
      · subst x
        change HasARun k (pushE (firstNormal
          (X ++ List.replicate (2 ^ eCount (e :: X) * k) a ++ Y)))
        simpa [eCount, pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm] using
            (pushE_hasARun_half (ih (k := 2 * k)))
      · have hi := hasARun_prefix [x] (ih (k := k))
        simpa [eCount, hx, firstNormal] using hi

theorem noAAA_not_hasARun_three {W : List A₂} (h : NoAAA W) :
    ¬ HasARun 3 W := by
  simpa [NoAAA, HasARun] using h

/-- The elementary but nontrivial run estimate invoked on page 50: destroying
a run of `run` many `a`'s while producing a first-block normal form with no
`aaa` requires at least `u` occurrences of `e` in the left context. -/
def LongRunRequirement (u run : ℕ) : Prop :=
  ∀ X Y,
    NoAAA (firstNormal (X ++ List.replicate run a ++ Y)) →
    u ≤ eCount X

/-- The quantitative assertion used on page 50.  The transposed long side
starts with `2t = 2 * 2^u` copies of `a`; if fewer than `u` priority letters
occur to its left, at least four consecutive `a`'s survive normalization. -/
theorem longRunRequirement_two_power (u : ℕ) :
    LongRunRequirement u (2 * 2 ^ u) := by
  intro X Y hnormal
  by_contra hbound
  have hlt : eCount X < u := Nat.lt_of_not_ge hbound
  have hpow : 2 ^ (eCount X + 2) ≤ 2 ^ (u + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hscale : 2 ^ eCount X * 4 ≤ 2 * 2 ^ u := by
    calc
      2 ^ eCount X * 4 = 2 ^ (eCount X + 2) := by
        rw [pow_add]
        congr
      _ ≤ 2 ^ (u + 1) := hpow
      _ = 2 * 2 ^ u := by simp [pow_succ, Nat.mul_comm]
  have hrep :
      List.replicate (2 * 2 ^ u) a ++ Y =
        List.replicate (2 ^ eCount X * 4) a ++
          (List.replicate (2 * 2 ^ u - 2 ^ eCount X * 4) a ++ Y) := by
    calc
      List.replicate (2 * 2 ^ u) a ++ Y =
          List.replicate
            (2 ^ eCount X * 4 + (2 * 2 ^ u - 2 ^ eCount X * 4)) a ++ Y := by
              rw [Nat.add_sub_of_le hscale]
      _ = List.replicate (2 ^ eCount X * 4) a ++
          (List.replicate (2 * 2 ^ u - 2 ^ eCount X * 4) a ++ Y) := by
            simp only [List.replicate_add, List.append_assoc]
  have hfour : HasARun 4
      (firstNormal (X ++ List.replicate (2 * 2 ^ u) a ++ Y)) := by
    rw [List.append_assoc, hrep, ← List.append_assoc]
    exact firstNormal_hasARun_scaled X
      (List.replicate (2 * 2 ^ u - 2 ^ eCount X * 4) a ++ Y) 4
  exact noAAA_not_hasARun_three hnormal
    (hasARun_of_le (by omega : 3 ≤ 4) hfour)

end Priority
end Matiyasevich1993
end Thue
end UniversalGroup
