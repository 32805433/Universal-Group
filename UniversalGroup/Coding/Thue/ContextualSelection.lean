module

public import UniversalGroup.Coding.Thue.RowSelection

@[expose] public section

namespace UniversalGroup
namespace Thue
namespace Matiyasevich1993
namespace Priority
namespace ContextualSelection

open RowSelection

/-!
The contextual form of the row-selection argument on page 50.  The first
priority block only tests whether a letter is `e`; consequently, once its
normal form is clean (a binary word followed by all the `e`'s), an arbitrary
left context acts on the binary suffix by consing binary letters and applying
`selectOdd` once for every `e`.
-/

/-- Decode a non-`e` letter of `A₂` to the binary alphabet. -/
def lowerBit (x : A₂) : Fin 2 :=
  if x = a then 0 else 1

theorem liftBit_lowerBit {x : A₂} (hx : x ≠ e) :
    liftBit (lowerBit x) = x := by
  fin_cases x
  · rfl
  · rfl
  · exact (hx rfl).elim

theorem lowerBit_liftBit (x : Fin 2) : lowerBit (liftBit x) = x := by
  fin_cases x <;> simp [lowerBit, liftBit, a]

/-- A clean output of `pushE` can only arise by sampling an even binary
prefix followed by the existing block of `e`'s. -/
theorem pushE_clean_inv (W : List A₂) (B : List (Fin 2)) (v : ℕ)
    (hcount : eCount W = v)
    (hclean : pushE W = liftBinary B ++ List.replicate (v + 1) e) :
    ∃ C : List (Fin 2),
      W = liftBinary C ++ List.replicate v e ∧
      2 ∣ C.length ∧ selectOdd C = B := by
  induction W using List.twoStepInduction generalizing B v with
  | nil =>
      simp [pushE, eCount] at hcount hclean
      subst v
      have hB : B = [] := by
        cases B with
        | nil => rfl
        | cons x B =>
            fin_cases x <;> simp [liftBinary, liftBit, e] at hclean
      subst B
      exact ⟨[], by simp [liftBinary], by simp, rfl⟩
  | singleton x =>
      have hB : B = [] := by
        cases B with
        | nil => rfl
        | cons z B =>
            have hz := congrArg List.head? hclean
            fin_cases z <;> simp [pushE, liftBinary, liftBit, e] at hz
      subst B
      fin_cases x
      · have hv : v = 0 := by simpa [eCount, e] using hcount.symm
        rw [hv] at hclean
        simp [pushE, liftBinary, e] at hclean
      · have hv : v = 0 := by simpa [eCount, e] using hcount.symm
        rw [hv] at hclean
        simp [pushE, liftBinary, e] at hclean
      · have hv : v = 1 := by simpa [eCount, e] using hcount.symm
        refine ⟨[], ?_, by simp, rfl⟩
        rw [hv]
        simp [liftBinary, e]
  | cons_cons x y W ih _ =>
      by_cases hxy : x ≠ e ∧ y ≠ e
      · let xb : Fin 2 := lowerBit x
        let yb : Fin 2 := lowerBit y
        have hx : liftBit xb = x := liftBit_lowerBit hxy.1
        have hy : liftBit yb = y := liftBit_lowerBit hxy.2
        have hcountW : eCount W = v := by
          simpa [eCount, hxy.1, hxy.2] using hcount
        rw [pushE, ite_eq_left hxy] at hclean
        cases B with
        | nil =>
            have : y = e := by
              simpa [liftBinary, List.replicate_succ, e] using
                congrArg List.head? hclean
            exact (hxy.2 this).elim
        | cons z B =>
            have hz : liftBit z = y := by
              simpa [liftBinary] using (congrArg List.head? hclean).symm
            have htail :
                pushE W = liftBinary B ++ List.replicate (v + 1) e := by
              simpa [liftBinary, hz] using hclean
            obtain ⟨C, hW, heven, hselect⟩ := ih B v hcountW htail
            have hzy : z = yb := by
              apply liftBit_injective
              rw [hz, hy]
            subst z
            refine ⟨xb :: yb :: C, ?_, ?_, ?_⟩
            · simp only [liftBinary_cons, List.cons_append]
              rw [hx, hy, hW]
            · obtain ⟨k, hk⟩ := heven
              refine ⟨k + 1, ?_⟩
              simp [hk, Nat.mul_add]
            · simp [selectOdd, hselect]
      · rw [pushE, ite_eq_right hxy] at hclean
        have hB : B = [] := by
          cases B with
          | nil => rfl
          | cons z B =>
              have : e = liftBit z := by
                simpa [liftBinary] using congrArg List.head? hclean
              fin_cases z <;> simp [liftBit, e] at this
        subst B
        have hW : x :: y :: W = List.replicate v e := by
          simpa using List.cons.inj hclean |>.2
        exact ⟨[], by simpa [liftBinary] using hW, by simp, rfl⟩

/-! ### The binary process represented by a clean normalization -/

/-- Fold a left context over a binary suffix: binary letters are retained,
while every `e` keeps every second letter of the state to its right. -/
def process : List A₂ → List (Fin 2) → List (Fin 2)
  | [], W => W
  | x :: l, W =>
      if x = e then selectOdd (process l W)
      else lowerBit x :: process l W

/-- Every `e` sees an even binary state.  This is exactly the condition under
which normalization finishes with all `e`'s in one trailing block. -/
def Processable : List A₂ → List (Fin 2) → Prop
  | [], _ => True
  | x :: l, W =>
      Processable l W ∧ (x = e → 2 ∣ (process l W).length)

@[simp] theorem process_cons_e (l : List A₂) (W : List (Fin 2)) :
    process (e :: l) W = selectOdd (process l W) := by
  simp [process]

theorem process_cons_ne (x : A₂) (l : List A₂) (W : List (Fin 2))
    (hx : x ≠ e) :
    process (x :: l) W = lowerBit x :: process l W := by
  simp [process, hx]

theorem processable_cons_e_iff (l : List A₂) (W : List (Fin 2)) :
    Processable (e :: l) W ↔
      Processable l W ∧ 2 ∣ (process l W).length := by
  simp [Processable]

theorem processable_cons_ne_iff (x : A₂) (l : List A₂)
    (W : List (Fin 2)) (hx : x ≠ e) :
    Processable (x :: l) W ↔ Processable l W := by
  simp [Processable, hx]

@[simp] theorem eCount_e_cons (l : List A₂) :
    eCount (e :: l) = eCount l + 1 := by
  simp [eCount]

theorem eCount_cons_ne (x : A₂) (l : List A₂) (hx : x ≠ e) :
    eCount (x :: l) = eCount l := by
  simp [eCount, hx]

/-- A processable context has the advertised clean first-priority normal
form. -/
theorem firstNormal_eq_process (l : List A₂) (W : List (Fin 2))
    (hvalid : Processable l W) :
    firstNormal (l ++ liftBinary W) =
      liftBinary (process l W) ++ List.replicate (eCount l) e := by
  induction l with
  | nil =>
      simpa [process, firstNormal] using firstNormal_liftBinary_append W []
  | cons x l ih =>
      by_cases hx : x = e
      · subst x
        have hv := (processable_cons_e_iff l W).mp hvalid
        rw [List.cons_append, firstNormal_e_cons, ih hv.1]
        rw [pushE_liftBinary_even (process l W) (eCount l) hv.2]
        simp [process, eCount, List.replicate_succ]
      · have hv := (processable_cons_ne_iff x l W hx).mp hvalid
        rw [List.cons_append]
        unfold firstNormal
        rw [ite_eq_right hx, ih hv]
        have hxlift : liftBit (lowerBit x) = x := liftBit_lowerBit hx
        simp [process, hx, eCount, hxlift]

/-- Conversely, a clean normal form uniquely determines the binary process
and proves all of its parity obligations. -/
theorem processable_of_firstNormal_clean (l : List A₂) (W B : List (Fin 2))
    (hclean : firstNormal (l ++ liftBinary W) =
      liftBinary B ++ List.replicate (eCount l) e) :
    Processable l W ∧ process l W = B := by
  induction l generalizing B with
  | nil =>
      simp only [List.nil_append, eCount_nil, List.replicate_zero,
        List.append_nil] at hclean
      have hnormal : firstNormal (liftBinary W) = liftBinary W := by
        simpa [firstNormal] using firstNormal_liftBinary_append W []
      rw [hnormal] at hclean
      have hBW : W = B := liftBinary_injective hclean
      exact ⟨trivial, hBW⟩
  | cons x l ih =>
      by_cases hx : x = e
      · subst x
        have hcount : eCount (firstNormal (l ++ liftBinary W)) = eCount l := by
          rw [firstNormal_eCount]
          simp
        have hpush : pushE (firstNormal (l ++ liftBinary W)) =
            liftBinary B ++ List.replicate (eCount l + 1) e := by
          simpa [eCount, List.replicate_succ] using hclean
        obtain ⟨C, htail, heven, hselect⟩ :=
          pushE_clean_inv (firstNormal (l ++ liftBinary W)) B
            (eCount l) hcount hpush
        obtain ⟨hvalid, hprocess⟩ := ih C htail
        constructor
        · exact (processable_cons_e_iff l W).mpr ⟨hvalid, by
            simpa [hprocess] using heven⟩
        · rw [process_cons_e, hprocess, hselect]
      · have hform :
            x :: firstNormal (l ++ liftBinary W) =
              liftBinary B ++ List.replicate (eCount l) e := by
          simpa [firstNormal, hx, eCount] using hclean
        cases B with
        | nil =>
            cases hcount : eCount l with
            | zero => simp [hcount, liftBinary] at hform
            | succ v =>
                have hxe : x = e := by
                  simpa [hcount, List.replicate_succ, liftBinary, e] using
                    congrArg List.head? hform
                exact (hx hxe).elim
        | cons z B =>
            have hxz : x = liftBit z := by
              simpa [liftBinary] using congrArg List.head? hform
            have htail : firstNormal (l ++ liftBinary W) =
                liftBinary B ++ List.replicate (eCount l) e := by
              simpa [liftBinary, hxz] using hform
            obtain ⟨hvalid, hprocess⟩ := ih B htail
            constructor
            · exact (processable_cons_ne_iff x l W hx).mpr hvalid
            · rw [process_cons_ne x l W hx, hprocess, hxz,
                lowerBit_liftBit]

/-- Changing the binary suffix length by a multiple of the full sampling
period preserves every intermediate parity obligation.  After all samplings,
the output length changes by precisely the quotient `k`. -/
theorem process_periodic_shift (l : List A₂)
    (W₁ W₂ : List (Fin 2)) (k : ℕ)
    (hlen : W₂.length = W₁.length + k * 2 ^ eCount l) :
    (Processable l W₁ ↔ Processable l W₂) ∧
      (process l W₂).length = (process l W₁).length + k := by
  induction l generalizing W₁ W₂ k with
  | nil =>
      constructor
      · simp [Processable]
      · simpa [process] using hlen
  | cons x l ih =>
      by_cases hx : x = e
      · subst x
        have hlen' : W₂.length =
            W₁.length + (2 * k) * 2 ^ eCount l := by
          rw [show eCount (e :: l) = eCount l + 1 by simp [eCount],
            pow_succ] at hlen
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlen
        obtain ⟨hvalid, hout⟩ := ih W₁ W₂ (2 * k) hlen'
        constructor
        · rw [processable_cons_e_iff, processable_cons_e_iff, hvalid]
          constructor
          · rintro ⟨hproc, m, hm⟩
            refine ⟨hproc, m + k, ?_⟩
            rw [hout, hm]
            omega
          · rintro ⟨hproc, m, hm⟩
            have hle : 2 * k ≤ (process l W₂).length := by
              rw [hout]
              omega
            refine ⟨hproc, m - k, ?_⟩
            rw [hout] at hm
            omega
        · rw [process_cons_e, process_cons_e,
            selectOdd_length, selectOdd_length, hout]
          omega
      · have hrec := ih W₁ W₂ k (by
            simpa [eCount, hx] using hlen)
        constructor
        · simpa [Processable, hx] using hrec.1
        · rw [process_cons_ne x l W₂ hx,
            process_cons_ne x l W₁ hx]
          simp only [List.length_cons]
          omega

/-! ### Affine description and phase-neutral transpose replacement -/

/-- An arbitrary context acts affinely on every binary suffix: a fixed binary
prefix is followed by one fixed residue class modulo `2^(eCount l)`. -/
theorem process_affine (l : List A₂) :
    ∃ P : List (Fin 2), ∃ j : Fin (2 ^ eCount l), ∀ W,
      process l W = P ++ affineSample (eCount l) j W := by
  induction l with
  | nil =>
      refine ⟨[], ⟨0, by simp⟩, ?_⟩
      intro W
      simp [process, affineSample, thin]
  | cons x l ih =>
      obtain ⟨P, j, hprocess⟩ := ih
      by_cases hx : x = e
      · subst x
        rw [eCount_e_cons]
        obtain ⟨P', j', hsample⟩ :=
          selectOdd_prefix_affineSample (eCount l) P j
        refine ⟨P', j', ?_⟩
        intro W
        rw [process_cons_e, hprocess]
        exact hsample W
      · rw [eCount_cons_ne x l hx]
        refine ⟨lowerBit x :: P, j, ?_⟩
        intro W
        rw [process_cons_ne x l W hx, hprocess]
        rfl

/-- Replacing a rectangular transpose by another rectangular transpose keeps
the fixed affine contexts and selects the same row index. -/
theorem process_replace_transpose (l : List A₂) (p q : ℕ)
    (leftRows rightRows : Fin (2 ^ eCount l) → List (Fin 2))
    (R : List (Fin 2))
    (hp : ∀ i, (leftRows i).length = p)
    (hq : ∀ i, (rightRows i).length = q) :
    ∃ P : List (Fin 2), ∃ j : Fin (2 ^ eCount l), ∃ S : List (Fin 2),
      process l (transpose p leftRows ++ R) =
          P ++ leftRows j ++ S ∧
        process l (transpose q rightRows ++ R) =
          P ++ rightRows j ++ S := by
  obtain ⟨P, j, hprocess⟩ := process_affine l
  refine ⟨P, j, affineSample (eCount l) j R, ?_, ?_⟩
  · rw [hprocess, affineSample_transpose_append _ p leftRows j R hp]
    simp only [List.append_assoc]
  · rw [hprocess, affineSample_transpose_append _ q rightRows j R hq]
    simp only [List.append_assoc]

/-- Since both transpose lengths are multiples of the full sampling period,
replacing one by the other preserves clean processability. -/
theorem processable_replace_transpose (l : List A₂) (p q : ℕ)
    (leftRows : Fin (2 ^ eCount l) → List (Fin 2))
    (rightRows : Fin (2 ^ eCount l) → List (Fin 2))
    (R : List (Fin 2)) :
    Processable l (transpose p leftRows ++ R) ↔
      Processable l (transpose q rightRows ++ R) := by
  by_cases hpq : p ≤ q
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
    apply (process_periodic_shift l
      (transpose p leftRows ++ R)
      (transpose (p + d) rightRows ++ R) d ?_).1
    simp [transpose_length, Nat.add_mul, Nat.add_assoc, Nat.add_comm]
  · have hqp : q ≤ p := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqp
    exact (process_periodic_shift l
      (transpose q rightRows ++ R)
      (transpose (q + d) leftRows ++ R) d (by
        simp [transpose_length, Nat.add_mul, Nat.add_assoc,
          Nat.add_comm])).1.symm

/-! ### The contextual same-row theorem -/

/-- A word with no `e` is uniquely in the image of the binary inclusion. -/
theorem exists_liftBinary_of_eCount_zero {W : List A₂}
    (hW : eCount W = 0) :
    ∃ B : List (Fin 2), W = liftBinary B := by
  induction W with
  | nil => exact ⟨[], rfl⟩
  | cons x W ih =>
      have hx : x ≠ e := by
        intro hx
        subst x
        simp [eCount] at hW
      have ht : eCount W = 0 := by
        simpa [eCount, hx] using hW
      obtain ⟨B, rfl⟩ := ih ht
      refine ⟨lowerBit x :: B, ?_⟩
      simp [liftBit_lowerBit hx]

/-- Contextual row selection without reserving a terminal marker. The full
binary endpoint is retained, so a caller can enforce its exact code language
before separating any marker suffix. -/
theorem replace_transpose_endpoint (u p q : ℕ)
    (leftRows rightRows : Fin (2 ^ u) → List (Fin 2))
    (hp : ∀ i, (leftRows i).length = p)
    (hq : ∀ i, (rightRows i).length = q)
    {l r : List A₂} {B : List (Fin 2)}
    (hl : eCount l = u) (hr : eCount r = 0)
    (hclean : firstNormal (l ++ liftBinary (transpose p leftRows) ++ r) =
      liftBinary B ++ List.replicate u e) :
    ∃ j : Fin (2 ^ u), ∃ before after : List (Fin 2),
      B = before ++ leftRows j ++ after ∧
        firstNormal (l ++ liftBinary (transpose q rightRows) ++ r) =
          liftBinary (before ++ rightRows j ++ after) ++ List.replicate u e := by
  subst u
  obtain ⟨R, hr⟩ := exists_liftBinary_of_eCount_zero hr
  subst r
  have hclean' : firstNormal (l ++ liftBinary (transpose p leftRows ++ R)) =
      liftBinary B ++ List.replicate (eCount l) e := by
    simpa only [liftBinary_append, List.append_assoc] using hclean
  obtain ⟨hvalidLeft, hprocessLeft⟩ :=
    processable_of_firstNormal_clean l (transpose p leftRows ++ R) B hclean'
  obtain ⟨P, j, S, hleft, hright⟩ :=
    process_replace_transpose l p q leftRows rightRows R hp hq
  have hvalidRight : Processable l (transpose q rightRows ++ R) :=
    (processable_replace_transpose l p q leftRows rightRows R).mp hvalidLeft
  have hnormalRight := firstNormal_eq_process l (transpose q rightRows ++ R) hvalidRight
  refine ⟨j, P, S, (hleft.symm.trans hprocessLeft).symm, ?_⟩
  rw [hright] at hnormalRight
  simpa only [liftBinary_append, List.append_assoc] using hnormalRight

end ContextualSelection
end Priority
end Matiyasevich1993
end Thue
end UniversalGroup
