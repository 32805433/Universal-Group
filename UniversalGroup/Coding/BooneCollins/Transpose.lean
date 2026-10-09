module

public import UniversalGroup.Coding.BooneCollins.Boundary
public import UniversalGroup.Coding.Thue.RowSelection

@[expose] public section

/-!
# Transposition bridges for the exact compiler

Relate the column-major word definitions to the reusable priority decoder's
binary transposition and record what happens when the final matrix entry is
changed.
-/

namespace UniversalGroup.BooneCollinsTranspose

open Thue.Matiyasevich1993
open BooneCollinsWords

theorem psiLetter_eq_lift (N : ℕ) (i : Fin N) :
    psiLetter N i = Priority.liftBinary (Binary.rho₁Letter N i) := by
  simp [psiLetter, Binary.rho₁Letter, Priority.liftBinary, Priority.liftBit]
  rfl

theorem columnsFrom_range {s : ℕ} (rows : Fin s → PositiveWord) (start width : ℕ) :
    Priority.columnsFrom rows start width =
      (List.range' start width).flatMap (Priority.column rows) := by
  induction width generalizing start with
  | zero => simp [Priority.columnsFrom]
  | succ width ih => simp [Priority.columnsFrom, List.range'_succ, ih]

/-- Both definitions read the same rectangular array column by column. -/
theorem transpose_lift {s : ℕ} (width : ℕ) (rows : Fin s → PositiveWord) :
    BooneCollinsWords.transpose width (fun i => Priority.liftBinary (rows i)) =
      Priority.liftBinary (Priority.transpose width rows) := by
  rw [Priority.transpose, columnsFrom_range]
  simp only [BooneCollinsWords.transpose, List.range_eq_range', Priority.liftBinary,
    List.map_flatMap]
  congr 1
  funext j
  simp only [Priority.column, List.map_ofFn]
  congr 1
  funext i
  exact List.getD_map (rows i) 0 Priority.liftBit

theorem longLeft_eq (r t : ℕ) (lhs : Fin (2 ^ t) → Fin r) :
    longLeft r t lhs = Priority.liftBinary
      (Priority.transpose (r + 4) (fun i => Binary.rho₁Letter r (lhs i))) := by
  simp only [longLeft, psiLetter_eq_lift]
  exact transpose_lift _ _

theorem longRight_eq (r t : ℕ) (rhs : Fin (2 ^ t) → Fin r × Fin r) :
    longRight r t rhs = Priority.liftBinary
      (Priority.transpose (2 * (r + 4)) (fun i =>
        Binary.rho₁Letter r (rhs i).1 ++ Binary.rho₁Letter r (rhs i).2)) := by
  simp only [longRight, psiLetter_eq_lift, ← Priority.liftBinary_append]
  exact transpose_lift _ _

/-- Change only the last entry of the last row from `γ` to `β`. -/
def alterRows {s : ℕ} (rows : Fin s → PositiveWord) (i : Fin s) : PositiveWord :=
  if i.val + 1 = s then (rows i).dropLast ++ [0] else rows i

theorem alterRows_length {s width : ℕ} (rows : Fin s → PositiveWord)
    (hw : 0 < width) (hlen : ∀ i, (rows i).length = width) (i : Fin s) :
    (alterRows rows i).length = width := by
  simp only [alterRows]
  split_ifs
  · simp [hlen]
    omega
  · exact hlen i

theorem alterRows_starts {s width : ℕ} (rows : Fin s → PositiveWord)
    (hw : 3 ≤ width) (hlen : ∀ i, (rows i).length = width)
    (hstart : ∀ i, ∃ v, rows i = [0, 0] ++ v) (i : Fin s) :
    ∃ v, alterRows rows i = [0, 0] ++ v := by
  obtain ⟨v, hv⟩ := hstart i
  have hn : v ≠ [] := by
    intro he
    have hh := hlen i
    simp [hv, he] at hh
    omega
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hn
  by_cases hi : i.val + 1 = s
  · exact ⟨(z :: zs).dropLast ++ [0], by simp [alterRows, hi, hv]⟩
  · exact ⟨z :: zs, by simp [alterRows, hi, hv]⟩

private theorem alterRows_update {s : ℕ} (rows : Fin (s + 1) → PositiveWord) :
    alterRows rows = Function.update rows (Fin.last s) ((rows (Fin.last s)).dropLast ++ [0]) := by
  funext i
  by_cases hi : i = Fin.last s
  · subst i
    simp [alterRows]
  · have hn : i.val + 1 ≠ s + 1 := by
      intro hh
      apply hi
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    simp only [alterRows, ite_eq_right hn, Function.update_of_ne hi]

private theorem transpose_update_last {s w : ℕ}
    (rows : Fin (s + 1) → PositiveWord) (init : PositiveWord) (a b : Fin 2)
    (hi : rows (Fin.last s) = init ++ [a]) (hlen : init.length = w) :
    Priority.transpose (w + 1)
      (Function.update rows (Fin.last s) (init ++ [b])) =
      (Priority.transpose (w + 1) rows).dropLast ++ [b] := by
  let changed := Function.update rows (Fin.last s) (init ++ [b])
  have hp : Priority.columnsFrom changed 0 w = Priority.columnsFrom rows 0 w := by
    rw [columnsFrom_range, columnsFrom_range]
    apply List.flatMap_congr
    intro j hj
    have hjw : j < w := by simpa using hj
    unfold Priority.column
    congr 1
    funext i
    by_cases he : i = Fin.last s
    · subst i
      simp only [changed, Function.update_self, hi]
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    · simp [changed, he]
  let columnPrefix : PositiveWord := List.ofFn fun i : Fin s => (rows i.castSucc).getD w 0
  have hcol : Priority.column rows w = columnPrefix ++ [a] := by
    rw [Priority.column, List.ofFn_succ_last]
    simp only [columnPrefix, hi, ← hlen]
    simp
  have hcol' : Priority.column changed w = columnPrefix ++ [b] := by
    rw [Priority.column, List.ofFn_succ_last]
    have hbefore : (fun i : Fin s => (changed i.castSucc).getD w 0) =
        fun i : Fin s => (rows i.castSucc).getD w 0 := by
      funext i
      have he : i.castSucc ≠ Fin.last s := by
        intro h
        have hh := congrArg Fin.val h
        simp at hh
        omega
      simp [changed, he]
    rw [hbefore]
    simp [changed, columnPrefix, ← hlen]
  simp only [Priority.transpose, Priority.RowSelection.columnsFrom_last, Nat.zero_add]
  change Priority.columnsFrom changed 0 w ++ Priority.column changed w = _
  rw [hp, hcol, hcol']
  simp [List.append_assoc]

/-- The last-row alteration is exactly the last-letter alteration of the
whole transposed word. -/
theorem transpose_alterRows {s width : ℕ} (rows : Fin s → PositiveWord)
    (hs : 0 < s) (hw : 0 < width) (hlen : ∀ i, (rows i).length = width)
    (hend : ∀ i, ∃ v, rows i = v ++ [1]) :
    Priority.transpose width (alterRows rows) =
      (Priority.transpose width rows).dropLast ++ [0] := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
  obtain ⟨init, hi⟩ := hend (Fin.last s)
  have hinit : init.length = w := by
    have h := hlen (Fin.last s)
    simp [hi] at h
    omega
  rw [alterRows_update]
  have hl : (rows (Fin.last s)).dropLast = init := by simp [hi]
  rw [hl]
  exact transpose_update_last rows init 1 0 hi hinit

end UniversalGroup.BooneCollinsTranspose
