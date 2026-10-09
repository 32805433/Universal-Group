module

public import UniversalGroup.Coding.Thue.RowSelection

@[expose] public section

namespace UniversalGroup.Thue.Matiyasevich1993.PriorityCompiler
open Priority Priority.RowSelection

/-- The priority endpoint with an arbitrary distinguished terminal bit. -/
def encodeWith (u : ℕ) (marker : Fin 2) (W : List (Fin 2)) : List Priority.A₂ :=
  liftBinary (W ++ [marker]) ++ List.replicate u e

def housekeepingIndex (i : Fin 4) : Fin 5 := Fin.castLE (by omega) i

@[simp] theorem stage₂F_housekeepingIndex (L : List Priority.A₂)
    (i : Fin 4) :
    stage₂F L (housekeepingIndex i) = housekeepingF i := by
  fin_cases i <;> simp [stage₂F, housekeepingF, housekeepingIndex] <;> decide

@[simp] theorem stage₂E_housekeepingIndex (M : List Priority.A₂)
    (i : Fin 4) :
    stage₂E M (housekeepingIndex i) = housekeepingE i := by
  fin_cases i <;> simp [stage₂E, housekeepingE, housekeepingIndex] <;> decide

theorem firstStep_to_thueStep (L M : List Priority.A₂)
    {X Y : List Priority.A₂} (h : FirstStep X Y) :
    ThueStep (stage₂System L M) X Y := by
  rcases h with ⟨l, s, i, rfl, rfl⟩
  exact ⟨l, s, housekeepingF i, housekeepingE i,
    ⟨housekeepingIndex i, by simp⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- Every directed first-priority reduction is also a derivation in the
symmetric five-relation Thue system. -/
theorem firstEq_to_stage₂Eq (L M : List Priority.A₂)
    {X Y : List Priority.A₂} (h : FirstEq X Y) :
    ThueEq (stage₂System L M) X Y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (firstStep_to_thueStep L M hstep)


theorem firstEq_paddedTransposeLast_expand
    (u width : ℕ) (rows : Fin (2 ^ u) → List (Fin 2))
    (j : Fin (2 ^ u)) (z : Fin 2) (tail : List (Fin 2))
    (hlen : ∀ i, (rows i).length = width) :
    FirstEq
      (List.replicate u e ++
        liftBinary (paddedTransposeLast width rows j z ++ expand u tail))
      (liftBinary (rows j ++ z :: tail) ++ List.replicate u e) := by
  have hpad : 2 ^ u ∣ (paddedTransposeLast width rows j z).length := by
    refine ⟨width + 1, ?_⟩
    simpa [Nat.mul_comm] using paddedTransposeLast_length rows j z
  have htotal : 2 ^ u ∣
      (paddedTransposeLast width rows j z ++ expand u tail).length := by
    rw [List.length_append]
    exact Nat.dvd_add hpad (expand_length_dvd u tail)
  have hthin :
      thin u (paddedTransposeLast width rows j z ++ expand u tail) =
        rows j ++ z :: tail := by
    rw [thin_append_of_dvd u _ _ hpad,
      thin_paddedTranspose_last u width rows j z hlen, thin_expand]
    simp
  have h := firstNormal_reachable
    (List.replicate u e ++
      liftBinary (paddedTransposeLast width rows j z ++ expand u tail))
  rw [firstNormal_replicate_e_liftBinary u _ htotal, hthin] at h
  exact h

theorem append_marker_eq_cons (marker : Fin 2) (right : List (Fin 2)) :
    ∃ z tail, right ++ [marker] = z :: tail := by
  cases right with
  | nil => exact ⟨marker, [], rfl⟩
  | cons z tail => exact ⟨z, tail ++ [marker], rfl⟩

theorem encode_append_eq (u : ℕ) (marker : Fin 2) (X Y : List (Fin 2)) :
    encodeWith u marker (X ++ Y) = liftBinary X ++ encodeWith u marker Y := by
  simp [encodeWith, List.append_assoc]

/-- One directed binary row replacement is simulated by the four
housekeeping relations, one use of the long relation, and the housekeeping
relations again. -/
theorem simulate_row (u p q : ℕ) (marker : Fin 2)
    (leftRows rightRows : Fin (2 ^ u) → List (Fin 2))
    (hleft : ∀ i, (leftRows i).length = p)
    (hright : ∀ i, (rightRows i).length = q)
    (j : Fin (2 ^ u)) (left right : List (Fin 2)) :
    ThueEq (stage₂System (liftBinary (transpose p leftRows)) (liftBinary (transpose q rightRows)))
      (encodeWith u marker (left ++ leftRows j ++ right))
      (encodeWith u marker (left ++ rightRows j ++ right)) := by
  obtain ⟨z, tail, hmarker⟩ := append_marker_eq_cons marker right
  let leftBlock := paddedTransposeLast
    p leftRows j z ++
      expand u tail
  let rightBlock := paddedTransposeLast
    q rightRows j z ++
      expand u tail
  have liftBinary_nil : liftBinary [] = [] := rfl
  have hleftDer : FirstEq
      (List.replicate u e ++ liftBinary leftBlock)
      (encodeWith u marker (leftRows j ++ right)) := by
    have h := firstEq_paddedTransposeLast_expand
      u p
      leftRows j z tail hleft
    have hrow : leftRows j ++ z :: tail =
        (leftRows j ++ right) ++ [marker] := by
      rw [← hmarker]
      simp
    rw [hrow] at h
    convert h using 1
    simp [encodeWith, liftBinary_append, liftBit, liftBinary_nil, List.append_assoc]
    try rfl
  have hrightDer : FirstEq
      (List.replicate u e ++ liftBinary rightBlock)
      (encodeWith u marker (rightRows j ++ right)) := by
    have h := firstEq_paddedTransposeLast_expand
      u q
      rightRows j z tail hright
    have hrow : rightRows j ++ z :: tail =
        (rightRows j ++ right) ++ [marker] := by
      rw [← hmarker]
      simp
    rw [hrow] at h
    convert h using 1
    simp [encodeWith, liftBinary_append, liftBit, liftBinary_nil, List.append_assoc]
    try rfl
  have hlong : ThueEq (stage₂System (liftBinary (transpose p leftRows)) (liftBinary (transpose q rightRows)))
      (List.replicate u e ++ liftBinary leftBlock)
      (List.replicate u e ++ liftBinary rightBlock) := by
    apply Relation.ReflTransGen.single
    refine ⟨List.replicate u e ++
        liftBinary (List.replicate (2 ^ u - 1 - j.val) 0),
      liftBinary (List.replicate j.val 0 ++ [z] ++ expand u tail),
      liftBinary (transpose p leftRows), liftBinary (transpose q rightRows), ⟨4, by simp [stage₂F, stage₂E]⟩, ?_⟩
    left
    constructor <;>
      simp [leftBlock, rightBlock, paddedTransposeLast,
         liftBinary_append, List.append_assoc]
  have hinner : ThueEq (stage₂System (liftBinary (transpose p leftRows)) (liftBinary (transpose q rightRows)))
      (encodeWith u marker (leftRows j ++ right))
      (encodeWith u marker (rightRows j ++ right)) :=
    (thueEq_symm (firstEq_to_stage₂Eq _ _ hleftDer)).trans
      (hlong.trans (firstEq_to_stage₂Eq _ _ hrightDer))
  simpa [encode_append_eq, List.append_assoc] using
    thueEq_context (liftBinary left) [] hinner

/-- Forward half of Matiyasevich's priority-compression equivalence: every
binary rewrite, in arbitrary two-sided context, is simulated by the
five-relation system on `{a,b,e}`. -/
theorem simulate_binary (u p q : ℕ) (marker : Fin 2)
    (leftRows rightRows : Fin (2 ^ u) → List (Fin 2))
    (hleft : ∀ i, (leftRows i).length = p)
    (hright : ∀ i, (rightRows i).length = q)
    {X Y : List (Fin 2)} (h : ThueEq (finiteSystem leftRows rightRows) X Y) :
    ThueEq (stage₂System (liftBinary (transpose p leftRows)) (liftBinary (transpose q rightRows)))
      (encodeWith u marker X) (encodeWith u marker Y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      rcases hstep with ⟨left, right, x, y, ⟨j, hrow⟩, hwords⟩
      injection hrow with hx hy
      subst x
      subst y
      rcases hwords with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih.trans (simulate_row u p q marker leftRows rightRows hleft hright j left right)
      · exact ih.trans (thueEq_symm (simulate_row u p q marker leftRows rightRows hleft hright j left right))

end UniversalGroup.Thue.Matiyasevich1993.PriorityCompiler
