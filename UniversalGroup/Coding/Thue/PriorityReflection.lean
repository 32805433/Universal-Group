module

public import UniversalGroup.Coding.Thue.ContextualSelection

@[expose] public section

namespace UniversalGroup.Thue.Matiyasevich1993.PriorityCompiler
open Priority

/-- An initial run in a long word forces every priority symbol into its
left context. No hypothesis on the final letter of the long word is needed. -/
theorem context_counts_of_long {u run : ℕ} {L W left right : List A₂}
    (hshape : ∃ tail, L = List.replicate run a ++ tail)
    (hrequire : LongRunRequirement u run)
    (hnormal : NoAAA (firstNormal W)) (hcount : eCount W = u)
    (hword : W = left ++ L ++ right) (hL : eCount L = 0) :
    eCount left = u ∧ eCount right = 0 := by
  obtain ⟨tail, hshape⟩ := hshape
  have hnormal' : NoAAA (firstNormal
      (left ++ List.replicate run a ++ (tail ++ right))) := by
    simpa only [hword, hshape, List.append_assoc] using hnormal
  have hleft : u ≤ eCount left := hrequire left _ hnormal'
  have hsum : eCount left + eCount right = u := by
    calc
      eCount left + eCount right = eCount W := by
        rw [hword, eCount_append, eCount_append, hL]
        omega
      _ = u := hcount
  omega

/-- Generalized contextual replacement with the complete binary endpoint.
This also accommodates Boone–Collins's final `gamma` marker. -/
theorem select_same_row {u p q : ℕ}
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
          liftBinary (before ++ rightRows j ++ after) ++ List.replicate u e :=
  ContextualSelection.replace_transpose_endpoint u p q leftRows rightRows hp hq hl hr hclean

end UniversalGroup.Thue.Matiyasevich1993.PriorityCompiler
