module

public import UniversalGroup.Coding.BooneCollins.Compiler

@[expose] public section

/-!
# The compiler rules and the public recognition rules coincide

The compiler writes its two short relations in the reverse direction from
the public table.  Rewriting is symmetric, so the two step relations and
their reflexive transitive closures are identical.
-/

namespace UniversalGroup.BooneCollinsRules

open Thue.Matiyasevich1993 BooneCollinsWords BooneCollinsCompiler BooneCollinsDecoder

theorem step_iff (r t : ℕ) (lhs : Fin (2 ^ t) → Fin r)
    (rhs : Fin (2 ^ t) → Fin r × Fin r) (X Y : PositiveWord) :
    ThueStep (finalSystem (longLeft r t lhs) (longRight r t rhs)) X Y ↔
      PositiveStep (words r t lhs rhs).rules X Y := by
  constructor
  · rintro ⟨l, s, x, y, ⟨i, hi⟩, hw⟩
    have hx := congrArg Prod.fst hi
    have hy := congrArg Prod.snd hi
    dsimp [finalSystem, finiteSystem] at hx hy
    subst x
    subst y
    refine ⟨l, s, (words r t lhs rhs).E i, (words r t lhs rhs).F i, ⟨i, rfl⟩, ?_⟩
    fin_cases i <;>
      simpa [words, shortLeft, shortRight, or_comm] using hw
  · rintro ⟨l, s, x, y, ⟨i, hi⟩, hw⟩
    have hx := congrArg Prod.fst hi
    have hy := congrArg Prod.snd hi
    dsimp [CodeWords.rules] at hx hy
    subst x
    subst y
    refine ⟨l, s,
      (![shortLeft 0, shortLeft 1, tau (longLeft r t lhs)] : Fin 3 → PositiveWord) i,
      (![shortRight, shortRight, tau (longRight r t rhs)] : Fin 3 → PositiveWord) i,
      ⟨i, rfl⟩, ?_⟩
    fin_cases i <;>
      simpa [words, shortLeft, shortRight, or_comm] using hw

theorem eq_iff (r t : ℕ) (lhs : Fin (2 ^ t) → Fin r)
    (rhs : Fin (2 ^ t) → Fin r × Fin r) (X Y : PositiveWord) :
    ThueEq (finalSystem (longLeft r t lhs) (longRight r t rhs)) X Y ↔
      PositiveEq (words r t lhs rhs).rules X Y := by
  have hrel : ThueStep (finalSystem (longLeft r t lhs) (longRight r t rhs)) =
      PositiveStep (words r t lhs rhs).rules := by
    funext U V
    exact propext (step_iff r t lhs rhs U V)
  simp only [ThueEq, PositiveEq, hrel]

end UniversalGroup.BooneCollinsRules
