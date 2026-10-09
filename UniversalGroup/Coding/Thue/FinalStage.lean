module

public import UniversalGroup.Coding.Thue.Core
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace UniversalGroup

namespace Thue

namespace Matiyasevich1993

/-!
# Binary parsing and the intermediate five-rule system

The right-to-left decoder reconstructs a binary word up to one unmatched
initial bit. The Boone–Collins compiler uses this precise residual alternative
together with the priority normalizer. The five-rule system records the four
housekeeping rules and one transposed relation.
-/

/-- The letters `a`, `b`, and `e` of the penultimate alphabet. -/
abbrev A₂ := Fin 3

namespace FinalLetters

abbrev a : A₂ := 0
abbrev b : A₂ := 1
abbrev e : A₂ := 2

end FinalLetters

open FinalLetters

/-- Equation (26), with `c = 1` and `d = 0`. -/
def rho₂Letter : A₂ → List (Fin 2) := ![
  [(1 : Fin 2)],
  [(1 : Fin 2), 0],
  [(0 : Fin 2), 0]
]

/-- The homomorphic extension of `ρ₂` to words. -/
def rho₂ (W : List A₂) : List (Fin 2) :=
  W.flatMap rho₂Letter

@[simp] theorem rho₂_cons (x : A₂) (W : List A₂) :
    rho₂ (x :: W) = rho₂Letter x ++ rho₂ W := by
  simp [rho₂]

@[simp] theorem rho₂_append (X Y : List A₂) :
    rho₂ (X ++ Y) = rho₂ X ++ rho₂ Y := by
  simp [rho₂]

/-- The right-to-left decoder `φ₂` from page 51, expressed on the reversed
input.  Reversed codewords are `1`, `01`, and `00`; a lone leading `0` is the
single possible unmatched `d`. -/
def phi₂Aux : List (Fin 2) → List A₂
  | [] => []
  | x :: xs =>
      if x = 1 then
        a :: phi₂Aux xs
      else
        match xs with
        | [] => []
        | y :: ys =>
            if y = 1 then b :: phi₂Aux ys else e :: phi₂Aux ys

/-- The inverse map `φ₂` in the orientation used in the paper. -/
def phi₂ (W : List (Fin 2)) : List A₂ :=
  (phi₂Aux (W.reverse)).reverse

private theorem phi₂Aux_rho₂_reverse_append (W : List A₂)
    (Z : List (Fin 2)) :
    phi₂Aux ((rho₂ W).reverse ++ Z) = W.reverse ++ phi₂Aux Z := by
  induction W generalizing Z with
  | nil => simp [rho₂]
  | cons x W ih =>
      rw [rho₂_cons, List.reverse_append, List.append_assoc, ih]
      fin_cases x
      · simp only [rho₂Letter]
        rw [phi₂Aux.eq_def]
        simp [a]
      · simp only [rho₂Letter]
        rw [phi₂Aux.eq_def]
        simp [b]
      · simp only [rho₂Letter]
        rw [phi₂Aux.eq_def]
        simp [e]

/-- `φ₂` is a left inverse to the binary encoding, as required below (26). -/
@[simp] theorem phi₂_rho₂ (W : List A₂) : phi₂ (rho₂ W) = W := by
  have h := phi₂Aux_rho₂_reverse_append W []
  simp only [List.append_nil] at h
  rw [phi₂, h]
  simp [phi₂Aux]

/-- Appending a complete encoded word cannot interact with the decoding of
the prefix.  This is the algebraic form of the right-to-left parsing used on
page 52. -/
theorem phi₂_append_rho₂ (X : List (Fin 2)) (W : List A₂) :
    phi₂ (X ++ rho₂ W) = phi₂ X ++ W := by
  have h := phi₂Aux_rho₂_reverse_append W X.reverse
  have h' := congrArg List.reverse h
  simpa [phi₂, List.reverse_append] using h'

private def rho₂Reverse (W : List A₂) : List (Fin 2) :=
  (rho₂ W.reverse).reverse

private theorem rho₂Reverse_cons (x : A₂) (W : List A₂) :
    rho₂Reverse (x :: W) = (rho₂Letter x).reverse ++ rho₂Reverse W := by
  simp [rho₂Reverse, rho₂]

private theorem fin₂_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  omega

@[simp] private theorem phi₂Aux_c (Z : List (Fin 2)) :
    phi₂Aux ((1 : Fin 2) :: Z) = a :: phi₂Aux Z := by
  rw [phi₂Aux.eq_def]
  simp

@[simp] private theorem phi₂Aux_dd (Z : List (Fin 2)) :
    phi₂Aux ((0 : Fin 2) :: 0 :: Z) = e :: phi₂Aux Z := by
  rw [phi₂Aux.eq_def]
  simp

@[simp] private theorem phi₂Aux_dc (Z : List (Fin 2)) :
    phi₂Aux ((0 : Fin 2) :: 1 :: Z) = b :: phi₂Aux Z := by
  rw [phi₂Aux.eq_def]
  simp

@[simp] private theorem rho₂Reverse_a (W : List A₂) :
    rho₂Reverse (a :: W) = (1 : Fin 2) :: rho₂Reverse W := by
  simpa [rho₂Letter, a] using rho₂Reverse_cons a W

@[simp] private theorem rho₂Reverse_b (W : List A₂) :
    rho₂Reverse (b :: W) = (0 : Fin 2) :: 1 :: rho₂Reverse W := by
  simpa [rho₂Letter, b] using rho₂Reverse_cons b W

@[simp] private theorem rho₂Reverse_e (W : List A₂) :
    rho₂Reverse (e :: W) = (0 : Fin 2) :: 0 :: rho₂Reverse W := by
  simpa [rho₂Letter, e] using rho₂Reverse_cons e W

/-- The parser consumes every binary word, with at most one unmatched initial
`d`.  This is the dichotomy immediately after the definition of `φ₂` on
page 51 (written here on reversed words). -/
private theorem phi₂Aux_reconstruct (Z : List (Fin 2)) :
    Z = rho₂Reverse (phi₂Aux Z) ∨
      Z = rho₂Reverse (phi₂Aux Z) ++ [(0 : Fin 2)] := by
  induction Z using List.twoStepInduction with
  | nil => exact Or.inl (by simp [phi₂Aux, rho₂Reverse, rho₂])
  | singleton x =>
      rcases fin₂_cases x with rfl | rfl
      · exact Or.inr (by simp [phi₂Aux.eq_def, rho₂Reverse, rho₂])
      · exact Or.inl (by
          rw [phi₂Aux_c, rho₂Reverse_a]
          simp [phi₂Aux, rho₂Reverse, rho₂])
  | cons_cons x y xs ih ih₁ =>
      rcases fin₂_cases x with rfl | rfl
      · rcases fin₂_cases y with rfl | rfl
        · rcases ih with h | h
          · exact Or.inl (by
              rw [phi₂Aux_dd, rho₂Reverse_e]
              exact congrArg ((0 : Fin 2) :: 0 :: ·) h)
          · exact Or.inr (by
              rw [phi₂Aux_dd, rho₂Reverse_e]
              simpa only [List.cons_append] using
                congrArg ((0 : Fin 2) :: 0 :: ·) h)
        · rcases ih with h | h
          · exact Or.inl (by
              rw [phi₂Aux_dc, rho₂Reverse_b]
              exact congrArg ((0 : Fin 2) :: 1 :: ·) h)
          · exact Or.inr (by
              rw [phi₂Aux_dc, rho₂Reverse_b]
              simpa only [List.cons_append] using
                congrArg ((0 : Fin 2) :: 1 :: ·) h)
      · have htail := ih₁ y
        rcases htail with h | h
        · exact Or.inl (by
            rw [phi₂Aux_c, rho₂Reverse_a]
            exact congrArg ((1 : Fin 2) :: ·) h)
        · exact Or.inr (by
            rw [phi₂Aux_c, rho₂Reverse_a]
            simpa only [List.cons_append] using congrArg ((1 : Fin 2) :: ·) h)

/-- Equivalently, every binary word is either exactly an encoded word or is
an encoded word preceded by the unmatched letter `d`. -/
theorem rho₂_phi₂_reconstruct (W : List (Fin 2)) :
    rho₂ (phi₂ W) = W ∨ (0 : Fin 2) :: rho₂ (phi₂ W) = W := by
  have h := phi₂Aux_reconstruct W.reverse
  rcases h with h | h
  · left
    have := congrArg List.reverse h
    simpa [phi₂, rho₂Reverse] using this.symm
  · right
    have := congrArg List.reverse h
    simpa [phi₂, rho₂Reverse] using this.symm

/-- The five left sides (20)--(24) of `T₂`. -/
def stage₂F (L : List A₂) : Fin 5 → List A₂ := ![
  [e, a, a],
  [e, a, b],
  [e, b, a],
  [e, b, b],
  L
]

/-- The five right sides (20)--(24) of `T₂`. -/
def stage₂E (M : List A₂) : Fin 5 → List A₂ := ![
  [a, e],
  [b, e],
  [a, e],
  [b, e],
  M
]

def stage₂System (L M : List A₂) : ThueSystem A₂ :=
  finiteSystem (stage₂F L) (stage₂E M)

end Matiyasevich1993

end Thue

end UniversalGroup
