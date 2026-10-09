module

public import UniversalGroup.Coding.BooneCollins.Long
public import UniversalGroup.Coding.BooneCollins.Forward

@[expose] public section

namespace UniversalGroup.BooneCollinsTheorem
open Thue Thue.Matiyasevich1993 Thue.Matiyasevich1993.Priority
open BooneCollinsWords BooneCollinsDecoder BooneCollinsNormalForm BooneCollinsCompiler
open BooneCollinsLong

set_option maxHeartbeats 1200000

def longSide {N s : ℕ} (p : ℕ) (F : Fin s→List (Fin N)) : IntermediateWord :=
  liftBinary (Priority.transpose p (fun j=>Binary.rho₁ N (F j)))

private theorem width_ge_three {N u p : ℕ} (F : Fin (2^u)→List (Fin N))
    (hF : ∀j,F j≠[]) (hp : ∀j,(Binary.rho₁ N (F j)).length=p) : 3≤p := by
  let j : Fin (2^u) := ⟨0,pow_pos (by omega) u⟩
  have hj : 1≤(F j).length := List.length_pos_iff.mpr (hF j)
  have hlen : p=(F j).length*(N+4) := by rw [←hp j,Binary.rho₁_length]
  rw [hlen]
  calc
    3≤1*(N+4) := by omega
    _≤(F j).length*(N+4) := Nat.mul_le_mul_right _ hj

private theorem source_row {N s : ℕ} (F E : Fin s→List (Fin N)) (j : Fin s) :
    ThueStep (finiteSystem F E) (F j) (E j) :=
  ⟨[],[],F j,E j,⟨j,rfl⟩,Or.inl ⟨by simp,by simp⟩⟩

private theorem replacements {N u p q : ℕ} (F E : Fin (2^u)→List (Fin N))
    (hF : ∀j,F j≠[]) (hE : ∀j,E j≠[])
    (hp : ∀j,(Binary.rho₁ N (F j)).length=p)
    (hq : ∀j,(Binary.rho₁ N (E j)).length=q) :
    LongReplacement u (finiteSystem F E) (longSide p F) (longSide q E) ∧
    LongReplacement u (finiteSystem F E) (longSide q E) (longSide p F) := by
  exact ⟨encoded_long_replacement _ F E hF hE hp hq
      (width_ge_three F hF hp) (width_ge_three E hE hq) (source_row F E),
    encoded_long_replacement _ E F hE hF hq hp
      (width_ge_three E hE hq) (width_ge_three F hF hp)
      (fun j=>thueStep_symm (source_row F E j))⟩

private theorem longSide_parity {N u p : ℕ} (F : Fin (2^u)→List (Fin N))
    (hF : ∀j,F j≠[]) (hp : ∀j,(Binary.rho₁ N (F j)).length=p)
    (r : PositiveWord) : initialParity (tau (longSide p F)++r)=false :=
  long_initialParity _ (pow_pos (by omega) u)
    (by have := width_ge_three F hF hp; omega)
    (fun j=>Binary.rho₁_starts_aa (hF j)) r

/-- A rectangular finite Thue system embeds in the exact binary three-rule
system, with the terminal gamma used by Boone–Collins. -/
theorem rectangular_equivalence {N u p q : ℕ}
    (F E : Fin (2^u)→List (Fin N))
    (hF : ∀j,F j≠[]) (hE : ∀j,E j≠[])
    (hp : ∀j,(Binary.rho₁ N (F j)).length=p)
    (hq : ∀j,(Binary.rho₁ N (E j)).length=q) (X Y : List (Fin N)) :
    ThueEq (finiteSystem F E) X Y ↔
      ThueEq (finalSystem (longSide p F) (longSide q E))
        (finalEndpoint N u X) (finalEndpoint N u Y) := by
  constructor
  · exact BooneCollinsForward.forward F E hF hE hp hq
  · obtain ⟨hLM,hML⟩ := replacements F E hF hE hp hq
    exact reflect_endpoints hLM hML (longSide_parity F hF hp) (longSide_parity E hE hq)

/-- Prefix reflection for arbitrary final words, not merely encoded words. -/
theorem rectangular_prefix {N u p q : ℕ}
    (F E : Fin (2^u)→List (Fin N))
    (hF : ∀j,F j≠[]) (hE : ∀j,E j≠[])
    (hp : ∀j,(Binary.rho₁ N (F j)).length=p)
    (hq : ∀j,(Binary.rho₁ N (E j)).length=q) (marker : Fin N)
    {Z : PositiveWord}
    (h : ThueEq (finalSystem (longSide p F) (longSide q E))
      (Z++finalEndpoint N u [marker]) (finalEndpoint N u [marker])) :
    ∃v,Z=chi N v ∧ ThueEq (finiteSystem F E) (v++[marker]) [marker] := by
  obtain ⟨hLM,hML⟩ := replacements F E hF hE hp hq
  exact reflect_prefix hLM hML (longSide_parity F hF hp)
    (longSide_parity E hE hq) marker h

/-- The source singleton/pair presentation used in the literal compiler. -/
def sourceSystem (r t : ℕ) (lhs : Fin (2^t)→Fin r)
    (rhs : Fin (2^t)→Fin r×Fin r) : ThueSystem (Fin r) :=
  finiteSystem (fun i=>[lhs i]) (fun i=>[(rhs i).1,(rhs i).2])

private theorem literal_left_eq (r t : ℕ) (lhs : Fin (2^t)→Fin r) :
    longLeft r t lhs=longSide (r+4) (fun i=>[lhs i]) := by
  simpa [longSide,Binary.rho₁] using BooneCollinsTranspose.longLeft_eq r t lhs

private theorem literal_right_eq (r t : ℕ) (rhs : Fin (2^t)→Fin r×Fin r) :
    longRight r t rhs=longSide (2*(r+4)) (fun i=>[(rhs i).1,(rhs i).2]) := by
  simpa [longSide,Binary.rho₁] using BooneCollinsTranspose.longRight_eq r t rhs

/-- Boone–Collins's three-rule compiler for the displayed literal words. -/
theorem literal_equivalence (r t : ℕ) (lhs : Fin (2^t)→Fin r)
    (rhs : Fin (2^t)→Fin r×Fin r) (X Y : List (Fin r)) :
    ThueEq (sourceSystem r t lhs rhs) X Y ↔
      ThueEq (finalSystem (longLeft r t lhs) (longRight r t rhs))
        (finalEndpoint r t X) (finalEndpoint r t Y) := by
  rw [literal_left_eq,literal_right_eq]
  exact rectangular_equivalence (fun i=>[lhs i]) (fun i=>[(rhs i).1,(rhs i).2])
    (by simp) (by simp) (by simp) (by simp [two_mul]) X Y

/-- The arbitrary-prefix strengthening needed for Valiev's marker. -/
theorem literal_prefix (r t : ℕ) (lhs : Fin (2^t)→Fin r)
    (rhs : Fin (2^t)→Fin r×Fin r) (marker : Fin r) {Z : PositiveWord}
    (h : ThueEq (finalSystem (longLeft r t lhs) (longRight r t rhs))
      (Z++finalEndpoint r t [marker]) (finalEndpoint r t [marker])) :
    ∃v,Z=chi r v ∧ ThueEq (sourceSystem r t lhs rhs) (v++[marker]) [marker] := by
  rw [literal_left_eq,literal_right_eq] at h
  exact rectangular_prefix (fun i=>[lhs i]) (fun i=>[(rhs i).1,(rhs i).2])
    (by simp) (by simp) (by simp) (by simp [two_mul]) marker h

end UniversalGroup.BooneCollinsTheorem
