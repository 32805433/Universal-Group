module

public import UniversalGroup.Coding.BooneCollins.Words
public import UniversalGroup.Coding.Thue.PriorityStage

@[expose] public section

/-!
# The right-to-left parser for Boone–Collins's final binary substitution

The parser is Matiyasevich's parser transported through the exchanges of the
intermediate and final letters. It leaves at most one unmatched initial `1`.
The residual context of a long relation changes its final `gamma` to `beta`;
this is handled separately from an aligned occurrence.
-/
namespace UniversalGroup.BooneCollinsDecoder
open BooneCollinsWords
open Thue.Matiyasevich1993

noncomputable section

def swapIntermediateLetter : Intermediate → Intermediate := ![1,0,2]
def swapIntermediate (W : IntermediateWord) : IntermediateWord := W.map swapIntermediateLetter
def swapFinalLetter : Fin 2 → Fin 2 := ![1,0]
def swapFinal (W : PositiveWord) : PositiveWord := W.map swapFinalLetter

@[simp] theorem swapIntermediateLetter_involutive (i : Intermediate) :
    swapIntermediateLetter (swapIntermediateLetter i) = i := by
  fin_cases i <;> rfl
@[simp] theorem swapFinalLetter_involutive (i : Fin 2) :
    swapFinalLetter (swapFinalLetter i) = i := by
  fin_cases i <;> rfl
@[simp] theorem swapIntermediate_involutive (W : IntermediateWord) :
    swapIntermediate (swapIntermediate W) = W := by
  simp [swapIntermediate, List.map_map, Function.comp_def]
@[simp] theorem swapFinal_involutive (W : PositiveWord) : swapFinal (swapFinal W) = W := by
  simp [swapFinal, List.map_map, Function.comp_def]
@[simp] theorem swapIntermediate_append (V W : IntermediateWord) :
    swapIntermediate (V ++ W) = swapIntermediate V ++ swapIntermediate W := by
  simp [swapIntermediate]
@[simp] theorem swapFinal_append (V W : PositiveWord) :
    swapFinal (V ++ W) = swapFinal V ++ swapFinal W := by simp [swapFinal]

theorem tau_eq (W : IntermediateWord) :
    tau W = swapFinal (rho₂ (swapIntermediate W)) := by
  induction W with
  | nil => rfl
  | cons i W ih =>
      fin_cases i <;> simpa [tau, tauLetter, swapFinal, swapFinalLetter, rho₂, rho₂Letter,
        swapIntermediate, swapIntermediateLetter] using ih

/-- Boone–Collins's inverse word parser, in the original letter convention. -/
def decode (W : PositiveWord) : IntermediateWord :=
  swapIntermediate (phi₂ (swapFinal W))

@[simp] theorem decode_tau (W : IntermediateWord) : decode (tau W) = W := by
  rw [decode, tau_eq, swapFinal_involutive, phi₂_rho₂, swapIntermediate_involutive]

theorem tau_decode_reconstruct (W : PositiveWord) :
    tau (decode W) = W ∨ (1 : Fin 2) :: tau (decode W) = W := by
  have h := rho₂_phi₂_reconstruct (swapFinal W)
  rcases h with h | h
  · left
    have he := congrArg swapFinal h
    simpa [tau_eq, decode] using he
  · right
    have he := congrArg swapFinal h
    rw [swapFinal_involutive] at he
    simpa [tau_eq, decode, swapFinal, swapFinalLetter] using he

@[simp] theorem decode_append_tau (V : PositiveWord) (W : IntermediateWord) :
    decode (V ++ tau W) = decode V ++ W := by
  rw [decode, swapFinal_append, tau_eq, swapFinal_involutive,
    phi₂_append_rho₂, swapIntermediate_append, swapIntermediate_involutive]
  rfl

theorem decode_context (V : PositiveWord) (W R : IntermediateWord) :
    decode (V ++ tau W ++ tau R) = decode V ++ W ++ R := by rw [decode_append_tau, decode_append_tau]

/-- Appending the residual final bit changes a terminal gamma to beta. -/
theorem tau_residual (W : IntermediateWord) :
    tau (W ++ [1]) ++ [1] = tau (W ++ [0]) := by
  simp [tau, tauLetter, List.append_assoc]

/-- The exact residual alignment appearing in Boone–Collins Lemma 2.16. -/
theorem decode_residual_context (V : PositiveWord) (W R : IntermediateWord) :
    decode (V ++ tau (W ++ [1]) ++ (1 : Fin 2) :: tau R) =
      decode V ++ (W ++ [0]) ++ R := by
  have he : V ++ tau (W ++ [1]) ++ (1 : Fin 2) :: tau R =
      V ++ tau (W ++ [0]) ++ tau R := by
    rw [← tau_residual]
    simp only [List.append_assoc, List.singleton_append]
  rw [he, decode_context]

open Thue.Matiyasevich1993.Priority

def shortLeft (i : Fin 2) : PositiveWord :=
  if i = 0 then [1,1,0,1,0] else [1,1,0,0]
def shortRight : PositiveWord := [0,1,1]

private theorem decode_residual_block (V block : PositiveWord) (R X : IntermediateWord)
    (hb : block ++ [1] = tau X) :
    decode (V ++ block ++ (1 : Fin 2) :: tau R) = decode V ++ X ++ R := by
  have he : V ++ block ++ (1 : Fin 2) :: tau R = V ++ tau X ++ tau R := by
    rw [← hb]
    simp only [List.append_assoc, List.singleton_append]
  rw [he, decode_context]

/-- Both alignments of either short final relation are housekeeping steps,
and therefore preserve the first priority normal form. -/
theorem decode_short_normal (i : Fin 2) (l r : PositiveWord) :
    firstNormal (decode (l ++ shortLeft i ++ r)) =
      firstNormal (decode (l ++ shortRight ++ r)) := by
  rcases tau_decode_reconstruct r with hr | hr
  · have hsmall : shortRight = tau [1,2] := rfl
    rw [← hr, hsmall]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one]
    · have hbig : shortLeft 0 = tau [2,0,1] := rfl
      rw [hbig, decode_context, decode_context]
      exact firstNormal_housekeeping (decode l) (decode r) 1
    · have hbig : shortLeft 1 = tau [2,1,1] := rfl
      rw [hbig, decode_context, decode_context]
      exact firstNormal_housekeeping (decode l) (decode r) 3
  · have hs := decode_residual_block l shortRight (decode r) [0,2] (by rfl)
    rw [hr] at hs
    rw [hs]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one]
    · have hb := decode_residual_block l (shortLeft 0) (decode r) [2,0,0] (by rfl)
      rw [hr] at hb
      rw [hb]
      exact firstNormal_housekeeping (decode l) (decode r) 0
    · have hb := decode_residual_block l (shortLeft 1) (decode r) [2,1,0] (by rfl)
      rw [hr] at hb
      rw [hb]
      exact firstNormal_housekeeping (decode l) (decode r) 2


/-- Parity of the initial run of final-alphabet `1` letters. -/
def initialParity : PositiveWord → Bool
  | [] => false
  | x::W => if x=0 then false else !(initialParity W)

@[simp] theorem initialParity_zero (W : PositiveWord) :
    initialParity (0::W) = false := by simp [initialParity]
@[simp] theorem initialParity_one (W : PositiveWord) :
    initialParity (1::W) = !(initialParity W) := by simp [initialParity]

@[simp] theorem initialParity_tau (W : IntermediateWord) :
    initialParity (tau W) = false := by
  induction W with
  | nil => rfl
  | cons i W ih =>
      fin_cases i <;> simp_all [tau,tauLetter,initialParity]

/-- Initial-run parity records exactly whether the right-to-left parser
leaves an unmatched initial bit. -/
theorem reconstruct_of_parity {W : PositiveWord}
    (h : initialParity W = false) : tau (decode W) = W := by
  rcases tau_decode_reconstruct W with he | he
  · exact he
  · have hp := congrArg initialParity he
    simp [h] at hp

theorem initialParity_prefix_congr (l : PositiveWord) {X Y : PositiveWord}
    (h : initialParity X = initialParity Y) :
    initialParity (l++X) = initialParity (l++Y) := by
  induction l with
  | nil => exact h
  | cons i l ih => simp [initialParity,ih]

@[simp] theorem initialParity_shortLeft (i : Fin 2) (r : PositiveWord) :
    initialParity (shortLeft i++r) = false := by
  fin_cases i <;> simp [shortLeft,initialParity]
@[simp] theorem initialParity_shortRight (r : PositiveWord) :
    initialParity (shortRight++r) = false := by rfl


end
end UniversalGroup.BooneCollinsDecoder
