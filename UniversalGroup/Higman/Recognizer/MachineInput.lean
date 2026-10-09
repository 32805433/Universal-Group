module

public import UniversalGroup.Computability.Machine.PartialRecursiveMachine
public import Mathlib.Computability.RE

@[expose] public section

/-! Literal binary word inputs for the verified partial-recursive-to-machine compiler.
The two sentinels make the machine input an ordinary letter substitution with
fixed prefix and suffix. No assertion about contextual Thue recognition is used. -/
namespace UniversalGroup.HigmanMachineInput
open Turing
set_option maxHeartbeats 800000

abbrev Symbol := PartrecToTM2.Γ'

def bitSymbol (b : Bool) : Symbol :=
  if b then .bit1 else .bit0

def wordNat : List Bool → ℕ
  | [] => 1
  | b :: w => Nat.bit b (wordNat w)

def inputNat (w : List Bool) : ℕ := Nat.bit false (wordNat w)

theorem wordNat_pos (w : List Bool) : 0 < wordNat w := by
  induction w with
  | nil => decide
  | cons b w ih => cases b <;> simp_all [wordNat, Nat.bit]

private theorem trNum_bit (b : Bool) (n : Num)
    (h : b = true ∨ n ≠ 0) :
    PartrecToTM2.trNum (Num.bit b n) =
      bitSymbol b :: PartrecToTM2.trNum n := by
  cases b
  · simp only [Bool.false_eq_true, false_or] at h
    cases n with
    | zero => exact (h rfl).elim
    | pos p => rfl
  · cases n <;> rfl

private theorem trNat_bit (b : Bool) (n : ℕ) (hn : n ≠ 0) :
    PartrecToTM2.trNat (Nat.bit b n) =
      bitSymbol b :: PartrecToTM2.trNat n := by
  unfold PartrecToTM2.trNat
  change PartrecToTM2.trNum (Num.ofNat' (Nat.bit b n)) = _
  rw [Num.ofNat'_bit]
  apply trNum_bit
  right
  intro h
  apply hn
  simpa using congrArg (fun x : Num => (x : ℕ)) h

theorem trNat_wordNat (w : List Bool) :
    PartrecToTM2.trNat (wordNat w) = w.map bitSymbol ++ [.bit1] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      rw [wordNat, trNat_bit b _ (Nat.ne_of_gt (wordNat_pos w)), ih]
      rfl

theorem trNat_inputNat (w : List Bool) :
    PartrecToTM2.trNat (inputNat w) = [.bit0] ++ w.map bitSymbol ++ [.bit1] := by
  rw [inputNat, trNat_bit false _ (Nat.ne_of_gt (wordNat_pos w)), trNat_wordNat]
  rfl

def symbolBit (s : Symbol) : Bool := s == .bit1

def decode (n : ℕ) : List Bool :=
  let letters := (PartrecToTM2.trNat n).drop 1
  (letters.take (letters.length - 1)).map symbolBit

@[simp] theorem symbolBit_bitSymbol (b : Bool) : symbolBit (bitSymbol b) = b := by
  cases b <;> rfl

@[simp] theorem decode_inputNat (w : List Bool) : decode (inputNat w) = w := by
  simp [decode, trNat_inputNat, List.map_map, Function.comp_def]

theorem decode_computable : Computable decode := by
  have hd : Computable (fun n => (PartrecToTM2.trNat n).drop 1) :=
    Primrec.list_drop.to_comp.comp (Computable.const 1) FixedMachine.trNat_computable
  have ht : Computable (fun n => ((PartrecToTM2.trNat n).drop 1).take
      (((PartrecToTM2.trNat n).drop 1).length - 1)) :=
    Primrec.list_take.to_comp.comp
      (Primrec.nat_sub.to_comp.comp (Primrec.list_length.to_comp.comp hd) (Computable.const 1)) hd
  exact (Primrec.list_map Primrec.id
    ((Primrec.dom_finite symbolBit).comp₂ Primrec₂.right)).to_comp.comp ht

/-- Every recursively enumerable binary-word language is recognized by a
compiled program on a literal, homomorphically encoded input. -/
theorem exists_code {language : List Bool → Prop} (hlanguage : REPred language) :
    ∃ c : ToPartrec.Code, ∀ w,
      (c.eval [inputNat w]).Dom ↔ language w := by
  have hf : Partrec (fun n => (Part.assert (language (decode n))
      (fun _ => Part.some (0 : ℕ)))) := by
    exact ((hlanguage.comp decode_computable).map (Computable.const (0 : ℕ)).to₂).of_eq
      (fun n => by apply Part.ext; intro x; simp [eq_comm])
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  refine ⟨c, fun w => ?_⟩
  have he := hc (inputNat w ::ᵥ List.Vector.nil)
  have hd := congrArg Part.Dom he
  change (c.eval [inputNat w]).Dom =
    (Part.assert (language (decode (inputNat w))) (fun _ => Part.some (0 : ℕ))).Dom at hd
  rw [decode_inputNat] at hd
  exact (Iff.of_eq hd).trans (by simp [Part.assert])

end UniversalGroup.HigmanMachineInput
