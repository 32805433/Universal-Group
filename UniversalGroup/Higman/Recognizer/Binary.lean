module

public import UniversalGroup.Higman.Recognizer.MachineInput
public import UniversalGroup.Computability.Machine.SupportedTM1Thue

@[expose] public section

/-!
# Literal input encoding for the finite Thue machine

The machine input becomes a homomorphic binary-word substitution between
fixed boundary words. Reachability of the fixed target is equivalent to
halting of the partial-recursive program. `HigmanFiniteRecognizer` uses this
interface to recognize languages over arbitrary finite alphabets.
-/
namespace UniversalGroup.HigmanMachineThue
open Turing
open HigmanMachineInput
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

abbrev TapeSymbol := FixedMachine.TapeSymbol

def tapeSymbol (s : Symbol) : TapeSymbol :=
  (false, Function.update (fun _ : FixedMachine.Stack => none)
    PartrecToTM2.K'.main (some s))

def firstSymbol : TapeSymbol := (true, (tapeSymbol .cons).2)

theorem postInput_literal (w : List Bool) :
    FixedMachine.postInput (inputNat w.reverse) =
      [firstSymbol, tapeSymbol .bit1] ++
        w.map (fun b => tapeSymbol (bitSymbol b)) ++ [tapeSymbol .bit0] := by
  simp [FixedMachine.postInput, PartrecToTM2.trList, trNat_inputNat,
    TM2to1.trInit, tapeSymbol, firstSymbol, List.reverse_append,
    List.map_reverse, List.map_map, List.append_assoc]

def binaryCode : TM1BinaryAdapter.Code TapeSymbol :=
  TM1BinaryAdapter.canonicalCode TapeSymbol

noncomputable abbrev Alphabet (c : ToPartrec.Code) :=
  SupportedTM1Thue.Alphabet binaryCode FixedMachine.oneTapeProgram (FixedMachine.oneTapeSupport c)

noncomputable def postMachine (c : ToPartrec.Code) :
    PostMachine.Machine (TM0PostAdapter.Phase
      (SupportedTM1Thue.State binaryCode FixedMachine.oneTapeProgram
        (FixedMachine.oneTapeSupport c))) := by
  letI := FixedMachine.oneTapeStateInhabited c
  exact SupportedTM1Thue.postMachine binaryCode FixedMachine.oneTapeProgram
    (FixedMachine.oneTapeSupport c) (FixedMachine.oneTapeProgram_supports c)

def system (c : ToPartrec.Code) : ThueSystem (Alphabet c) :=
  PostMachine.system (postMachine c)

def start (c : ToPartrec.Code) (input : List TapeSymbol) : List (Alphabet c) := by
  letI := FixedMachine.oneTapeStateInhabited c
  exact SupportedTM1Thue.start binaryCode FixedMachine.oneTapeProgram
    (FixedMachine.oneTapeSupport c) (FixedMachine.oneTapeProgram_supports c) input

def target (c : ToPartrec.Code) : List (Alphabet c) := PostMachine.target

instance alphabetFinite (c : ToPartrec.Code) : Finite (Alphabet c) := inferInstance

theorem system_finite (c : ToPartrec.Code) : (system c).Finite := by
  let := FixedMachine.oneTapeStateInhabited c
  exact SupportedTM1Thue.system_finite binaryCode FixedMachine.oneTapeProgram
    (FixedMachine.oneTapeSupport c) (FixedMachine.oneTapeProgram_supports c)

theorem recognizes (c : ToPartrec.Code) (w : List Bool) :
    ThueEq (system c) (start c (FixedMachine.postInput (inputNat w.reverse))) (target c) ↔
      (c.eval [inputNat w.reverse]).Dom := by
  let := FixedMachine.stateInhabited c
  let := FixedMachine.oneTapeStateInhabited c
  have h := SupportedTM1Thue.thue_iff_eval_dom binaryCode FixedMachine.oneTapeProgram
    (FixedMachine.oneTapeSupport c) (FixedMachine.oneTapeProgram_supports c)
    (FixedMachine.postInput (inputNat w.reverse))
  refine h.trans ?_
  exact (TM2to1.tr_eval_dom PartrecToTM2.tr PartrecToTM2.K'.main
    (PartrecToTM2.trList [inputNat w.reverse])).trans
    (FixedMachine.tm2_eval_dom_iff c (inputNat w.reverse))

def prefixBytes : List Bool :=
  TM1BinaryAdapter.encodeInput binaryCode [firstSymbol, tapeSymbol .bit1]

def letterBytes (b : Bool) : List Bool :=
  (binaryCode.enc (tapeSymbol (bitSymbol b))).toList

def suffixBytes : List Bool := (binaryCode.enc (tapeSymbol .bit0)).toList

theorem binaryCode_width_pos : 0 < binaryCode.width := by
  by_contra h
  have hz : binaryCode.width = 0 := by omega
  have he : binaryCode.enc firstSymbol = binaryCode.enc (tapeSymbol .bit0) := by
    apply Subtype.ext
    have h₁ := (binaryCode.enc firstSymbol).2
    have h₂ := (binaryCode.enc (tapeSymbol .bit0)).2
    exact (List.length_eq_zero_iff.mp (h₁.trans hz)).trans
      (List.length_eq_zero_iff.mp (h₂.trans hz)).symm
  have hh := congrArg binaryCode.dec he
  rw [binaryCode.dec_enc, binaryCode.dec_enc] at hh
  have := congrArg Prod.fst hh
  contradiction

theorem prefixBytes_ne_nil : prefixBytes ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp [prefixBytes, TM1BinaryAdapter.encodeInput] at hl
  have := binaryCode_width_pos
  omega

def leftBoundary (c : ToPartrec.Code) : List (Alphabet c) := by
  letI := FixedMachine.oneTapeStateInhabited c
  letI := TM1BinaryAdapter.finiteStateInhabited binaryCode FixedMachine.oneTapeProgram
    (FixedMachine.oneTapeSupport c) (FixedMachine.oneTapeProgram_supports c)
  exact [PostMachine.Symbol.leftMarker, PostMachine.Symbol.tape prefixBytes.headI,
    PostMachine.Symbol.state (TM0PostAdapter.Phase.normal default)] ++
    prefixBytes.tail.map PostMachine.Symbol.tape

def letter (c : ToPartrec.Code) (b : Bool) : List (Alphabet c) :=
  (letterBytes b).map PostMachine.Symbol.tape

def suffix (c : ToPartrec.Code) : List (Alphabet c) :=
  suffixBytes.map PostMachine.Symbol.tape ++ [PostMachine.Symbol.rightMarker]

theorem start_literal (c : ToPartrec.Code) (w : List Bool) :
    start c (FixedMachine.postInput (inputNat w.reverse)) =
      leftBoundary c ++ w.flatMap (letter c) ++ suffix c := by
  rw [postInput_literal]
  let := FixedMachine.oneTapeStateInhabited c
  let := TM1BinaryAdapter.finiteStateInhabited binaryCode FixedMachine.oneTapeProgram
    (FixedMachine.oneTapeSupport c) (FixedMachine.oneTapeProgram_supports c)
  have he : TM1BinaryAdapter.encodeInput binaryCode
      ([firstSymbol, tapeSymbol .bit1] ++ w.map (fun b => tapeSymbol (bitSymbol b)) ++
        [tapeSymbol .bit0]) = prefixBytes ++ w.flatMap letterBytes ++ suffixBytes := by
    simp [prefixBytes, suffixBytes, TM1BinaryAdapter.encodeInput, List.flatMap_map]
    rfl
  unfold start SupportedTM1Thue.start
  rw [he]
  cases hp : prefixBytes with
  | nil => exact (prefixBytes_ne_nil hp).elim
  | cons b bs =>
    simp [TM0PostAdapter.init, PostMachine.encode, PostMachine.encodeTape,
      leftBoundary, suffix, hp, List.map_flatMap, List.append_assoc]
    rfl

end
end UniversalGroup.HigmanMachineThue
