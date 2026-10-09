module

public import UniversalGroup.Higman.Recognizer.Binary
public import UniversalGroup.Computability.Enumerable

@[expose] public section

/-! Arbitrary finite input alphabets for literal finite Thue recognition. -/
namespace UniversalGroup.HigmanFiniteRecognizer
open HigmanMachineThue
noncomputable section
set_option maxHeartbeats 1000000

/-- A positive-length, injective block code, including the empty input alphabet. -/
def bitBlock (k : ℕ) (i : Fin k) : List Bool :=
  List.ofFn (fun j : Fin (k+1) => decide (j.val=i.val))

def binaryWord (k : ℕ) (w : List (Fin k)) : List Bool := w.flatMap (bitBlock k)

@[simp] theorem bitBlock_length (k : ℕ) (i : Fin k) : (bitBlock k i).length=k+1 := by
  simp [bitBlock]

theorem bitBlock_ne_nil (k : ℕ) (i : Fin k) : bitBlock k i ≠ [] := by
  intro h
  have hh := congrArg List.length h
  simp at hh

theorem bitBlock_injective (k : ℕ) : Function.Injective (bitBlock k) := by
  intro i j h
  have hi : i.val < k+1 := by omega
  have hh := congrArg (fun w : List Bool => w[i.val]?) h
  unfold bitBlock at hh
  rw [List.getElem?_ofFn, List.getElem?_ofFn] at hh
  simp only [dite_eq_left hi, decide_true, Option.some.injEq, true_eq_decide_iff] at hh
  exact Fin.ext hh

theorem binaryWord_injective (k : ℕ) : Function.Injective (binaryWord k) := by
  intro u v h
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => rfl
      | cons a v =>
          have hh : bitBlock k a = [] := (List.append_eq_nil_iff.mp h.symm).1
          exact (bitBlock_ne_nil k a hh).elim
  | cons a u ih =>
      cases v with
      | nil =>
          have hh : bitBlock k a = [] := (List.append_eq_nil_iff.mp h).1
          exact (bitBlock_ne_nil k a hh).elim
      | cons b v =>
          change bitBlock k a ++ binaryWord k u = bitBlock k b ++ binaryWord k v at h
          have hl : (bitBlock k a).length = (bitBlock k b).length := by simp
          have hab := bitBlock_injective k (List.append_inj_left h hl)
          have huv := ih (List.append_inj_right h hl)
          exact congrArg₂ List.cons hab huv

theorem binaryWord_primrec (k : ℕ) : Primrec (binaryWord k) :=
  Primrec.list_flatMap Primrec.id ((Primrec.dom_finite (bitBlock k)).comp₂ Primrec₂.right)

def binaryLanguage {k : ℕ} (language : List (Fin k) → Prop) (w : List Bool) : Prop :=
  ∃ v, language v ∧ binaryWord k v=w

theorem binaryLanguage_re {k : ℕ} {language : List (Fin k) → Prop}
    (hL : REPred language) : REPred (binaryLanguage language) := by
  have he : PrimrecPred (fun p : List Bool × List (Fin k) => binaryWord k p.2=p.1) :=
    Primrec.eq.comp ((binaryWord_primrec k).comp Primrec.snd) Primrec.fst
  exact RecursiveEnumerable.exists_re
    (RecursiveEnumerable.and (RecursiveEnumerable.comp hL Computable.snd) he.computablePred.to_re)

@[simp] theorem binaryLanguage_encoded {k : ℕ} (language : List (Fin k) → Prop)
    (w : List (Fin k)) : binaryLanguage language (binaryWord k w) ↔ language w := by
  constructor
  · rintro ⟨v,hv,he⟩
    exact binaryWord_injective k he ▸ hv
  · exact fun h => ⟨w,h,rfl⟩

/-- A finite fixed-boundary recognizer, including the nonempty words needed
by the binary triangularization. -/
structure Data (k : ℕ) (language : List (Fin k) → Prop) where
  Alphabet : Type
  finiteAlphabet : Finite Alphabet
  rules : ThueSystem Alphabet
  finiteRules : rules.Finite
  nonemptyRules : ∀ p ∈ rules, p.1 ≠ [] ∧ p.2 ≠ []
  left : List Alphabet
  right : List Alphabet
  target : List Alphabet
  code : Fin k → List Alphabet
  left_nonempty : left ≠ []
  right_nonempty : right ≠ []
  code_nonempty : ∀ i, code i ≠ []
  recognizes : ∀ w, language w ↔ ThueEq rules (left ++ w.flatMap code ++ right) target

theorem system_nonempty (c : Turing.ToPartrec.Code) :
    ∀ p ∈ system c, p.1 ≠ [] ∧ p.2 ≠ [] := by
  rintro ⟨x,y⟩ h
  change PostMachine.Rule (postMachine c) x y at h
  cases h <;> simp

theorem letter_nonempty (c : Turing.ToPartrec.Code) (b : Bool) : letter c b ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [letter, letterBytes, List.length_map, List.Vector.toList_length, List.length_nil] at hl
  have hp := binaryCode_width_pos
  omega

/-- Every recursively enumerable language over a finite alphabet admits a
finite Thue recognizer with literal substitution and fixed boundaries. -/
theorem exists_data {k : ℕ} {language : List (Fin k) → Prop} (hL : REPred language) :
    Nonempty (Data k language) := by
  have hr : REPred (fun w : List Bool => binaryLanguage language w.reverse) :=
    (binaryLanguage_re hL).comp Computable.list_reverse
  obtain ⟨c,hc⟩ := HigmanMachineInput.exists_code hr
  let code : Fin k → List (Alphabet c) := fun i => (bitBlock k i).flatMap (letter c)
  refine ⟨{
    Alphabet := Alphabet c
    finiteAlphabet := inferInstance
    rules := system c
    finiteRules := system_finite c
    nonemptyRules := system_nonempty c
    left := leftBoundary c
    right := suffix c
    target := target c
    code := code
    left_nonempty := by simp [leftBoundary]
    right_nonempty := by simp [suffix]
    code_nonempty := ?_
    recognizes := ?_
  }⟩
  · intro i hi
    have hh := List.flatMap_eq_nil_iff.mp hi
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil (bitBlock k i) (bitBlock_ne_nil k i)
    exact letter_nonempty c b (hh b hb)
  · intro w
    have hh := recognizes c (binaryWord k w)
    rw [start_literal, hc] at hh
    simp only [List.reverse_reverse, binaryLanguage_encoded] at hh
    simpa only [binaryWord, List.flatMap_assoc, code] using hh.symm

end
end UniversalGroup.HigmanFiniteRecognizer
