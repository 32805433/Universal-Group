module

public import Mathlib.Computability.TuringMachine.ToPartrec

@[expose] public section

/-!
# Partial-recursive programs as finitely supported one-tape machines

Mathlib compiles each list-oriented partial-recursive code through its
four-stack machine to a one-tape machine. We expose the initial input,
finite state support, and halting-domain equivalence used by the Thue
recognizer. The numeric input serialization is computable.
-/

namespace UniversalGroup

open Turing
open Encodable Denumerable

namespace FixedMachine

abbrev State := PartrecToTM2.Λ'
abbrev Symbol := PartrecToTM2.Γ'
abbrev Stack := PartrecToTM2.K'

set_option backward.isDefEq.respectTransparency.types false in
deriving instance Fintype for PartrecToTM2.K'

noncomputable instance symbolPrimcodable : Primcodable Symbol :=
  Primcodable.ofEquiv (Fin (Fintype.card Symbol)) (Fintype.equivFin Symbol)

/-- With the initial-state instance specialized to the program `c`, Mathlib's
standard `TM2.init` is definitionally the configuration used by the verified
partial-recursive-to-machine compiler. -/
theorem tm2_eval_dom_iff (c : ToPartrec.Code) (n : ℕ) :
    letI : Inhabited State :=
      ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
    (TM2.eval PartrecToTM2.tr PartrecToTM2.K'.main
      (PartrecToTM2.trList [n])).Dom ↔
      (c.eval [n]).Dom := by
  let : Inhabited State :=
    ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  have hinit :
      TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList [n]) =
        PartrecToTM2.init c [n] := by
    unfold TM2.init PartrecToTM2.init
    congr 1
    funext k
    cases k <;> rfl
  unfold TM2.eval
  rw [hinit, PartrecToTM2.tr_eval]
  rfl

/-! The verified Mathlib compiler turns the four-stack machine into a
deterministic one-tape machine. Its finite support is restricted before the
subsequent binary and Post-machine translations. -/

abbrev TapeSymbol :=
  TM2to1.Γ' Stack (fun _ : Stack => Symbol)

abbrev OneTapeState :=
  TM2to1.Λ' Stack (fun _ : Stack => Symbol) State (Option Symbol)

def oneTapeProgram :
    OneTapeState → TM1.Stmt TapeSymbol OneTapeState (Option Symbol) :=
  TM2to1.tr PartrecToTM2.tr

@[reducible] def stateInhabited (c : ToPartrec.Code) : Inhabited State :=
  ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩

@[reducible] def oneTapeStateInhabited (c : ToPartrec.Code) : Inhabited OneTapeState :=
  @TM2to1.Λ'.inhabited Stack (fun _ : Stack => Symbol) State
    (Option Symbol) (stateInhabited c)

/-- Initial one-tape input obtained from the singleton numeric argument. -/
def postInput (n : ℕ) : List TapeSymbol :=
  TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [n])

private theorem trNum_bit (b : Bool) (n : Num)
    (h : b = true ∨ n ≠ 0) :
    PartrecToTM2.trNum (Num.bit b n) =
      (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0) ::
        PartrecToTM2.trNum n := by
  cases b
  · simp only [Bool.false_eq_true, false_or] at h
    cases n with
    | zero => exact (h rfl).elim
    | pos p => rfl
  · cases n <;> rfl

private theorem trNat_bit (b : Bool) (n : ℕ)
    (h : b = true ∨ n ≠ 0) :
    PartrecToTM2.trNat (Nat.bit b n) =
      (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0) ::
        PartrecToTM2.trNat n := by
  unfold PartrecToTM2.trNat
  change PartrecToTM2.trNum (Num.ofNat' (Nat.bit b n)) =
    _ :: PartrecToTM2.trNum (Num.ofNat' n)
  rw [Num.ofNat'_bit]
  exact trNum_bit b n <| h.imp_right fun hn hcast => hn <| by
    simpa using congrArg (fun x : Num => (x : ℕ)) hcast

theorem trNat_computable : Computable PartrecToTM2.trNat := by
  let g : Unit → List (List Symbol) → Option (List Symbol) := fun _ ih =>
    ih.length.casesOn (some []) fun k =>
      some ((if (k + 1).bodd then PartrecToTM2.Γ'.bit1
        else PartrecToTM2.Γ'.bit0) :: ih.getI (k + 1).div2)
  have hsym : Computable₂ fun (_ : Unit × List (List Symbol)) (k : ℕ) =>
      if (k + 1).bodd then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0 := by
    unfold Computable₂
    exact (Computable.cond
      (Computable.nat_bodd.comp (Computable.succ.comp
        (Computable.snd : Computable (fun p :
          (Unit × List (List Symbol)) × ℕ => p.2))))
      (Computable.const PartrecToTM2.Γ'.bit1)
      (Computable.const PartrecToTM2.Γ'.bit0)).of_eq fun p => by
        simp only [Nat.add_one, Nat.bodd_succ]
        cases p.2.bodd <;> rfl
  have hget : Computable₂ fun (p : Unit × List (List Symbol)) (k : ℕ) =>
      p.2.getI (k + 1).div2 :=
    (Primrec.list_getI.to_comp.comp
      (Computable.snd.comp Computable.fst)
      (Computable.nat_div2.comp (Computable.succ.comp Computable.snd))).to₂
  have htail : Computable₂ fun (p : Unit × List (List Symbol)) (k : ℕ) =>
      some ((if (k + 1).bodd then PartrecToTM2.Γ'.bit1
        else PartrecToTM2.Γ'.bit0) ::
          p.2.getI (k + 1).div2) :=
    Computable.option_some.comp₂ (Computable.list_cons.comp₂ hsym hget)
  have hg : Computable₂ g := by
    unfold Computable₂
    dsimp only [g]
    apply Computable.nat_casesOn
    · exact Computable.list_length.comp Computable.snd
    · exact Computable.const (some [])
    · exact htail
  have hrec := Computable.nat_strong_rec
    (fun _ n => PartrecToTM2.trNat n) hg
  have hspec : ∀ (_ : Unit) n,
      g Unit.unit ((List.range n).map PartrecToTM2.trNat) =
        some (PartrecToTM2.trNat n) := by
    intro _ n
    cases n with
    | zero => simp [g, PartrecToTM2.trNat_zero]
    | succ n =>
      have hlt : (n + 1).div2 < n + 1 :=
        Nat.div_lt_self (by omega) (by decide)
      have hb : (n + 1).bodd = true ∨ (n + 1).div2 ≠ 0 := by
        by_cases hzero : (n + 1).div2 = 0
        · left
          have hn : n = 0 := by
            rw [Nat.div2_val] at hzero
            omega
          subst n
          rfl
        · exact Or.inr hzero
      simp only [g, List.length_map, List.length_range]
      rw [List.getI_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hlt]
      simp only [Option.map_some, Option.getD_some]
      rw [← trNat_bit (n + 1).bodd (n + 1).div2 hb,
        Nat.bit_bodd_div2]
  exact (hrec hspec).comp (Computable.const Unit.unit) Computable.id

/-- The explicit finite support of the intermediate deterministic one-tape
machine.  This is exposed for bridges that operate at the `TM1` level. -/
noncomputable def oneTapeSupport (c : ToPartrec.Code) : Finset OneTapeState :=
  letI : Inhabited State := stateInhabited c
  TM2to1.trSupp PartrecToTM2.tr <|
    PartrecToTM2.codeSupp c PartrecToTM2.Cont'.halt

theorem oneTapeProgram_supports (c : ToPartrec.Code) :
    @TM1.Supports TapeSymbol OneTapeState (Option Symbol)
      (oneTapeStateInhabited c) oneTapeProgram (oneTapeSupport c) := by
  let : Inhabited State := stateInhabited c
  let : Inhabited OneTapeState := oneTapeStateInhabited c
  apply TM2to1.tr_supports
  exact PartrecToTM2.tr_supports c PartrecToTM2.Cont'.halt

end FixedMachine

end UniversalGroup
