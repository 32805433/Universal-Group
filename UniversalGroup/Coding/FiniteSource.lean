module

public import UniversalGroup.Coding.Triangular
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

/-! A finite, numerically indexed triangular source with the two input letters
numbered 0 and 1 and the marker numbered 2. -/
namespace UniversalGroup.Coding.FiniteSource
open Thue
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable (G : PreparedInput)

def alphabetSize : ℕ := 3 + Fintype.card (Triangular.Extra G)
def relationCount : ℕ := Fintype.card (Triangular.RuleIndex G)
theorem alphabetSize_ge_three : 3 ≤ alphabetSize G := by simp [alphabetSize]
theorem relationCount_pos : 0 < relationCount G := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨Sum.inr (0,true)⟩

def alphabetEquiv : Triangular.Alphabet G ≃ Fin (alphabetSize G) :=
  (Equiv.sumCongr (Equiv.refl (Fin 3)) (Fintype.equivFin (Triangular.Extra G))).trans finSumFinEquiv

def indexEquiv : Triangular.RuleIndex G ≃ Fin (relationCount G) := Fintype.equivFin _
def inputLetter (i : Fin 2) : Fin (alphabetSize G) := Fin.castLE (by dsimp [alphabetSize]; omega) i
def marker : Fin (alphabetSize G) := ⟨2,by dsimp [alphabetSize]; omega⟩
def inputWord (w : PositiveWord) : List (Fin (alphabetSize G)) := w.map (inputLetter G)

@[simp] theorem alphabetEquiv_letter (i : Fin 2) :
    alphabetEquiv G (Triangular.letter G i) = inputLetter G i := by
  apply Fin.ext
  rfl
@[simp] theorem alphabetEquiv_marker :
    alphabetEquiv G (Triangular.marker G) = marker G := by
  apply Fin.ext
  rfl
@[simp] theorem alphabetEquiv_lift (w : PositiveWord) :
    (Triangular.lift G w).map (alphabetEquiv G) = inputWord G w := by
  simp [Triangular.lift,inputWord,List.map_map,Function.comp_def]

def lhs (i : Fin (relationCount G)) : Fin (alphabetSize G) :=
  alphabetEquiv G (Triangular.lhs G ((indexEquiv G).symm i))
def rhs (i : Fin (relationCount G)) : Fin (alphabetSize G) × Fin (alphabetSize G) :=
  ((alphabetEquiv G) (Triangular.rhs G ((indexEquiv G).symm i)).1,
   (alphabetEquiv G) (Triangular.rhs G ((indexEquiv G).symm i)).2)
def rules : ThueSystem (Fin (alphabetSize G)) :=
  Set.range fun i => ([lhs G i],[(rhs G i).1,(rhs G i).2])

theorem forward {X Y : List (Triangular.Alphabet G)} (h : ThueEq (Triangular.rules G) X Y) :
    ThueEq (rules G) (X.map (alphabetEquiv G)) (Y.map (alphabetEquiv G)) := by
  have hm : ∀ x y, (x,y) ∈ Triangular.rules G →
      ThueEq (rules G) (x.flatMap (fun a => [alphabetEquiv G a]))
        (y.flatMap (fun a => [alphabetEquiv G a])) := by
    rintro x y ⟨i,hi⟩
    rcases Prod.mk.inj hi with ⟨rfl,rfl⟩
    apply SourceMarker.relation_eq
    refine ⟨indexEquiv G i,?_⟩
    simp [lhs,rhs]
  simpa only [← List.map_eq_flatMap] using SourceMarker.substitute_eq _ hm h

theorem reflection {X Y : List (Fin (alphabetSize G))} (h : ThueEq (rules G) X Y) :
    ThueEq (Triangular.rules G) (X.map (alphabetEquiv G).symm) (Y.map (alphabetEquiv G).symm) := by
  have hm : ∀ x y, (x,y) ∈ rules G →
      ThueEq (Triangular.rules G) (x.flatMap (fun a => [(alphabetEquiv G).symm a]))
        (y.flatMap (fun a => [(alphabetEquiv G).symm a])) := by
    rintro x y ⟨i,hi⟩
    rcases Prod.mk.inj hi with ⟨rfl,rfl⟩
    apply SourceMarker.relation_eq
    refine ⟨(indexEquiv G).symm i,?_⟩
    simp [lhs,rhs]
  simpa only [← List.map_eq_flatMap] using SourceMarker.substitute_eq _ hm h

theorem map_eq_iff (X Y : List (Triangular.Alphabet G)) :
    ThueEq (Triangular.rules G) X Y ↔
      ThueEq (rules G) (X.map (alphabetEquiv G)) (Y.map (alphabetEquiv G)) := by
  constructor
  · exact forward G
  · intro h
    simpa [List.map_map,Function.comp_def] using reflection G h

theorem recognizes (w : PositiveWord) :
    PositiveEq G.monoidRules w [] ↔
      ThueEq (rules G) (inputWord G w ++ [marker G]) [marker G] := by
  rw [Triangular.recognizes G w,map_eq_iff]
  simp

theorem prefix_decoding (v : List (Fin (alphabetSize G)))
    (h : ThueEq (rules G) (v ++ [marker G]) [marker G]) :
    ∃ w : PositiveWord, v = inputWord G w ∧ PositiveEq G.monoidRules w [] := by
  have hm : (alphabetEquiv G).symm (marker G) = Triangular.marker G := by
    rw [← alphabetEquiv_marker,Equiv.symm_apply_apply]
  have hh := reflection G h
  simp only [List.map_append,List.map_cons,List.map_nil,hm] at hh
  obtain ⟨w,hw,hrec⟩ := Triangular.prefix_decoding G _ hh
  refine ⟨w,?_,hrec⟩
  have he := congrArg (List.map (alphabetEquiv G)) hw
  simpa [List.map_map,Function.comp_def] using he

end
end UniversalGroup.Coding.FiniteSource
