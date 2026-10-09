module

public import UniversalGroup.Computability.Machine.TM1BinaryAdapter
public import UniversalGroup.Computability.Machine.TM0PostAdapter

@[expose] public section

/-!
# Finite Thue recognition for supported one-tape machines

Binary compilation and restriction to a finite state support produce a Post
machine. Its finite Thue system recognizes precisely the source machine's
halting inputs.
-/

namespace UniversalGroup

open Turing

namespace SupportedTM1Thue

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable [Fintype Γ] [Fintype σ]

noncomputable abbrev State (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) :=
  TM1BinaryAdapter.support B M S

noncomputable abbrev Alphabet (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) :=
  PostMachine.Symbol (TM0PostAdapter.Phase (State B M S))

/-- The combined write-and-move machine obtained from a supported source
`TM1`, after binary compilation and restriction to finite state. -/
noncomputable def postMachine (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S) :
    PostMachine.Machine (TM0PostAdapter.Phase (State B M S)) :=
  @TM0PostAdapter.machine (State B M S)
    (TM1BinaryAdapter.finiteStateInhabited B M S hS)
    (TM1BinaryAdapter.finiteMachine B M S hS)

/-- The Thue word encoding the initial configuration on a source input. -/
noncomputable def start (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S)
    (input : List Γ) : List (Alphabet B M S) :=
  PostMachine.encode <|
    @TM0PostAdapter.init (State B M S)
      (TM1BinaryAdapter.finiteStateInhabited B M S hS)
      (TM1BinaryAdapter.encodeInput B input)

/-- The resulting finite fixed-target Thue system recognizes precisely the
halting inputs of the supported source program. -/
theorem thue_iff_eval_dom (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S)
    (input : List Γ) :
    ThueEq (PostMachine.system (postMachine B M S hS))
        (start B M S hS input)
        (PostMachine.target : List (Alphabet B M S)) ↔
      (TM1.eval M input).Dom := by
  let : Inhabited (State B M S) :=
    TM1BinaryAdapter.finiteStateInhabited B M S hS
  exact (TM0PostAdapter.thue_iff_tm0_eval_dom
    (TM1BinaryAdapter.finiteMachine B M S hS)
    (TM1BinaryAdapter.encodeInput B input)).trans
      (TM1BinaryAdapter.finite_eval_dom_iff B M S hS input)

/-- The Thue presentation used above has finitely many rules. -/
theorem system_finite (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S) :
    Set.Finite (PostMachine.system (postMachine B M S hS)) := by
  let : Inhabited (State B M S) :=
    TM1BinaryAdapter.finiteStateInhabited B M S hS
  exact TM0PostAdapter.thue_system_finite
    (TM1BinaryAdapter.finiteMachine B M S hS)

end SupportedTM1Thue

end UniversalGroup
