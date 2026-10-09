module

public import UniversalGroup.Coding.BooneCollins.NormalForm
public import UniversalGroup.Coding.Thue.PriorityReflection

@[expose] public section

namespace UniversalGroup.BooneCollinsReflection
open Thue Thue.Matiyasevich1993 Thue.Matiyasevich1993.Priority
open BooneCollinsNormalForm BooneCollinsBoundary

set_option maxHeartbeats 1200000

/-- A transposed replacement selects exactly one source relation in the
complete normalized endpoint. The final gamma remains in the right context. -/
theorem normal_long_replacement {N u p q : ℕ}
    (S : ThueSystem (Fin N)) (W : List (Fin N))
    (rowsX rowsY : Fin (2^u) → List (Fin 2))
    (hp : ∀j,(rowsX j).length=p) (hq : ∀j,(rowsY j).length=q)
    (hwidth : 2 ≤ p)
    (hstart : ∀j,∃tail,rowsX j=(0:Fin 2)::0::tail)
    (hrow : ∀j before after,
      Binary.rho₁ N W ++ [1] = before ++ rowsX j ++ after →
      ∃V,ThueStep S W V ∧
        before ++ rowsY j ++ after = Binary.rho₁ N V ++ [1])
    (l r : List (Fin 3))
    (hn : firstNormal (l ++ liftBinary (transpose p rowsX) ++ r) = endpoint N u W) :
    ∃V,ThueStep S W V ∧
      firstNormal (l ++ liftBinary (transpose q rowsY) ++ r) = endpoint N u V := by
  obtain ⟨tail,htail⟩ := transpose_starts_two_columns rowsX hwidth hstart
  have hshape : ∃tail',liftBinary (transpose p rowsX) =
      List.replicate (2*2^u) a ++ tail' := by
    refine ⟨liftBinary tail,?_⟩
    simp [htail,liftBinary,liftBit,a]
  have hcount : eCount (l ++ liftBinary (transpose p rowsX) ++ r) = u := by
    simpa only [firstNormal_eCount,endpoint_eCount] using congrArg eCount hn
  have hno : NoAAA (firstNormal (l ++ liftBinary (transpose p rowsX) ++ r)) := by
    rw [hn]; exact endpoint_noAAA N u W
  obtain ⟨hl,hr⟩ := PriorityCompiler.context_counts_of_long hshape
    (longRunRequirement_two_power u) hno hcount rfl (eCount_liftBinary _)
  obtain ⟨j,before,after,he,hnew⟩ := PriorityCompiler.select_same_row rowsX rowsY hp hq hl hr hn
  obtain ⟨V,hstep,hV⟩ := hrow j before after he
  refine ⟨V,hstep,?_⟩
  simpa only [hV,endpoint] using hnew

end UniversalGroup.BooneCollinsReflection
