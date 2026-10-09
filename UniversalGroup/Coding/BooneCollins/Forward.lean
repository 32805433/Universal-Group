module

public import UniversalGroup.Coding.BooneCollins.Compiler
public import UniversalGroup.Coding.Thue.PriorityForward

@[expose] public section

namespace UniversalGroup.BooneCollinsForward
open Thue Thue.Matiyasevich1993 Thue.Matiyasevich1993.Priority
open BooneCollinsWords BooneCollinsDecoder BooneCollinsNormalForm BooneCollinsCompiler

set_option maxHeartbeats 1200000

private theorem housekeeping_tau_step (L M : IntermediateWord) (i : Fin 4) :
    ThueStep (finalSystem L M) (tau (housekeepingF i)) (tau (housekeepingE i)) := by
  fin_cases i
  · refine ⟨[],[1],shortLeft 0,shortRight,⟨0,rfl⟩,Or.inl ?_⟩
    constructor <;> rfl
  · refine ⟨[],[],shortLeft 0,shortRight,⟨0,rfl⟩,Or.inl ?_⟩
    constructor <;> rfl
  · refine ⟨[],[1],shortLeft 1,shortRight,⟨1,rfl⟩,Or.inl ?_⟩
    constructor <;> rfl
  · refine ⟨[],[],shortLeft 1,shortRight,⟨1,rfl⟩,Or.inl ?_⟩
    constructor <;> rfl

theorem tau_step (L M : IntermediateWord) {W V : IntermediateWord}
    (h : ThueStep (stage₂System L M) W V) :
    ThueStep (finalSystem L M) (tau W) (tau V) := by
  obtain ⟨l,r,x,y,⟨i,hi⟩,hw⟩ := h
  have hx := congrArg Prod.fst hi
  have hy := congrArg Prod.snd hi
  dsimp only at hx hy
  subst x; subst y
  have hside : ThueStep (finalSystem L M) (tau (stage₂F L i)) (tau (stage₂E M i)) := by
    fin_cases i
    · exact housekeeping_tau_step L M 0
    · exact housekeeping_tau_step L M 1
    · exact housekeeping_tau_step L M 2
    · exact housekeeping_tau_step L M 3
    · exact ⟨[],[],tau L,tau M,⟨2,rfl⟩,Or.inl ⟨by simp [stage₂F],by simp [stage₂E]⟩⟩
  have hcontext := thueStep_context (tau l) (tau r) hside
  rcases hw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · simpa only [tau_append] using hcontext
  · simpa only [tau_append] using thueStep_symm hcontext

theorem tau_derivation (L M : IntermediateWord) {W V : IntermediateWord}
    (h : ThueEq (stage₂System L M) W V) :
    ThueEq (finalSystem L M) (tau W) (tau V) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (tau_step L M hs)

/-- The forward compiler for rectangular source relations and the exact
Boone–Collins terminal gamma. -/
theorem forward {N u p q : ℕ}
    (F E : Fin (2^u)→List (Fin N))
    (hF : ∀i,F i≠[]) (hE : ∀i,E i≠[])
    (hp : ∀i,(Binary.rho₁ N (F i)).length=p)
    (hq : ∀i,(Binary.rho₁ N (E i)).length=q)
    {X Y : List (Fin N)} (h : ThueEq (finiteSystem F E) X Y) :
    ThueEq (finalSystem
      (liftBinary (Priority.transpose p (fun i=>Binary.rho₁ N (F i))))
      (liftBinary (Priority.transpose q (fun i=>Binary.rho₁ N (E i)))))
      (finalEndpoint N u X) (finalEndpoint N u Y) := by
  have hbinary := (Binary.thueEq_iff F E hF hE X Y).mp h
  have hpriority := PriorityCompiler.simulate_binary u p q 1
    (fun i=>Binary.rho₁ N (F i)) (fun i=>Binary.rho₁ N (E i)) hp hq hbinary
  have hfinal := tau_derivation _ _ hpriority
  change ThueEq _ (tau (endpoint N u X)) (tau (endpoint N u Y)) at hfinal
  simpa only [tau_endpoint] using hfinal

end UniversalGroup.BooneCollinsForward
