module

public import UniversalGroup.Coding.BooneCollins.Reflection

@[expose] public section

namespace UniversalGroup.BooneCollinsCompiler
open Thue Thue.Matiyasevich1993 Thue.Matiyasevich1993.Priority
open BooneCollinsWords BooneCollinsDecoder BooneCollinsNormalForm BooneCollinsBoundary

set_option maxHeartbeats 1200000

def finalSystem (L M : IntermediateWord) : ThueSystem (Fin 2) :=
  finiteSystem ![shortLeft 0,shortLeft 1,tau L] ![shortRight,shortRight,tau M]

/-- Local normal-form reflection for a long relation, including both
possible alignments of the binary parser. -/
def LongReplacement {N : ℕ} (u : ℕ) (S : ThueSystem (Fin N))
    (L M : IntermediateWord) : Prop :=
  ∀(W : List (Fin N)) (l r : PositiveWord),
    firstNormal (decode (l++tau L++r))=endpoint N u W →
    ∃V,ThueStep S W V ∧ firstNormal (decode (l++tau M++r))=endpoint N u V

private theorem short_normal_transport {N u : ℕ} {S : ThueSystem (Fin N)}
    {X B : List (Fin N)} {W W' : PositiveWord} (i : Fin 2) (l r : PositiveWord)
    (hwords : (W=l++shortLeft i++r ∧ W'=l++shortRight++r) ∨
      (W=l++shortRight++r ∧ W'=l++shortLeft i++r))
    (hB : ThueEq S X B) (hn : firstNormal (decode W)=endpoint N u B)
    (hpar : initialParity W=false) :
    ∃B',ThueEq S X B' ∧ firstNormal (decode W')=endpoint N u B' ∧
      initialParity W'=false := by
  have he := decode_short_normal i l r
  have hp : initialParity (l++shortLeft i++r)=initialParity (l++shortRight++r) := by
    simpa only [List.append_assoc] using initialParity_prefix_congr l
      (by simp : initialParity (shortLeft i++r)=initialParity (shortRight++r))
  rcases hwords with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨B,hB,he.symm.trans hn,hp.symm.trans hpar⟩
  · exact ⟨B,hB,he.trans hn,hp.trans hpar⟩

theorem reflect_step {N u : ℕ} {S : ThueSystem (Fin N)}
    {L M : IntermediateWord}
    (hLM : LongReplacement u S L M) (hML : LongReplacement u S M L)
    (hparL : ∀r,initialParity (tau L++r)=false)
    (hparM : ∀r,initialParity (tau M++r)=false)
    {X : List (Fin N)} {W W' : PositiveWord}
    (hW : ∃B,ThueEq S X B ∧ firstNormal (decode W)=endpoint N u B ∧ initialParity W=false)
    (hs : ThueStep (finalSystem L M) W W') :
    ∃B,ThueEq S X B ∧ firstNormal (decode W')=endpoint N u B ∧ initialParity W'=false := by
  obtain ⟨B,hB,hn,hpar⟩ := hW
  obtain ⟨l,r,x,y,⟨i,hi⟩,hw⟩ := hs
  have hx : (![shortLeft 0,shortLeft 1,tau L] : Fin 3→PositiveWord) i=x := congrArg Prod.fst hi
  have hy : (![shortRight,shortRight,tau M] : Fin 3→PositiveWord) i=y := congrArg Prod.snd hi
  subst x; subst y
  fin_cases i <;> simp only [Fin.zero_eta,Fin.mk_one] at hw
  · exact short_normal_transport 0 l r hw hB hn hpar
  · exact short_normal_transport 1 l r hw hB hn hpar
  · change (W=l++tau L++r ∧ W'=l++tau M++r) ∨
      (W=l++tau M++r ∧ W'=l++tau L++r) at hw
    have hp : initialParity (l++tau L++r)=initialParity (l++tau M++r) := by
      simpa only [List.append_assoc] using initialParity_prefix_congr l
        ((hparL r).trans (hparM r).symm)
    rcases hw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · obtain ⟨V,hV,hnV⟩ := hLM B l r hn
      exact ⟨V,hB.tail hV,hnV,hp.symm.trans hpar⟩
    · obtain ⟨V,hV,hnV⟩ := hML B l r hn
      exact ⟨V,hB.tail hV,hnV,hp.trans hpar⟩

/-- Every reachable final word reconstructs exactly and its priority normal
form is the encoding of a source-equivalent word. -/
theorem reflect_reachable {N u : ℕ} {S : ThueSystem (Fin N)}
    {L M : IntermediateWord}
    (hLM : LongReplacement u S L M) (hML : LongReplacement u S M L)
    (hparL : ∀r,initialParity (tau L++r)=false)
    (hparM : ∀r,initialParity (tau M++r)=false)
    {X : List (Fin N)} {W : PositiveWord}
    (h : ThueEq (finalSystem L M) (finalEndpoint N u X) W) :
    ∃Y,ThueEq S X Y ∧ firstNormal (decode W)=endpoint N u Y ∧ initialParity W=false := by
  induction h with
  | refl =>
      refine ⟨X,Relation.ReflTransGen.refl,?_,?_⟩
      · simp
      · rw [←tau_endpoint]; exact initialParity_tau _
  | tail h hs ih => exact reflect_step hLM hML hparL hparM ih hs

/-- Reflection on complete encoded words. -/
theorem reflect_endpoints {N u : ℕ} {S : ThueSystem (Fin N)}
    {L M : IntermediateWord}
    (hLM : LongReplacement u S L M) (hML : LongReplacement u S M L)
    (hparL : ∀r,initialParity (tau L++r)=false)
    (hparM : ∀r,initialParity (tau M++r)=false)
    {X Y : List (Fin N)}
    (h : ThueEq (finalSystem L M) (finalEndpoint N u X) (finalEndpoint N u Y)) :
    ThueEq S X Y := by
  obtain ⟨Z,hZ,hn,-⟩ := reflect_reachable hLM hML hparL hparM h
  have hz : Y=Z := endpoint_injective N u (by simpa using hn)
  simpa [hz] using hZ

/-- An arbitrary prefix of a marker in its congruence class is exactly a
concatenation of complete source codes. No assumption that the prefix was
already encoded is made. -/
theorem reflect_prefix {N u : ℕ} {S : ThueSystem (Fin N)}
    {L M : IntermediateWord}
    (hLM : LongReplacement u S L M) (hML : LongReplacement u S M L)
    (hparL : ∀r,initialParity (tau L++r)=false)
    (hparM : ∀r,initialParity (tau M++r)=false)
    (p : Fin N) {Z : PositiveWord}
    (h : ThueEq (finalSystem L M) (Z++finalEndpoint N u [p]) (finalEndpoint N u [p])) :
    ∃v,Z=chi N v ∧ ThueEq S (v++[p]) [p] := by
  obtain ⟨Y,hY,hn,hpar⟩ := reflect_reachable hLM hML hparL hparM (thueEq_symm h)
  have hdecode : decode (Z++finalEndpoint N u [p])=decode Z++endpoint N u [p] := by
    rw [←tau_endpoint,decode_append_tau]
  rw [hdecode] at hn
  have hc : eCount (decode Z)=0 := by
    have hc := congrArg eCount hn
    rw [firstNormal_eCount,eCount_append,endpoint_eCount,endpoint_eCount] at hc
    omega
  obtain ⟨B,hB⟩ := ContextualSelection.exists_liftBinary_of_eCount_zero hc
  have hnZ : firstNormal (decode Z++endpoint N u [p])=decode Z++endpoint N u [p] := by
    rw [hB,firstNormal_liftBinary_append,firstNormal_endpoint]
  rw [hnZ,endpoint_eq_psi,endpoint_eq_psi] at hn
  have he : psi N Y++[1]=decode Z++psi N [p]++[1] :=
    (List.append_left_injective (List.replicate u 2)
      (by simpa only [List.append_assoc] using hn)).symm
  obtain ⟨v,R,hYword,hZword,hR⟩ := psi_occurrence_suffix (by simp : [p]≠[]) he
  have hRlen := congrArg List.length hR
  simp only [List.length_append,List.length_singleton,psi_length] at hRlen
  have hRzero : R.length=0 := by
    have hm : R.length*(N+4)=0 := by omega
    exact (Nat.mul_eq_zero.mp hm).resolve_right (by omega)
  have hRnil : R=[] := List.length_eq_zero_iff.mp hRzero
  have hpZ : initialParity Z=false := by
    have hp := initialParity_prefix_congr Z
      (show initialParity (finalEndpoint N u [p])=initialParity [] by
        rw [←tau_endpoint]; exact initialParity_tau _)
    simpa using hp.symm.trans hpar
  refine ⟨v,?_,?_⟩
  · rw [←reconstruct_of_parity hpZ,hZword,←chi_eq_tau_psi]
  · have hy : Y=v++[p] := by simpa [hRnil] using hYword
    simpa [hy] using thueEq_symm hY

end UniversalGroup.BooneCollinsCompiler
