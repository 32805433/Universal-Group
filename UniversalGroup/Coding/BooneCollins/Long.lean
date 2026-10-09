module

public import UniversalGroup.Coding.BooneCollins.Compiler
public import UniversalGroup.Coding.BooneCollins.Transpose

@[expose] public section

namespace UniversalGroup.BooneCollinsLong
open Thue Thue.Matiyasevich1993 Thue.Matiyasevich1993.Priority
open BooneCollinsWords BooneCollinsDecoder BooneCollinsNormalForm
open BooneCollinsBoundary BooneCollinsReflection BooneCollinsCompiler BooneCollinsTranspose

set_option maxHeartbeats 1200000

private theorem rho_ends {N : ℕ} (W : List (Fin N)) (hW : W≠[]) :
    ∃v,Binary.rho₁ N W=v++[1] := by
  induction W with
  | nil => exact False.elim (hW rfl)
  | cons i W ih =>
      by_cases hw : W=[]
      · subst W
        simpa only [Binary.rho₁_cons,Binary.rho₁,List.flatMap_cons,List.flatMap_nil,List.append_nil]
          using Binary.rho₁Letter_ends_b i
      · obtain ⟨v,hv⟩ := ih hw
        exact ⟨Binary.rho₁Letter N i++v,by simp [hv,List.append_assoc]⟩

private theorem row_step {N : ℕ} (S : ThueSystem (Fin N))
    {W X Y : List (Fin N)} (hX : X≠[]) (hXY : ThueStep S X Y)
    {before after : PositiveWord}
    (he : Binary.rho₁ N W++[1]=before++Binary.rho₁ N X++after) :
    ∃V,ThueStep S W V ∧ before++Binary.rho₁ N Y++after=Binary.rho₁ N V++[1] := by
  obtain ⟨l,r,hw,hb,ha⟩ := binary_occurrence_suffix hX he
  refine ⟨l++Y++r,?_,by simp [hb,ha,List.append_assoc]⟩
  rw [hw]
  exact thueStep_context l r hXY

/-- The final binary parser's two alignments both reduce to the same
source-row replacement. The possible altered last row is forbidden by ψ. -/
theorem encoded_long_replacement {N u p q : ℕ}
    (S : ThueSystem (Fin N)) (F E : Fin (2^u)→List (Fin N))
    (hF : ∀j,F j≠[]) (hE : ∀j,E j≠[])
    (hp : ∀j,(Binary.rho₁ N (F j)).length=p)
    (hq : ∀j,(Binary.rho₁ N (E j)).length=q)
    (hp3 : 3≤p) (hq3 : 3≤q)
    (hFE : ∀j,ThueStep S (F j) (E j)) :
    LongReplacement u S
      (liftBinary (Priority.transpose p (fun j=>Binary.rho₁ N (F j))))
      (liftBinary (Priority.transpose q (fun j=>Binary.rho₁ N (E j)))) := by
  intro W l r hn
  let FX := fun j=>Binary.rho₁ N (F j)
  let EX := fun j=>Binary.rho₁ N (E j)
  have hstartF : ∀j,∃v,FX j=(0:Fin 2)::0::v := fun j=>Binary.rho₁_starts_aa (hF j)
  have hstartE : ∀j,∃v,EX j=(0:Fin 2)::0::v := fun j=>Binary.rho₁_starts_aa (hE j)
  have hendF : ∀j,∃v,FX j=v++[1] := fun j=>rho_ends (F j) (hF j)
  have hendE : ∀j,∃v,EX j=v++[1] := fun j=>rho_ends (E j) (hE j)
  rcases tau_decode_reconstruct r with hr | hr
  · rw [←hr,decode_context] at hn ⊢
    exact normal_long_replacement S W FX EX hp hq (by omega) hstartF
      (fun j _ _ he=>row_step S (hF j) (hFE j) he) (decode l) (decode r) hn
  · obtain ⟨preF,hpreF⟩ := RowSelection.transpose_ends_b FX
      (pow_pos (by omega) u) (by omega) hp hendF
    obtain ⟨preE,hpreE⟩ := RowSelection.transpose_ends_b EX
      (pow_pos (by omega) u) (by omega) hq hendE
    have hliftF : liftBinary (Priority.transpose p FX)=liftBinary preF++[1] := by
      rw [hpreF,liftBinary_append]; rfl
    have hliftE : liftBinary (Priority.transpose q EX)=liftBinary preE++[1] := by
      rw [hpreE,liftBinary_append]; rfl
    change firstNormal (decode (l++tau (liftBinary (Priority.transpose p FX))++r))=_ at hn
    change ∃V,ThueStep S W V ∧ firstNormal (decode (l++tau (liftBinary (Priority.transpose q EX))++r))=_
    rw [←hr,hliftF,decode_residual_context] at hn
    rw [←hr,hliftE,decode_residual_context]
    have haltF : liftBinary (Priority.transpose p (alterRows FX))=liftBinary preF++[0] := by
      rw [transpose_alterRows FX (pow_pos (by omega) u) (by omega) hp hendF,hpreF]
      simp only [List.dropLast_concat,liftBinary_append]
      rfl
    have haltE : liftBinary (Priority.transpose q (alterRows EX))=liftBinary preE++[0] := by
      rw [transpose_alterRows EX (pow_pos (by omega) u) (by omega) hq hendE,hpreE]
      simp only [List.dropLast_concat,liftBinary_append]
      rfl
    rw [←haltF] at hn
    rw [←haltE]
    apply normal_long_replacement S W (alterRows FX) (alterRows EX)
      (alterRows_length FX (by omega) hp) (alterRows_length EX (by omega) hq)
      (by omega) (alterRows_starts FX hp3 hp hstartF) _ (decode l) (decode r) hn
    intro j before after he
    by_cases hj : j.val+1=2^u
    · have hb : Binary.rho₁ N W++[1]=before++(Binary.rho₁ N (F j)).dropLast++[0]++after := by
        simpa only [alterRows,ite_eq_left hj,FX,List.append_assoc] using he
      exact False.elim (binary_altered_occurrence_impossible (hF j) before after hb)
    · simp only [alterRows,ite_eq_right hj] at he ⊢
      exact row_step S (hF j) (hFE j) he

/-- Every long side starts with a complete beta code, so it preserves the
parity invariant in arbitrary right context. -/
theorem long_initialParity {s width : ℕ} (rows : Fin s→PositiveWord)
    (hs : 0<s) (hw : 2≤width)
    (hstart : ∀j,∃v,rows j=(0:Fin 2)::0::v) (R : PositiveWord) :
    initialParity (tau (liftBinary (Priority.transpose width rows))++R)=false := by
  obtain ⟨v,hv⟩ := transpose_starts_two_columns rows hw hstart
  have hp : 0<2*s := by omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  rw [hv,hk,List.replicate_succ]
  change initialParity (0::1::(tau (liftBinary (List.replicate k 0++v))++R))=false
  rfl

end UniversalGroup.BooneCollinsLong
