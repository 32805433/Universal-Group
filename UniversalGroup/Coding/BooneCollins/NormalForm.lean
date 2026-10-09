module

public import UniversalGroup.Coding.BooneCollins.Boundary
public import UniversalGroup.Coding.BooneCollins.Decoder

@[expose] public section

namespace UniversalGroup.BooneCollinsNormalForm
open Thue.Matiyasevich1993 Thue.Matiyasevich1993.Priority
open BooneCollinsWords BooneCollinsBoundary

set_option maxHeartbeats 1200000

/-- Canonical intermediate endpoint, with Boone's terminal gamma. -/
def endpoint (N u : ℕ) (W : List (Fin N)) : List (Fin 3) :=
  liftBinary (Binary.rho₁ N W ++ [1]) ++ List.replicate u e

@[simp] theorem endpoint_eCount (N u : ℕ) (W : List (Fin N)) :
    eCount (endpoint N u W) = u := by
  rw [endpoint,eCount_append,eCount_liftBinary]
  simp [eCount]

@[simp] theorem firstNormal_endpoint (N u : ℕ) (W : List (Fin N)) :
    firstNormal (endpoint N u W) = endpoint N u W := by
  rw [endpoint, firstNormal_liftBinary_append, firstNormal_replicate_e]

theorem endpoint_injective (N u : ℕ) : Function.Injective (endpoint N u) := by
  intro W V h
  have hb := liftBinary_injective (List.append_left_injective (List.replicate u e) h)
  exact Binary.rho₁_injective (List.append_left_injective [1] hb)

private theorem noAAA_iff_not_infix {W : List (Fin 3)} :
    NoAAA W ↔ ¬ [a,a,a] <:+: W := by
  constructor
  · intro h ⟨l,r,he⟩; exact h ⟨l,r,he.symm⟩
  · intro h ⟨l,r,he⟩; exact h ⟨l,r,he.symm⟩

private theorem noAAA_liftBinary {W : List (Fin 2)}
    (h : ¬ ∃ l r, W = l ++ [(0 : Fin 2),0,0] ++ r) : NoAAA (liftBinary W) := by
  rw [noAAA_iff_not_infix]
  intro hi
  obtain ⟨Z,hZW,hmap⟩ := List.infix_map_iff.mp hi
  have hZ : Z = [(0 : Fin 2),0,0] := by
    apply liftBinary_injective
    simpa [liftBinary,liftBit,a] using hmap.symm
  subst Z
  obtain ⟨l,r,he⟩ := hZW
  exact h ⟨l,r,he.symm⟩

private theorem noAAA_append_of_count_zero {W R : List (Fin 3)}
    (hW : NoAAA W) (hR : R.count a = 0) : NoAAA (W ++ R) := by
  rw [noAAA_iff_not_infix] at hW ⊢
  rw [List.infix_append_iff]
  rintro (h | h | ⟨l₁,l₂,he,h₁,h₂⟩)
  · exact hW h
  · have hc := List.IsInfix.count_le a h
    simp [hR] at hc
  · have hp : l₂ <:+ List.replicate 3 a := ⟨l₁, by simpa using he.symm⟩
    have hr := (List.suffix_replicate_iff.mp hp).2
    have hc := List.IsInfix.count_le a h₂.isInfix
    rw [hR,hr,List.count_replicate_self] at hc
    have hz : l₂ = [] := List.length_eq_zero_iff.mp (by omega)
    subst l₂
    simp only [List.append_nil] at he
    subst l₁
    exact hW h₁.isInfix

/-- Canonical endpoints have no run of three beta letters. -/
theorem endpoint_noAAA (N u : ℕ) (W : List (Fin N)) : NoAAA (endpoint N u W) := by
  unfold endpoint
  rw [liftBinary_append, List.append_assoc]
  apply noAAA_append_of_count_zero (noAAA_liftBinary (Binary.rho₁_noAAA W))
  simp only [liftBinary,List.map_cons,List.map_nil,liftBit,
    List.count_append,List.count_cons]
  change 0 + (List.replicate u e).count a = 0
  rw [Nat.zero_add,List.count_eq_zero]
  simp [a,e]

theorem psi_eq_lift (N : ℕ) (W : List (Fin N)) :
    psi N W = liftBinary (Binary.rho₁ N W) := by
  induction W with
  | nil => rfl
  | cons i W ih =>
      change psiLetter N i ++ psi N W = _
      rw [Binary.rho₁_cons, liftBinary_append, ih]
      congr 1
      simp [psiLetter,Binary.rho₁Letter,liftBinary,liftBit,List.map_replicate]
      rfl

theorem endpoint_eq_psi (N u : ℕ) (W : List (Fin N)) :
    endpoint N u W = psi N W ++ [1] ++ List.replicate u 2 := by
  rw [endpoint,liftBinary_append,← psi_eq_lift]
  rfl

/-- Exact literal binary endpoint used by the three-rule system. -/
def finalEndpoint (N u : ℕ) (W : List (Fin N)) : PositiveWord :=
  chi N W ++ [0] ++ List.replicate (2*u) 1

@[simp] theorem tau_endpoint (N u : ℕ) (W : List (Fin N)) :
    tau (endpoint N u W) = finalEndpoint N u W := by
  rw [endpoint_eq_psi, tau_append, tau_append, ← chi_eq_tau_psi]
  have hrep : tau (List.replicate u 2) = List.replicate (2*u) 1 := by
    induction u with
    | zero => rfl
    | succ u ih =>
        rw [List.replicate_succ]
        change [1,1] ++ tau (List.replicate u 2) = _
        rw [ih,show 2*(u+1)=2+2*u by omega,List.replicate_add]
        rfl
  rw [hrep]
  rfl

@[simp] theorem decode_finalEndpoint (N u : ℕ) (W : List (Fin N)) :
    BooneCollinsDecoder.decode (finalEndpoint N u W) = endpoint N u W := by
  rw [← tau_endpoint,BooneCollinsDecoder.decode_tau]

end UniversalGroup.BooneCollinsNormalForm
