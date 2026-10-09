module

public import UniversalGroup.Coding.BooneCollins.Words
public import UniversalGroup.Coding.Thue.BinaryStage

@[expose] public section

/-!
# The terminal marker and the altered last-letter boundary case

The priority decoder ends in an extra `γ`.  Code occurrences cannot consume
this marker.  Replacing just the last `γ` of a code row by `β` cannot produce
an occurrence in the code language, even in the presence of that marker.
This is the boundary exclusion used in Boone–Collins–Matijasevic, Lemma 2.16.
-/

namespace UniversalGroup.BooneCollinsBoundary

open Thue.Matiyasevich1993.Binary
open BooneCollinsWords

variable {N : ℕ}

private theorem marker_boundary_suffix {W : List (Fin N)}
    {l s : List (Fin 2)}
    (h : rho₁ N W ++ [1] = l ++ [0, 0] ++ s) :
    ∃ L R, W = L ++ R ∧ l = rho₁ N L := by
  have hs : s ≠ [] := by
    intro hs
    have he := congrArg List.getLast? h
    simp [hs] at he
  have he : s.getLast? = some 1 := by
    have he := congrArg List.getLast? h
    simpa only [List.getLast?_append_of_ne_nil _ hs,
      List.getLast?_append, List.getLast?_singleton, Option.some_or] using he.symm
  obtain ⟨s', rfl⟩ := List.getLast?_eq_some_iff.mp he
  have hp : rho₁ N W = l ++ [0, 0] ++ s' := by
    exact List.append_cancel_right (by simpa only [List.append_assoc] using h)
  exact rho₁_marker_boundary hp

/-- Prefix recognition remains valid when the whole encoded word has a
single terminal `γ`. -/
theorem binary_prefix_suffix {X W : List (Fin N)} {s : List (Fin 2)}
    (h : rho₁ N W ++ [1] = rho₁ N X ++ s) :
    ∃ R, W = X ++ R ∧ s = rho₁ N R ++ [1] := by
  induction X generalizing W s with
  | nil => exact ⟨W, by simp, by simpa [rho₁] using h.symm⟩
  | cons j X ih =>
      cases W with
      | nil =>
          have hlen := congrArg List.length h
          simp at hlen
          omega
      | cons k W =>
          rw [rho₁_cons, rho₁_cons] at h
          have hparts := List.append_inj
            (show rho₁Letter N k ++ (rho₁ N W ++ [1]) =
              rho₁Letter N j ++ (rho₁ N X ++ s) by
                simpa only [List.append_assoc] using h)
            (show (rho₁Letter N k).length = (rho₁Letter N j).length by simp)
          have hkj : k = j := rho₁Letter_injective hparts.1
          subst k
          obtain ⟨R, hW, hs⟩ := ih hparts.2
          exact ⟨R, by simp [hW], hs⟩

/-- A code row occurring in a word with the terminal marker is still aligned
with source letters, and its right context retains that marker. -/
theorem binary_occurrence_suffix {W X : List (Fin N)} {l s : List (Fin 2)}
    (hX : X ≠ []) (h : rho₁ N W ++ [1] = l ++ rho₁ N X ++ s) :
    ∃ L R, W = L ++ X ++ R ∧ l = rho₁ N L ∧ s = rho₁ N R ++ [1] := by
  obtain ⟨tail, ht⟩ := rho₁_starts_aa hX
  have hm : rho₁ N W ++ [1] = l ++ [0, 0] ++ (tail ++ s) := by
    simpa [ht, List.append_assoc] using h
  obtain ⟨L, W', hW, hl⟩ := marker_boundary_suffix hm
  subst W
  have hp : rho₁ N W' ++ [1] = rho₁ N X ++ s := by
    simpa only [rho₁_append, hl, List.append_assoc,
      List.append_cancel_left_eq] using h
  obtain ⟨R, hR, hs⟩ := binary_prefix_suffix hp
  exact ⟨L, R, by simp [hR, List.append_assoc], hl, hs⟩

private theorem binary_last (j : Fin N) : (rho₁Letter N j).getLast? = some 1 := by
  obtain ⟨v, hv⟩ := rho₁Letter_ends_b j
  simp [hv]

private theorem altered_prefix_impossible {W X : List (Fin N)}
    (hX : X ≠ []) (s : List (Fin 2)) :
    rho₁ N W ++ [1] ≠ (rho₁ N X).dropLast ++ [0] ++ s := by
  intro h
  let Y := X.dropLast
  let j := X.getLast hX
  have hXsplit : X = Y ++ [j] := (List.dropLast_append_getLast hX).symm
  rw [hXsplit] at h
  have hj : rho₁Letter N j ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp at hh
  have hp : rho₁ N W ++ [1] = rho₁ N Y ++
      ((rho₁Letter N j).dropLast ++ [0] ++ s) := by
    simpa [rho₁, List.dropLast_append_of_ne_nil hj, List.append_assoc] using h
  obtain ⟨R, hW, hR⟩ := binary_prefix_suffix hp
  cases R with
  | nil =>
      have hh := congrArg List.length hR
      simp only [List.length_append, List.length_dropLast, rho₁Letter_length,
        List.length_singleton, rho₁_length, List.length_nil, Nat.zero_mul] at hh
      omega
  | cons k R =>
      have he : rho₁Letter N k = (rho₁Letter N j).dropLast ++ [0] := by
        have hh : rho₁Letter N k ++ (rho₁ N R ++ [1]) =
            ((rho₁Letter N j).dropLast ++ [0]) ++ s := by
          simpa only [rho₁_cons, List.append_assoc] using hR.symm
        exact (List.append_inj hh (by simp)).1
      have hh := congrArg List.getLast? he
      simp [binary_last] at hh

/-- The exceptional long-rule parse, which changes its final `γ` into `β`,
is impossible in an encoded word with a terminal `γ`. -/
theorem binary_altered_occurrence_impossible {W X : List (Fin N)}
    (hX : X ≠ []) (l s : List (Fin 2)) :
    rho₁ N W ++ [1] ≠ l ++ (rho₁ N X).dropLast ++ [0] ++ s := by
  intro h
  obtain ⟨tail, ht⟩ := rho₁_starts_aa hX
  have hn : tail ≠ [] := by
    intro he
    have hh := congrArg List.length ht
    have hxlen : 0 < X.length := List.length_pos_iff.mpr hX
    simp only [rho₁_length, List.length_cons, List.length_nil, he] at hh
    have hm : 4 ≤ X.length * (N + 4) := by
      calc
        4 ≤ 1 * (N + 4) := by omega
        _ ≤ X.length * (N + 4) := Nat.mul_le_mul_right _ hxlen
    omega
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hn
  have hm : rho₁ N W ++ [1] = l ++ [0, 0] ++
      ((z :: zs).dropLast ++ [0] ++ s) := by
    simpa [ht, List.append_assoc] using h
  obtain ⟨L, R, hW, hl⟩ := marker_boundary_suffix hm
  subst W
  have hp : rho₁ N R ++ [1] = (rho₁ N X).dropLast ++ [0] ++ s := by
    simpa only [rho₁_append, hl, List.append_assoc,
      List.append_cancel_left_eq] using h
  exact altered_prefix_impossible hX s hp

/-- Forget the unused third letter when comparing with the binary code. -/
def binaryProjection : Intermediate → Fin 2 := ![0, 1, 0]

@[simp] theorem map_binaryProjection_psiLetter (i : Fin N) :
    (psiLetter N i).map binaryProjection = rho₁Letter N i := by
  simp [psiLetter, rho₁Letter, binaryProjection]

@[simp] theorem map_binaryProjection_psi (W : List (Fin N)) :
    (psi N W).map binaryProjection = rho₁ N W := by
  induction W with
  | nil => rfl
  | cons j W ih =>
      change (psiLetter N j ++ psi N W).map binaryProjection = _
      simp [ih]

theorem psi_length (W : List (Fin N)) :
    (psi N W).length = W.length * (N + 4) := by
  simpa only [List.length_map, rho₁_length] using
    congrArg List.length (map_binaryProjection_psi W)

/-- The actual intermediate-alphabet version of the code-occurrence lemma. -/
theorem psi_occurrence_suffix {W X : List (Fin N)}
    {l s : IntermediateWord} (hX : X ≠ [])
    (h : psi N W ++ [1] = l ++ psi N X ++ s) :
    ∃ L R, W = L ++ X ++ R ∧ l = psi N L ∧ s = psi N R ++ [1] := by
  have hb : rho₁ N W ++ [1] = l.map binaryProjection ++
      rho₁ N X ++ s.map binaryProjection := by
    simpa only [List.map_append, List.map_cons, List.map_nil,
      map_binaryProjection_psi, show binaryProjection 1 = 1 from rfl] using
      congrArg (List.map binaryProjection) h
  obtain ⟨L, R, hW, hl, hs⟩ := binary_occurrence_suffix hX hb
  have hlen : l.length = (psi N L).length := by
    simpa [psi_length] using congrArg List.length hl
  have hh : l ++ (psi N X ++ s) =
      psi N L ++ (psi N X ++ (psi N R ++ [1])) := by
    simpa [hW, List.append_assoc] using h.symm
  have hp := List.append_inj hh hlen
  refine ⟨L, R, hW, hp.1, ?_⟩
  exact List.append_cancel_left hp.2


end UniversalGroup.BooneCollinsBoundary
