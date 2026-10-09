module

public import UniversalGroup.Coding.Data
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The literal Boone–Collins compiler words

These are the substitutions and column transpositions on page 2 of Boone and
Collins, *Embeddings into groups with only a few defining relations* (1974).
The source alphabet is numbered from zero here: source letters `0,1` are the
two input letters, and letter `2` is the marker.  The intermediate alphabet is
`β = 0, γ = 1, ε = 2`; the final alphabet is `σ = 0, α = 1`.

This module proves only literal word identities and support.  Semantic
reflection of rewriting is a separate part of the compiler.
-/

namespace UniversalGroup.BooneCollinsWords

abbrev Intermediate := Fin 3
abbrev IntermediateWord := List Intermediate

/-- The fixed-width first substitution, with the source index shifted by one. -/
def psiLetter (r : ℕ) (i : Fin r) : IntermediateWord :=
  [0, 0] ++ List.replicate (i.val + 1) 1 ++ [0] ++
    List.replicate (r - i.val) 1

def psi (r : ℕ) (w : List (Fin r)) : IntermediateWord :=
  w.flatMap (psiLetter r)

/-- `τ(β)=σα`, `τ(γ)=σ`, and `τ(ε)=αα`. -/
def tauLetter : Intermediate → PositiveWord := ![[0, 1], [0], [1, 1]]

def tau (w : IntermediateWord) : PositiveWord := w.flatMap tauLetter

def chiLetter (r : ℕ) (i : Fin r) : PositiveWord := tau (psiLetter r i)

def chi (r : ℕ) (w : List (Fin r)) : PositiveWord :=
  w.flatMap (chiLetter r)

@[simp] theorem psi_append (r : ℕ) (u v : List (Fin r)) :
    psi r (u ++ v) = psi r u ++ psi r v := by simp [psi]

@[simp] theorem tau_append (u v : IntermediateWord) :
    tau (u ++ v) = tau u ++ tau v := by simp [tau]

@[simp] theorem chi_append (r : ℕ) (u v : List (Fin r)) :
    chi r (u ++ v) = chi r u ++ chi r v := by simp [chi]

theorem chi_eq_tau_psi (r : ℕ) (w : List (Fin r)) :
    chi r w = tau (psi r w) := by
  simp only [chi, tau, psi, List.flatMap_assoc]
  rfl

@[simp] theorem psiLetter_length (r : ℕ) (i : Fin r) :
    (psiLetter r i).length = r + 4 := by
  simp [psiLetter]
  omega

@[simp] theorem psiLetter_getD_zero (r : ℕ) (i : Fin r) :
    (psiLetter r i).getD 0 0 = 0 := by simp [psiLetter]

@[simp] theorem beta_mem_psiLetter (r : ℕ) (i : Fin r) :
    (0 : Intermediate) ∈ psiLetter r i := by simp [psiLetter]

@[simp] theorem tau_gamma_replicate (n : ℕ) :
    tau (List.replicate n 1) = List.replicate n 0 := by
  simp [tau, tauLetter, List.flatMap_replicate]

/-- This is Valiev's displayed word, before specializing the source letter. -/
theorem chiLetter_eq (r : ℕ) (i : Fin r) :
    chiLetter r i = [0, 1, 0, 1] ++ List.replicate (i.val + 2) 0 ++
      [1] ++ List.replicate (r - i.val) 0 := by
  simp only [chiLetter, psiLetter, tau_append, tau_gamma_replicate]
  simp only [tau, List.flatMap_cons, List.flatMap_nil, tauLetter,
    Matrix.cons_val_zero, List.append_nil]
  rw [show i.val + 2 = (i.val + 1) + 1 by omega, List.replicate_add]
  simp only [List.replicate_add, List.replicate_one, List.append_assoc,
    List.cons_append, List.nil_append]

/-- The first two source letters give the exact two Valiev codewords. -/
theorem chiLetter_input (r : ℕ) (hr : 2 ≤ r) (i : Fin 2) :
    chiLetter r (Fin.castLE hr i) = valievCode r i := by
  simp [chiLetter_eq, valievCode]

/-- The third source letter followed by the selection suffix is the exact
marker used in the later recognition interface. -/
theorem chiLetter_marker (r t : ℕ) (hr : 3 ≤ r) :
    chiLetter r ⟨2, by omega⟩ ++ [0] ++ List.replicate (2 * t) 1 =
      valievMarker r t := by
  rw [chiLetter_eq]
  have h : r - 1 = (r - 2) + 1 := by omega
  simp [valievMarker, h, List.replicate_add, List.append_assoc]

theorem chiLetter_support (r : ℕ) (i : Fin r) :
    ContainsBoth (chiLetter r i) := by
  simp [ContainsBoth, chiLetter_eq]

theorem valievMarker_support (r t : ℕ) : ContainsBoth (valievMarker r t) := by
  simp [ContainsBoth, valievMarker]

/-- Read a rectangular array down each column, from the first column onward.
`getD` only supplies a total definition; the rows used below have exactly the
stated width. -/
def transpose {s : ℕ} (width : ℕ) (rows : Fin s → IntermediateWord) :
    IntermediateWord :=
  (List.range width).flatMap fun j => List.ofFn fun i => (rows i).getD j 0

theorem beta_mem_transpose {s width : ℕ} (rows : Fin s → IntermediateWord)
    (hs : 0 < s) (hw : 0 < width) (hrows : ∀ i, (rows i).getD 0 0 = 0) :
    (0 : Intermediate) ∈ transpose width rows := by
  apply List.mem_flatMap.mpr
  refine ⟨0, List.mem_range.mpr hw, List.mem_ofFn.mpr ?_⟩
  exact ⟨⟨0, hs⟩, hrows _⟩

theorem tau_support_of_beta_mem {w : IntermediateWord} (hw : 0 ∈ w) :
    ContainsBoth (tau w) := by
  constructor
  · exact List.mem_flatMap.mpr ⟨0, hw, by simp [tauLetter]⟩
  · exact List.mem_flatMap.mpr ⟨0, hw, by simp [tauLetter]⟩

/-- The two transposition words for `2^t` triangular rules. -/
def longLeft (r t : ℕ) (lhs : Fin (2 ^ t) → Fin r) : IntermediateWord :=
  transpose (r + 4) fun i => psiLetter r (lhs i)

def longRight (r t : ℕ) (rhs : Fin (2 ^ t) → Fin r × Fin r) : IntermediateWord :=
  transpose (2 * (r + 4)) fun i =>
    psiLetter r (rhs i).1 ++ psiLetter r (rhs i).2

theorem longLeft_support (r t : ℕ) (lhs : Fin (2 ^ t) → Fin r) :
    ContainsBoth (tau (longLeft r t lhs)) := by
  apply tau_support_of_beta_mem
  apply beta_mem_transpose _ (by positivity) (by omega)
  simp [psiLetter]

theorem longRight_support (r t : ℕ) (rhs : Fin (2 ^ t) → Fin r × Fin r) :
    ContainsBoth (tau (longRight r t rhs)) := by
  apply tau_support_of_beta_mem
  apply beta_mem_transpose _ (by positivity) (by omega)
  simp [psiLetter]

/-- The three final rules, oriented as `(E,F)` in `CodeWords.rules`. -/
def words (r t : ℕ) (lhs : Fin (2 ^ t) → Fin r)
    (rhs : Fin (2 ^ t) → Fin r × Fin r) : CodeWords where
  E := ![[0, 1, 1], [0, 1, 1], tau (longLeft r t lhs)]
  F := ![[1, 1, 0, 1, 0], [1, 1, 0, 0], tau (longRight r t rhs)]
  code := valievCode r
  P := valievMarker r t

theorem words_E_support (r t : ℕ) (lhs : Fin (2 ^ t) → Fin r)
    (rhs : Fin (2 ^ t) → Fin r × Fin r) (i : Fin 3) :
    ContainsBoth ((words r t lhs rhs).E i) := by
  fin_cases i
  · simp [words, ContainsBoth]
  · simp [words, ContainsBoth]
  · exact longLeft_support r t lhs

theorem words_F_support (r t : ℕ) (lhs : Fin (2 ^ t) → Fin r)
    (rhs : Fin (2 ^ t) → Fin r × Fin r) (i : Fin 3) :
    ContainsBoth ((words r t lhs rhs).F i) := by
  fin_cases i
  · simp [words, ContainsBoth]
  · simp [words, ContainsBoth]
  · exact longRight_support r t rhs

end UniversalGroup.BooneCollinsWords
