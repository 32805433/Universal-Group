module

public import UniversalGroup.Host.Words

@[expose] public section

/-!
# Prepared inputs and the Valiev–Boone–Collins recognition interface

This module defines the input and coding data used by the proved existence theorems.
Positive monoid equality is kept distinct from equality in its group
presentation: the recognition hypothesis concerns the former, as in Valiev.
In particular, no undecidable-word-problem hypothesis is substituted for the
recognition and prefix-decoding properties.
-/

namespace UniversalGroup

abbrev PositiveWord := List (Fin 2)

/-- A positive word as a signed group word. -/
def signedPositive (w : PositiveWord) : Word 2 :=
  w.map fun i => (i, true)

/-- A finite presentation whose displayed relators are positive words. -/
def positivePresentation (relators : Fin m → PositiveWord) : FP 2 m :=
  ⟨fun i => signedPositive (relators i)⟩

/-- One symmetric rewriting step, in an arbitrary left and right context. -/
def PositiveStep (rules : Set (PositiveWord × PositiveWord))
    (u v : PositiveWord) : Prop :=
  ∃ l r x y : PositiveWord, (x, y) ∈ rules ∧
    ((u = l ++ x ++ r ∧ v = l ++ y ++ r) ∨
      (u = l ++ y ++ r ∧ v = l ++ x ++ r))

/-- Equality in the monoid presented by a set of positive rewriting rules. -/
def PositiveEq (rules : Set (PositiveWord × PositiveWord)) :=
  Relation.ReflTransGen (PositiveStep rules)

/-- A prepared two-generator input, including the infinite-order hypotheses
needed when taking free subgroups together with the input generators. -/
structure PreparedInput where
  relatorCount : ℕ
  relators : Fin relatorCount → PositiveWord
  infiniteOrder : ∀ (i : Fin 2) (z : ℤ),
    (generators (positivePresentation relators) i) ^ z = 1 → z = 0

namespace PreparedInput

def presentation (G : PreparedInput) : FP 2 G.relatorCount :=
  positivePresentation G.relators

def monoidRules (G : PreparedInput) : Set (PositiveWord × PositiveWord) :=
  Set.range fun i => (G.relators i, [])

/-- Each displayed positive relator is trivial in the input monoid itself. -/
theorem relator_monoidEq (G : PreparedInput) (i : Fin G.relatorCount) :
    PositiveEq G.monoidRules (G.relators i) [] := by
  apply Relation.ReflTransGen.single
  exact ⟨[], [], G.relators i, [], ⟨i, rfl⟩, Or.inl ⟨by simp, by simp⟩⟩

end PreparedInput

def CodeWords.rules (D : CodeWords) : Set (PositiveWord × PositiveWord) :=
  Set.range fun i => (D.E i, D.F i)

def ContainsBoth (w : PositiveWord) : Prop := 0 ∈ w ∧ 1 ∈ w

/-- Valiev's two literal codewords, with common exponent vector `(r+4,3)`. -/
def valievCode (r : ℕ) (i : Fin 2) : PositiveWord :=
  [0, 1, 0, 1] ++ List.replicate (i.val + 2) 0 ++ [1] ++
    List.replicate (r - i.val) 0

/-- Valiev's distinguished marker word. The numerical parameter `t` is
unrelated to any group-theoretic stable letter. -/
def valievMarker (r t : ℕ) : PositiveWord :=
  [0, 1, 0, 1] ++ List.replicate 4 0 ++ [1] ++
    List.replicate (r - 1) 0 ++ List.replicate (2 * t) 1

/-- The positive coding and prefix-decoding hypotheses for the host.
`recognizes` detects positive nullwords; `prefix_decoding` recovers literal code prefixes.
The literal code shapes and both-letter support are recorded separately. -/
structure ValievDatum (G : PreparedInput) extends CodeWords where
  r : ℕ
  t : ℕ
  r_ge_two : 2 ≤ r
  code_shape : code = valievCode r
  marker_shape : P = valievMarker r t
  E_support : ∀ i, ContainsBoth (E i)
  F_support : ∀ i, ContainsBoth (F i)
  P_support : ContainsBoth P
  recognizes : ∀ w : PositiveWord,
    PositiveEq G.monoidRules w [] ↔
      PositiveEq toCodeWords.rules (w.flatMap code ++ P) P
  prefix_decoding : ∀ v : PositiveWord,
    PositiveEq toCodeWords.rules (v ++ P) P →
      ∃ w : PositiveWord, v = w.flatMap code


end UniversalGroup
