module

public import UniversalGroup.Foundations.Presentation
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# Codewords and words for the six-generator host

The simulator data and the six named letters determine the common input
attachment relations. Every abbreviation is a word in the ambient alphabet;
it does not introduce an additional presentation generator.
-/

namespace UniversalGroup.Word

@[simp]
theorem substitute_generator (σ : Fin n → Word k) (i : Fin n) :
    substitute σ (generator i) = σ i := by
  simp [substitute, generator]

@[simp]
theorem substitute_inverse (σ : Fin n → Word k) (w : Word n) :
    substitute σ (inverse w) = inverse (substitute σ w) := by
  simpa [inverse, FreeGroup.invRev, List.map_reverse] using substitute_invRev σ w

@[simp]
theorem substitute_product (σ : Fin n → Word k) (ws : List (Word n)) :
    substitute σ (product ws) = product (ws.map (substitute σ)) :=
  substitute_flatten σ ws

@[simp]
theorem substitute_pow (σ : Fin n → Word k) (w : Word n) (j : ℕ) :
    substitute σ (pow w j) = pow (substitute σ w) j := by
  simp [pow, substitute_flatten, product]

@[simp]
theorem substitute_commutator (σ : Fin n → Word k) (u v : Word n) :
    substitute σ (commutator u v) = commutator (substitute σ u) (substitute σ v) := by
  simp [commutator, mul]

end UniversalGroup.Word

namespace UniversalGroup

/-- The three positive rewriting rules, distinguished positive word, and the
two positive codewords for the prepared input group. -/
structure CodeWords where
  E : Fin 3 → List (Fin 2)
  F : Fin 3 → List (Fin 2)
  P : List (Fin 2)
  code : Fin 2 → List (Fin 2)

/-- Values of the six named letters, as words in an arbitrary alphabet. -/
structure BaseWords (n : ℕ) where
  c : Word n
  d : Word n
  f : Word n
  k : Word n
  a : Word n
  b : Word n

namespace BaseWords

def x (w : BaseWords n) : Word n :=
  Word.product [Word.inverse w.k, w.f, w.k]

def x1 (w : BaseWords n) : Word n :=
  Word.product [Word.inverse w.a, w.x, w.a]

def h (w : BaseWords n) : Word n :=
  Word.product [Word.inverse (Word.pow w.a 2), w.x, Word.pow w.a 2]

def s1 (w : BaseWords n) : Word n :=
  Word.product [w.f, w.x1, Word.inverse w.f]

def s2 (w : BaseWords n) : Word n :=
  Word.product [w.f, Word.inverse w.h, Word.inverse w.x1, w.h, Word.inverse w.f]

def t (w : BaseWords n) : Word n :=
  Word.product [w.f, Word.inverse w.h, w.f, w.h]

def ell (w : BaseWords n) : Word n :=
  Word.product [w.b, w.c, Word.inverse w.b]

/-- The words for the two prepared input generators, in their fixed order. -/
def u (w : BaseWords n) : Fin 2 → Word n :=
  ![Word.product [Word.pow w.b 2, w.c, Word.inverse (Word.pow w.b 2)],
    Word.product [Word.inverse w.b, w.c, w.b]]

def positive (w : BaseWords n) (v : List (Fin 2)) : Word n :=
  Word.substitutePositive w.s1 w.s2 v

def T (w : BaseWords n) (datum : CodeWords) : Word n :=
  Word.product [w.positive datum.P, w.t, Word.inverse w.f,
    Word.inverse (w.positive datum.P), w.f]

end BaseWords

/-- Core rows 7 and 8: the relations attaching the prepared input generators. -/
def inputRelator (datum : CodeWords) (w : BaseWords n) (i : Fin 2) : Word n :=
  Word.relation
    (Word.product [w.positive (datum.code i), w.ell])
    (Word.product [w.ell, w.positive (datum.code i), w.f, w.u i, Word.inverse w.f])

/-- Core rows 9 and 10. -/
def inputCommutator (datum : CodeWords) (w : BaseWords n) (i : Fin 2) : Word n :=
  Word.commutator w.ell
    (Word.product [Word.inverse w.k, w.positive (datum.code i), w.k])

/-- The actual generators of the six-generator stage are `c,d,f,k,a,b`. -/
def baseWords : BaseWords 6 where
  c := Word.generator 0
  d := Word.generator 1
  f := Word.generator 2
  k := Word.generator 3
  a := Word.generator 4
  b := Word.generator 5

end UniversalGroup
