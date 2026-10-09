module

public import UniversalGroup.Host.Words
public import UniversalGroup.Embedding.CompressionIdentities

@[expose] public section

/-!
# Literal presentations for the positive-sign factor swap

The six-generator host has nineteen rows. Its positive symmetry uses
`e = f h⁻¹ d h f⁻¹` and `[d,h²] = 1`. The final table retains thirteen
specified rows after substituting words in the two actual letters `c,r`.
-/

namespace UniversalGroup.Embedding

/-- Positive-sign recovery of the simulator letter `e`. -/
def positiveE (w : BaseWords n) : Word n :=
  Word.product [w.f, Word.inverse w.h, w.d, w.h, Word.inverse w.f]

def swapB (w : BaseWords n) : Word n :=
  Word.product [w.c, w.b, Word.inverse w.c]

def swapA (w : BaseWords n) : Word n :=
  Word.product [swapB w, Word.pow w.c 3, Word.inverse (swapB w)]

def positiveRewritingRelator (D : CodeWords) (w : BaseWords n) (i : Fin 3) : Word n :=
  Word.relation
    (Word.product [Word.inverse (Word.pow w.d (i.val + 1)), w.c,
      Word.pow w.d (i.val + 1), w.positive (D.E i)])
    (Word.product [w.positive (D.F i), Word.pow (positiveE w) (i.val + 1),
      w.c, Word.inverse (Word.pow (positiveE w) (i.val + 1))])

/-- The twelve core rows; row ten, indexed from zero, is the positive symmetry. -/
def positiveCoreRelators (D : CodeWords) (w : BaseWords n) : Fin 12 → Word n :=
  ![Word.relation (Word.product [Word.pow w.d 4, w.s1])
      (Word.product [w.s1, w.d]),
    Word.relation (Word.product [positiveE w, w.s1])
      (Word.product [w.s1, Word.pow (positiveE w) 4]),
    positiveRewritingRelator D w 0,
    positiveRewritingRelator D w 1,
    positiveRewritingRelator D w 2,
    Word.commutator (w.T D) w.k,
    inputRelator D w 0,
    inputRelator D w 1,
    inputCommutator D w 0,
    inputCommutator D w 1,
    Word.commutator w.d (Word.pow w.h 2),
    Word.relation (Word.product [w.positive D.P, w.t])
      (Word.product [Word.inverse (Word.pow w.a 3), w.x, Word.pow w.a 3])]

/-- The positive host, with actual generators `c,d,f,k,a,b`. -/
def positiveBasePresentation (D : CodeWords) : FP 6 19 where
  relator := Fin.append (positiveCoreRelators D baseWords)
    ![Word.commutator baseWords.c baseWords.f,
      Word.commutator baseWords.d baseWords.f,
      Word.commutator baseWords.c baseWords.k,
      Word.commutator baseWords.d baseWords.k,
      Word.commutator baseWords.c baseWords.a,
      Word.commutator baseWords.a baseWords.b,
      Word.commutator baseWords.b baseWords.x]

/-- Ordered recovery of all six old letters using only `c,r`. -/
def thirteenWords : BaseWords 2 :=
  let c := Word.generator 0
  let r := Word.generator 1
  let a := Word.product [Word.inverse r, c, r]
  let J := Word.product [Word.inverse (Word.pow r 2), Word.pow c 2, Word.pow r 2]
  let b := Word.product [Word.inverse J, Word.pow c 6, J]
  let B := Word.product [c, b, Word.inverse c]
  { c := c
    d := Word.product [Word.pow r 2, Word.pow c 3, Word.inverse (Word.pow r 2)]
    f := Word.product [r, B, Word.pow c 3, Word.inverse B, Word.inverse r]
    k := Word.product [r, B, Word.inverse r]
    a := a
    b := b }

def thirteenSubstitution : Fin 6 → Word 2 :=
  ![thirteenWords.c, thirteenWords.d, thirteenWords.f,
    thirteenWords.k, thirteenWords.a, thirteenWords.b]

/-- The retained rows are the first ten core rows, the last core row,
`[c,a]`, and `[b,x]`. The six other rows will be derived algebraically. -/
def thirteenRelatorIndex : Fin 13 → Fin 19 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 16, 18]

def thirteenPresentation (D : CodeWords) : FP 2 13 where
  relator i := Word.substitute thirteenSubstitution
    ((positiveBasePresentation D).relator (thirteenRelatorIndex i))

theorem thirteenPresentation_relator (D : CodeWords) (i : Fin 13) :
    (thirteenPresentation D).relator i = Word.substitute thirteenSubstitution
      ((positiveBasePresentation D).relator (thirteenRelatorIndex i)) := rfl

section Evaluation

variable {G : Type*} [Group G]

@[simp] theorem eval_swapB (v : Fin n → G) (w : BaseWords n) :
    Word.eval v (swapB w) = rowB (Word.eval v w.c) (Word.eval v w.b) := by
  simp [swapB, rowB, mul_assoc]

@[simp] theorem eval_swapA (v : Fin n → G) (w : BaseWords n) :
    Word.eval v (swapA w) = rowA (Word.eval v w.c) (Word.eval v w.b) := by
  simp [swapA, rowA, mul_assoc]

@[simp] theorem eval_thirteen_c (c r : G) :
    Word.eval ![c,r] thirteenWords.c = c := by simp [thirteenWords]

@[simp] theorem eval_thirteen_a (c r : G) :
    Word.eval ![c,r] thirteenWords.a = r⁻¹ * c * r := by simp [thirteenWords, mul_assoc]

@[simp] theorem eval_thirteen_b (c r : G) :
    Word.eval ![c,r] thirteenWords.b = finalB c r := by
  simp [thirteenWords, finalB, finalJ, mul_assoc]

@[simp] theorem eval_thirteen_k (c r : G) :
    Word.eval ![c,r] thirteenWords.k = r * rowB c (finalB c r) * r⁻¹ := by
  simp [thirteenWords, rowB, finalB, finalJ, mul_assoc]

@[simp] theorem eval_thirteen_f (c r : G) :
    Word.eval ![c,r] thirteenWords.f = r * rowA c (finalB c r) * r⁻¹ := by
  simp [thirteenWords, rowA, rowB, finalB, finalJ, mul_assoc]

@[simp] theorem eval_thirteen_d (c r : G) :
    Word.eval ![c,r] thirteenWords.d = r ^ 2 * c ^ 3 * (r ^ 2)⁻¹ := by
  simp [thirteenWords, mul_assoc]

/-- The word `k⁻¹ f k` simplifies before the fifth elimination is used. -/
theorem eval_thirteen_x (c r : G) :
    Word.eval ![c,r] thirteenWords.x = r * c ^ 3 * r⁻¹ := by
  simp only [BaseWords.x, Word.eval_product, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, Word.eval_inverse,
    eval_thirteen_k, eval_thirteen_f, rowA]
  group

/-- All five HNN equations hold identically under the ordered substitutions. -/
theorem eval_factor_swap_equations (c r : G) :
    r⁻¹ * Word.eval ![c,r] thirteenWords.c * r = Word.eval ![c,r] thirteenWords.a ∧
    r⁻¹ * Word.eval ![c,r] thirteenWords.d * r = Word.eval ![c,r] thirteenWords.x ∧
    r⁻¹ * Word.eval ![c,r] thirteenWords.f * r = Word.eval ![c,r] (swapA thirteenWords) ∧
    r⁻¹ * Word.eval ![c,r] thirteenWords.k * r = Word.eval ![c,r] (swapB thirteenWords) ∧
    r⁻¹ * (Word.eval ![c,r] thirteenWords.h) ^ 2 * r =
      Word.eval ![c,r] thirteenWords.b := by
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · rw [eval_thirteen_d, eval_thirteen_x]
    simp only [pow_two]
    group
  · simp [mul_assoc]
  · simp [mul_assoc]
  · simp only [BaseWords.h, Word.eval_product, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, Word.eval_inverse, Word.eval_pow,
      eval_thirteen_x, eval_thirteen_a, eval_thirteen_b, finalB, finalJ, pow_two]
    group
    simp only [zpow_two, mul_assoc]

end Evaluation

end UniversalGroup.Embedding
