module

public import UniversalGroup.Embedding.PositiveHost.InputEmbedding
public import UniversalGroup.Embedding.PositiveHost.Source
public import UniversalGroup.Embedding.PositiveHost.Target

@[expose] public section

/-!
# The concrete attaching maps in the positive nineteen-relator host

The source bases are `(c,d)` and `(f,k,h²)`. The target bases are `(a,x)`
and `(A,B,b)`, where `B = cbc⁻¹` and `A = Bc³B⁻¹`. All twelve cross
commutations and all ten basis images follow from the displayed nineteen
relators, independently of any embedding claim.

The faithful positive extension tower proves the marked input embedding.
A detecting quotient separates the source factors; the proper row HNN and
column product transfer the protected rank-three subgroup into the target.
The resulting model injections certify these exact presentation maps.
-/

namespace UniversalGroup.Embedding

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

namespace PositiveBase

variable (D : CodeWords)

abbrev Host := (positiveBasePresentation D).Group

def c : Host D := generators (positiveBasePresentation D) 0
def d : Host D := generators (positiveBasePresentation D) 1
def f : Host D := generators (positiveBasePresentation D) 2
def k : Host D := generators (positiveBasePresentation D) 3
def a : Host D := generators (positiveBasePresentation D) 4
def b : Host D := generators (positiveBasePresentation D) 5
def x : Host D := (k D)⁻¹ * f D * k D
def h : Host D := (a D ^ 2)⁻¹ * x D * a D ^ 2

@[simp] theorem eval_x : (positiveBasePresentation D).evalWord baseWords.x = x D := by
  simp [FP.evalWord, BaseWords.x, baseWords, x, k, f, generators, mul_assoc]

@[simp] theorem eval_h2 :
    (positiveBasePresentation D).evalWord (Word.pow baseWords.h 2) = h D ^ 2 := by
  simp [FP.evalWord, BaseWords.h, BaseWords.x, baseWords, h, x, a, k, f, generators, mul_assoc]

@[simp] theorem eval_A :
    (positiveBasePresentation D).evalWord (swapA baseWords) = rowA (c D) (b D) := by
  simp [FP.evalWord, baseWords, c, b, generators]

@[simp] theorem eval_B :
    (positiveBasePresentation D).evalWord (swapB baseWords) = rowB (c D) (b D) := by
  simp [FP.evalWord, baseWords, c, b, generators]

private theorem commutator_iff (v : Fin n → Host D) (u w : Word n) :
    Word.eval v (Word.commutator u w) = 1 ↔
      Commute (Word.eval v u) (Word.eval v w) := by
  rw [Word.eval_commutator, mul_assoc, mul_assoc, inv_mul_eq_one,
    eq_inv_mul_iff_mul_eq, commute_iff_eq]
  exact eq_comm

private theorem displayed_commutation (i : Fin 19) (u w : Word 6)
    (hi : (positiveBasePresentation D).relator i = Word.commutator u w) :
    Commute ((positiveBasePresentation D).evalWord u)
      ((positiveBasePresentation D).evalWord w) := by
  apply (commutator_iff D _ _ _).mp
  rw [← hi]
  exact (positiveBasePresentation D).relator_eq_one i

/-- The seven explicit cross-commutators at the end of the literal table. -/
theorem basic_commutations :
    Commute (c D) (f D) ∧ Commute (d D) (f D) ∧
    Commute (c D) (k D) ∧ Commute (d D) (k D) ∧
    Commute (c D) (a D) ∧ Commute (a D) (b D) ∧ Commute (b D) (x D) := by
  have hh := And.intro (displayed_commutation D 12 _ _ (by rfl))
      (And.intro (displayed_commutation D 13 _ _ (by rfl))
      (And.intro (displayed_commutation D 14 _ _ (by rfl))
      (And.intro (displayed_commutation D 15 _ _ (by rfl))
      (And.intro (displayed_commutation D 16 _ _ (by rfl))
      (And.intro (displayed_commutation D 17 _ _ (by rfl))
        (displayed_commutation D 18 _ _ (by rfl)))))))
  simpa [FP.evalWord, baseWords, c, d, f, k, a, b, x, BaseWords.x, generators, mul_assoc] using hh

theorem c_x : Commute (c D) (x D) := by
  obtain ⟨hcf, _, hck, _⟩ := basic_commutations D
  exact (hck.inv_right.mul_right hcf).mul_right hck

theorem c_h2 : Commute (c D) (h D ^ 2) := by
  have hca := (basic_commutations D).2.2.2.2.1
  exact (((hca.pow_right 2).inv_right.mul_right (c_x D)).mul_right
    (hca.pow_right 2)).pow_right 2

/-- Row ten supplies the positive-sign relation `[d,h²] = 1`. -/
theorem d_h2 : Commute (d D) (h D ^ 2) := by
  have hh := displayed_commutation D 10 baseWords.d (Word.pow baseWords.h 2) (by rfl)
  simpa [FP.evalWord, baseWords, BaseWords.h, BaseWords.x, d, h, a, x, f, k,
    generators, mul_assoc] using hh

end PositiveBase

private theorem commute_free_lifts {H : Type*} [Group H]
    {α β : Type*} (x : α → H) (y : β → H)
    (h : ∀ i j, Commute (x i) (y j)) (u : FreeGroup α) (v : FreeGroup β) :
    Commute (FreeGroup.lift x u) (FreeGroup.lift y v) := by
  have hgen (i : α) (w : FreeGroup β) : Commute (x i) (FreeGroup.lift y w) := by
    induction w using FreeGroup.induction_on with
    | one => simp
    | of j => simpa using h i j
    | inv_of j hj => simpa only [map_inv] using hj.inv_right
    | mul w z hw hz => simpa only [map_mul] using hw.mul_right hz
  induction u using FreeGroup.induction_on with
  | one => simp
  | of i => simpa using hgen i v
  | inv_of i hi => simpa only [map_inv] using hi.inv_left
  | mul w z hw hz => simpa only [map_mul] using hw.mul_left hz

def positiveSourceFirst (D : CodeWords) : FreeGroup (Fin 2) →* (positiveBasePresentation D).Group :=
  FreeGroup.lift ![PositiveBase.c D, PositiveBase.d D]

def positiveSourceSecond (D : CodeWords) : FreeGroup (Fin 3) →* (positiveBasePresentation D).Group :=
  FreeGroup.lift ![PositiveBase.f D, PositiveBase.k D, PositiveBase.h D ^ 2]

def positiveTargetFirst (D : CodeWords) : FreeGroup (Fin 2) →* (positiveBasePresentation D).Group :=
  FreeGroup.lift ![PositiveBase.a D, PositiveBase.x D]

def positiveTargetSecond (D : CodeWords) : FreeGroup (Fin 3) →* (positiveBasePresentation D).Group :=
  FreeGroup.lift ![rowA (PositiveBase.c D) (PositiveBase.b D),
    rowB (PositiveBase.c D) (PositiveBase.b D), PositiveBase.b D]

theorem positiveSource_commute (D : CodeWords) (u : FreeGroup (Fin 2)) (v : FreeGroup (Fin 3)) :
    Commute (positiveSourceFirst D u) (positiveSourceSecond D v) := by
  apply commute_free_lifts
  intro i j
  obtain ⟨hcf, hdf, hck, hdk, _⟩ := PositiveBase.basic_commutations D
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact hcf
  · exact hck
  · exact PositiveBase.c_h2 D
  · exact hdf
  · exact hdk
  · exact PositiveBase.d_h2 D

theorem positiveTarget_commute (D : CodeWords) (u : FreeGroup (Fin 2)) (v : FreeGroup (Fin 3)) :
    Commute (positiveTargetFirst D u) (positiveTargetSecond D v) := by
  apply commute_free_lifts
  intro i j
  obtain ⟨_, _, _, _, hca, hab, hbx⟩ := PositiveBase.basic_commutations D
  have hxc := (PositiveBase.c_x D).symm
  have haB : Commute (PositiveBase.a D) (rowB (PositiveBase.c D) (PositiveBase.b D)) :=
    (hca.symm.mul_right hab).mul_right hca.symm.inv_right
  have hxB : Commute (PositiveBase.x D) (rowB (PositiveBase.c D) (PositiveBase.b D)) :=
    (hxc.mul_right hbx.symm).mul_right hxc.inv_right
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact (haB.mul_right (hca.symm.pow_right 3)).mul_right haB.inv_right
  · exact haB
  · exact hab
  · exact (hxB.mul_right (hxc.pow_right 3)).mul_right hxB.inv_right
  · exact hxB
  · exact hbx.symm

/-- The specified source product map on `(c,d;f,k,h²)`. -/
def positiveSource (D : CodeWords) : FactorSwapDomain →* (positiveBasePresentation D).Group :=
  (positiveSourceFirst D).noncommCoprod (positiveSourceSecond D) (positiveSource_commute D)

/-- The specified target product map on `(a,x;A,B,b)`. -/
def positiveTarget (D : CodeWords) : FactorSwapDomain →* (positiveBasePresentation D).Group :=
  (positiveTargetFirst D).noncommCoprod (positiveTargetSecond D) (positiveTarget_commute D)

@[simp] theorem positiveSource_c (D : CodeWords) :
    positiveSource D (factorFirst 0) = generators (positiveBasePresentation D) 0 := by
  simp [positiveSource, positiveSourceFirst, positiveSourceSecond, factorFirst, PositiveBase.c]

@[simp] theorem positiveSource_d (D : CodeWords) :
    positiveSource D (factorFirst 1) = generators (positiveBasePresentation D) 1 := by
  simp [positiveSource, positiveSourceFirst, positiveSourceSecond, factorFirst, PositiveBase.d]

@[simp] theorem positiveSource_f (D : CodeWords) :
    positiveSource D (factorSecond 0) = generators (positiveBasePresentation D) 2 := by
  simp [positiveSource, positiveSourceFirst, positiveSourceSecond, factorSecond, PositiveBase.f]

@[simp] theorem positiveSource_k (D : CodeWords) :
    positiveSource D (factorSecond 1) = generators (positiveBasePresentation D) 3 := by
  simp [positiveSource, positiveSourceFirst, positiveSourceSecond, factorSecond, PositiveBase.k]

@[simp] theorem positiveSource_h2 (D : CodeWords) :
    positiveSource D (factorSecond 2) =
      (positiveBasePresentation D).evalWord (Word.pow baseWords.h 2) := by
  simp [positiveSource, positiveSourceFirst, positiveSourceSecond, factorSecond]

@[simp] theorem positiveTarget_a (D : CodeWords) :
    positiveTarget D (factorFirst 0) = generators (positiveBasePresentation D) 4 := by
  simp [positiveTarget, positiveTargetFirst, positiveTargetSecond, factorFirst, PositiveBase.a]

@[simp] theorem positiveTarget_x (D : CodeWords) :
    positiveTarget D (factorFirst 1) = (positiveBasePresentation D).evalWord baseWords.x := by
  rw [PositiveBase.eval_x]
  simp [positiveTarget, positiveTargetFirst, positiveTargetSecond, factorFirst]

@[simp] theorem positiveTarget_A (D : CodeWords) :
    positiveTarget D (factorSecond 0) = (positiveBasePresentation D).evalWord (swapA baseWords) := by
  simp [positiveTarget, positiveTargetFirst, positiveTargetSecond, factorSecond]

@[simp] theorem positiveTarget_B (D : CodeWords) :
    positiveTarget D (factorSecond 1) = (positiveBasePresentation D).evalWord (swapB baseWords) := by
  simp [positiveTarget, positiveTargetFirst, positiveTargetSecond, factorSecond]

@[simp] theorem positiveTarget_b (D : CodeWords) :
    positiveTarget D (factorSecond 2) = generators (positiveBasePresentation D) 5 := by
  simp [positiveTarget, positiveTargetFirst, positiveTargetSecond, factorSecond, PositiveBase.b]

set_option backward.isDefEq.respectTransparency false in
/-- The specified source product embeds, including its third generator `h²`. -/
theorem positive_source_injective (G : PreparedInput) (D : ValievDatum G)
    (hi : ValievIntersections G D) : Function.Injective (positiveSource D.toCodeWords) := by
  let s := (PositiveHost.BaseModel.hom G D hi).comp (positiveSource D.toCodeWords)
  have hs : Function.Injective s := by
    apply PositiveHost.Source.injective_of_coordinates G D hi
    · intro i
      change PositiveHost.BaseModel.hom G D hi (positiveSource D.toCodeWords (factorFirst i)) = _
      fin_cases i
      · exact (congrArg (PositiveHost.BaseModel.hom G D hi) (positiveSource_c D.toCodeWords)).trans
          (PositiveHost.BaseModel.hom_generator G D hi 0)
      · exact (congrArg (PositiveHost.BaseModel.hom G D hi) (positiveSource_d D.toCodeWords)).trans
          (PositiveHost.BaseModel.hom_generator G D hi 1)
    · intro i
      change PositiveHost.BaseModel.hom G D hi (positiveSource D.toCodeWords (factorSecond i)) = _
      fin_cases i
      · exact (congrArg (PositiveHost.BaseModel.hom G D hi) (positiveSource_f D.toCodeWords)).trans
          (PositiveHost.BaseModel.hom_generator G D hi 2)
      · exact (congrArg (PositiveHost.BaseModel.hom G D hi) (positiveSource_k D.toCodeWords)).trans
          (PositiveHost.BaseModel.hom_generator G D hi 3)
      · change PositiveHost.BaseModel.hom G D hi (positiveSource D.toCodeWords (factorSecond 2)) =
          PositiveHost.BaseModel.h G D hi ^ 2
        rw [positiveSource_h2, PositiveHost.BaseModel.hom_evalWord]
        simpa only [PositiveHost.BaseModelLaws.value_pow] using
          congrArg (fun z => z ^ 2) (PositiveHost.BaseModel.value_h G D hi)
  intro x y hxy
  exact hs (congrArg (PositiveHost.BaseModel.hom G D hi) hxy)

set_option backward.isDefEq.respectTransparency false in
/-- Transfer the protected row triple through
the full product at the positive host's final `b` extension. -/
theorem positive_target_injective (G : PreparedInput) (D : ValievDatum G)
    (hi : ValievIntersections G D) (hp : ProtectedRowTriple G) :
    Function.Injective (positiveTarget D.toCodeWords) := by
  have he : (PositiveHost.BaseModel.hom G D hi).comp (positiveTarget D.toCodeWords) =
      PositiveHost.Target.product G D hi := by
    apply PositiveHost.Source.hom_ext
    · intro i
      change PositiveHost.BaseModel.hom G D hi (positiveTarget D.toCodeWords (factorFirst i)) =
        PositiveHost.Target.product G D hi (factorFirst i)
      rw [PositiveHost.Target.product_first]
      fin_cases i
      · exact (congrArg (PositiveHost.BaseModel.hom G D hi) (positiveTarget_a D.toCodeWords)).trans
          (PositiveHost.BaseModel.hom_generator G D hi 4)
      · exact (congrArg (PositiveHost.BaseModel.hom G D hi) (positiveTarget_x D.toCodeWords)).trans
          ((PositiveHost.BaseModel.hom_evalWord G D hi baseWords.x).trans
            (PositiveHost.BaseModelLaws.value_x _ _ _ _))
    · intro i
      change PositiveHost.BaseModel.hom G D hi (positiveTarget D.toCodeWords (factorSecond i)) =
        PositiveHost.Target.product G D hi (factorSecond i)
      rw [PositiveHost.Target.product_second]
      fin_cases i
      · refine (congrArg (PositiveHost.BaseModel.hom G D hi)
          ((positiveTarget_A D.toCodeWords).trans (PositiveBase.eval_A D.toCodeWords))).trans ?_
        simpa only [rowA, rowB, map_mul, map_pow, map_inv, PositiveBase.c, PositiveBase.b,
          Matrix.cons_val, Matrix.cons_val_zero'] using
          congrArg₂ rowA (PositiveHost.BaseModel.hom_generator G D hi 0)
            (PositiveHost.BaseModel.hom_generator G D hi 5)
      · refine (congrArg (PositiveHost.BaseModel.hom G D hi)
          ((positiveTarget_B D.toCodeWords).trans (PositiveBase.eval_B D.toCodeWords))).trans ?_
        simpa only [rowB, map_mul, map_inv, PositiveBase.c, PositiveBase.b, Matrix.cons_val,
          Matrix.cons_val_succ', Matrix.cons_val_zero'] using
          congrArg₂ rowB (PositiveHost.BaseModel.hom_generator G D hi 0)
            (PositiveHost.BaseModel.hom_generator G D hi 5)
      · exact (congrArg (PositiveHost.BaseModel.hom G D hi) (positiveTarget_b D.toCodeWords)).trans
          (PositiveHost.BaseModel.hom_generator G D hi 5)
  intro x y hxy
  apply PositiveHost.Target.product_injective G D hi hp
  simpa only [← MonoidHom.comp_apply, he] using congrArg (PositiveHost.BaseModel.hom G D hi) hxy

/-- All factor-swap coordinates are proved; only the two precisely specified
injectivity theorems enter this constructor. -/
theorem positive_factorSwapData (G : PreparedInput) (D : ValievDatum G)
    (hi : ValievIntersections G D) (hp : ProtectedRowTriple G) :
    Nonempty (FactorSwapData D.toCodeWords) := by
  exact ⟨{
    left := positiveSource D.toCodeWords
    right := positiveTarget D.toCodeWords
    left_injective := positive_source_injective G D hi
    right_injective := positive_target_injective G D hi hp
    left_c := positiveSource_c D.toCodeWords
    left_d := positiveSource_d D.toCodeWords
    left_f := positiveSource_f D.toCodeWords
    left_k := positiveSource_k D.toCodeWords
    left_h2 := positiveSource_h2 D.toCodeWords
    right_a := positiveTarget_a D.toCodeWords
    right_x := positiveTarget_x D.toCodeWords
    right_A := positiveTarget_A D.toCodeWords
    right_B := positiveTarget_B D.toCodeWords
    right_b := positiveTarget_b D.toCodeWords }⟩

end UniversalGroup.Embedding
