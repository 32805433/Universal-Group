module

public import UniversalGroup.Higman.EffectiveEmbedding.HNN

@[expose] public section

/-! Explicit, primitive recursive defining words for the countable HNN embedding. -/
namespace UniversalGroup.EffectiveEmbeddingWords

abbrev RawWord := List (ℕ × Bool)
def shiftWord (w : RawWord) : RawWord := w.map fun l => (l.1+3,l.2)
def leftWord (i : ℕ) : RawWord :=
  List.replicate i (1,false) ++ [(0,true)] ++ List.replicate i (1,true)
def rightInvWord : ℕ → RawWord
  | 0 => [(1,false)]
  | j+1 => List.replicate (j+1) (0,false) ++ [(1,false)] ++
      List.replicate (j+1) (0,true) ++ [(j+3,false)]
def hnnWord (i : ℕ) : RawWord := [(2,false)] ++ leftWord i ++ [(2,true)] ++ rightInvWord i

theorem shiftWord_primrec : Primrec shiftWord :=
  Primrec.list_map Primrec.id
    (((Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 3)).pair
      (Primrec.snd.comp Primrec.snd)).to₂)

theorem replicate_primrec (l : ℕ × Bool) : Primrec (fun i : ℕ => List.replicate i l) := by
  exact (Primrec.list_map Primrec.list_range (Primrec.const l).to₂).of_eq (by intro i; simp)

theorem leftWord_primrec : Primrec leftWord :=
  Primrec.list_append.comp
    (Primrec.list_append.comp (replicate_primrec (1,false)) (Primrec.const [(0,true)]))
    (replicate_primrec (1,true))

theorem rightInvWord_primrec : Primrec rightInvWord := by
  have h : Primrec (fun j : ℕ => List.replicate (j+1) (0,false) ++ [(1,false)] ++
      List.replicate (j+1) (0,true) ++ [(j+3,false)]) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp ((replicate_primrec (0,false)).comp Primrec.succ)
          (Primrec.const [(1,false)]))
        ((replicate_primrec (0,true)).comp Primrec.succ))
      (Primrec.list_cons.comp
        ((Primrec.nat_add.comp Primrec.id (Primrec.const 3)).pair (Primrec.const false))
        (Primrec.const []))
  exact (Primrec.nat_casesOn Primrec.id (Primrec.const [(1,false)])
    (h.comp Primrec.snd).to₂).of_eq (by intro i; cases i <;> rfl)

theorem hnnWord_primrec : Primrec hnnWord :=
  Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.const [(2,false)]) leftWord_primrec)
      (Primrec.const [(2,true)])) rightInvWord_primrec

variable {H : Type*} [Group H]
def eval (f : ℕ → H) (w : RawWord) : H := FreeGroup.lift f (FreeGroup.mk w)

@[simp] theorem eval_nil (f : ℕ → H) : eval f []=1 := rfl
@[simp] theorem eval_cons (f : ℕ → H) (l : ℕ × Bool) (w : RawWord) :
    eval f (l::w) = (if l.2 then f l.1 else (f l.1)⁻¹) * eval f w := by
  cases l with | mk k s => cases s <;> simp [eval,FreeGroup.lift_mk]
@[simp] theorem eval_append (f : ℕ → H) (v w : RawWord) :
    eval f (v++w)=eval f v*eval f w := by simp [eval,FreeGroup.lift_mk]
@[simp] theorem eval_replicate (f : ℕ → H) (i : ℕ) (l : ℕ × Bool) :
    eval f (List.replicate i l) = (if l.2 then f l.1 else (f l.1)⁻¹)^i := by
  cases l with | mk k s => cases s <;> simp [eval,FreeGroup.lift_mk]

theorem eval_shiftWord (f : ℕ → H) (w : RawWord) :
    eval f (shiftWord w)=eval (fun i=>f (i+3)) w := by
  induction w with
  | nil => rfl
  | cons l w ih => simpa [shiftWord] using congrArg ((if l.2 then f (l.1+3) else (f (l.1+3))⁻¹)*·) ih

theorem eval_leftWord (f : ℕ → H) (i : ℕ) :
    eval f (leftWord i)=(f 1^i)⁻¹*f 0*f 1^i := by
  simp [leftWord,←inv_pow,mul_assoc]
theorem eval_rightInvWord_zero (f : ℕ → H) : eval f (rightInvWord 0)=(f 1)⁻¹ := by
  simp [rightInvWord]
theorem eval_rightInvWord_succ (f : ℕ → H) (i : ℕ) :
    eval f (rightInvWord (i+1))=(f (i+3)*(f 0^(i+1))⁻¹*f 1*f 0^(i+1))⁻¹ := by
  simp [rightInvWord,←inv_pow,mul_assoc]

theorem eval_hnnWord_zero (f : ℕ → H) :
    eval f (hnnWord 0)=(f 2)⁻¹*f 0*f 2*(f 1)⁻¹ := by
  simp [hnnWord,eval_leftWord,eval_rightInvWord_zero,mul_assoc]
theorem eval_hnnWord_succ (f : ℕ → H) (i : ℕ) :
    eval f (hnnWord (i+1)) =
      (f 2)⁻¹*((f 1^(i+1))⁻¹*f 0*f 1^(i+1))*f 2*
        (f (i+3)*(f 0^(i+1))⁻¹*f 1*f 0^(i+1))⁻¹ := by
  simp [hnnWord,eval_leftWord,eval_rightInvWord_succ,mul_assoc]

end UniversalGroup.EffectiveEmbeddingWords
