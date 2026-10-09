module

public import UniversalGroup.Coding.BooneCollins.Words
public import UniversalGroup.Simulator.Codes.Cancellation
public import Mathlib.Data.Int.ConditionallyCompleteOrder

@[expose] public section

/-! Nielsen reduction and positivity for the complete Boone–Collins alphabet. -/
namespace UniversalGroup.HigmanCode
noncomputable section
set_option maxHeartbeats 1200000
open CodeSubgroups

abbrev Letter := Fin 2 × Bool
abbrev SourceLetter (r : ℕ) := Fin r × Bool
abbrev pos := CodeCancellation.positiveLetters
abbrev neg := CodeCancellation.negativeLetters
def stem : PositiveWord := [0,1,0,1,0,0]
def suffix (k : ℕ) : PositiveWord := [0] ++ List.replicate k 1
def code (r : ℕ) : FreeGroup (Fin r) →* FreeGroup (Fin 2) :=
  FreeGroup.lift (fun i=>positiveFree (BooneCollinsWords.chiLetter r i))

def run (z : ℤ) : List Letter :=
  if 0 ≤ z then List.replicate z.toNat (0,true)
  else List.replicate (-z).toNat (0,false)

theorem run_nonempty (z : ℤ) (hz : z≠0) : run z≠[] := by
  simp only [run]
  split_ifs with h
  · have : 0<z.toNat := by omega
    simpa using this.ne'
  · have : 0<(-z).toNat := by omega
    simpa using this.ne'
theorem run_letters (z : ℤ) (l : Letter) (hl : l∈run z) : l.1=0 := by
  unfold run at hl
  split_ifs at hl <;> obtain ⟨_,rfl⟩ := List.mem_replicate.mp hl <;> rfl

theorem reduced_sign (w : List Letter) (s : Bool) (h : ∀ l∈w,l.2=s) : FreeGroup.IsReduced w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [FreeGroup.IsReduced,List.isChain_cons]
    refine ⟨?_,ih (fun b hb=>h b (by simp [hb]))⟩
    intro b hb _
    exact (h a (by simp)).trans (h b (List.mem_cons_of_mem _ (List.mem_of_mem_head? hb))).symm
theorem pos_sign (w : PositiveWord) (l : Letter) (hl : l∈pos w) : l.2=true := by
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp hl
  rfl
theorem neg_sign (w : PositiveWord) (l : Letter) (hl : l∈neg w) : l.2=false := by
  simp only [CodeCancellation.negativeLetters,FreeGroup.invRev,List.mem_reverse,List.mem_map] at hl
  obtain ⟨a,ha,rfl⟩:=hl
  simp [pos_sign w a ha]
theorem pos_reduced (w : PositiveWord) : FreeGroup.IsReduced (pos w) := reduced_sign _ _ (pos_sign w)
theorem run_reduced (z : ℤ) : FreeGroup.IsReduced (run z) := by
  unfold run
  split_ifs
  · exact reduced_sign _ true (by simp)
  · exact reduced_sign _ false (by simp)

def endNegative : ℕ → List Letter
  | 0 => [(0,false),(0,false),(1,false),(0,false),(1,false)]
  | k+1 => [(0,false),(0,false),(1,false),(0,false)] ++ pos (List.replicate k 1)
def ending (r k : ℕ) (a : SourceLetter r) : List Letter :=
  if a.2 then pos (List.replicate (r-a.1.val) 0 ++ suffix k)
  else neg (List.replicate a.1.val 0) ++ endNegative k
def start (r : ℕ) (a : SourceLetter r) : List Letter :=
  if a.2 then pos (stem ++ List.replicate a.1.val 0)
  else neg (List.replicate (r-a.1.val) 0)
def gap (r : ℕ) (a b : SourceLetter r) : List Letter :=
  if a.2=b.2 then
    if a.2 then pos (List.replicate (r-a.1.val) 0 ++ stem ++ List.replicate b.1.val 0)
    else neg (List.replicate (r-b.1.val) 0 ++ stem ++ List.replicate a.1.val 0)
  else run ((b.1.val:ℤ)-(a.1.val:ℤ))
def inner (r k : ℕ) (a : SourceLetter r) : List (SourceLetter r) → List Letter
  | [] => (1,a.2)::ending r k a
  | b::w => (1,a.2)::(gap r a b ++ inner r k b w)
def normal (r k : ℕ) : List (SourceLetter r) → List Letter
  | [] => pos (suffix k)
  | a::w => start r a ++ inner r k a w

@[simp] theorem inner_head (r k : ℕ) (a : SourceLetter r) (w : List (SourceLetter r)) :
    (inner r k a w).head?=some (1,a.2) := by cases w <;> rfl

theorem prepend_sign (L R : List Letter) (s : Bool)
    (hL : ∀ a∈L,a.2=s) (hR : FreeGroup.IsReduced R)
    (hh : ∀ a∈R.head?,a.2=s) : FreeGroup.IsReduced (L++R) := by
  apply List.IsChain.append (reduced_sign L s hL) hR
  intro a ha b hb _
  exact (hL a (List.mem_of_mem_getLast? ha)).trans (hh b hb).symm

theorem endNegative_reduced (k : ℕ) : FreeGroup.IsReduced (endNegative k) := by
  cases k with
  | zero => exact reduced_sign _ false (by simp [endNegative])
  | succ k =>
    apply List.IsChain.append (reduced_sign _ false (by simp)) (pos_reduced _)
    intro a ha b hb hab
    simp only [List.getLast?_cons,Option.mem_some_iff] at ha
    subst a
    have hb' : b.1=1 := by
      have hm := List.mem_of_mem_head? hb
      simp only [pos,CodeCancellation.positiveLetters,List.map_replicate,List.mem_replicate] at hm
      exact congrArg Prod.fst hm.2
    simp [hb'] at hab

theorem inner_nil_reduced (r k : ℕ) (a : SourceLetter r) : FreeGroup.IsReduced (inner r k a []) := by
  rcases a with ⟨i,s⟩
  cases s
  · change FreeGroup.IsReduced ([(1,false)] ++ neg (List.replicate i.val 0) ++ endNegative k)
    apply prepend_sign _ _ false ?_ (endNegative_reduced k) ?_
    · intro l hl
      rcases List.mem_append.mp hl with hl|hl
      · exact congrArg Prod.snd (List.mem_singleton.mp hl)
      · exact neg_sign _ l hl
    · cases k <;> simp [endNegative]
  · exact pos_reduced ([1]++List.replicate (r-i.val) 0++suffix k)

theorem inner_reduced (r k : ℕ) (a : SourceLetter r) (w : List (SourceLetter r))
    (hw : FreeGroup.IsReduced (a::w)) : FreeGroup.IsReduced (inner r k a w) := by
  induction w generalizing a with
  | nil => exact inner_nil_reduced r k a
  | cons b w ih =>
    have hab := (FreeGroup.isReduced_cons_cons.mp hw).1
    have hb := ih b (FreeGroup.isReduced_cons_cons.mp hw).2
    change FreeGroup.IsReduced ([(1,a.2)] ++ gap r a b ++ inner r k b w)
    by_cases hs : a.2=b.2
    · apply prepend_sign _ _ a.2 ?_ hb ?_
      · intro l hl
        rcases List.mem_append.mp hl with hl|hl
        · exact congrArg Prod.snd (List.mem_singleton.mp hl)
        · simp only [gap,ite_eq_left hs] at hl
          cases ha : a.2
          · simp only [ha,Bool.false_eq_true,↓reduceIte] at hl
            exact neg_sign _ l hl
          · simp only [ha,↓reduceIte] at hl
            exact pos_sign _ l hl
      · simp [hs]
    · have hi : a.1≠b.1 := fun h=>hs (hab h)
      have hz : (b.1.val:ℤ)-(a.1.val:ℤ)≠0 := by
        intro h
        apply hi
        apply Fin.ext
        omega
      rw [gap,ite_eq_right hs]
      have hr := run_reduced ((b.1.val:ℤ)-(a.1.val:ℤ))
      have hn := run_nonempty _ hz
      have hm := run_letters ((b.1.val:ℤ)-(a.1.val:ℤ))
      have ht : FreeGroup.IsReduced (run ((b.1.val:ℤ)-(a.1.val:ℤ)) ++ inner r k b w) := by
        apply List.IsChain.append hr hb
        intro l hl q hq he
        have hl0 := hm l (List.mem_of_mem_getLast? hl)
        simp only [inner_head,Option.mem_some_iff] at hq
        subst q
        simp [hl0] at he
      rw [List.append_assoc]
      apply List.IsChain.append (by simp) ht
      intro l hl q hq he
      simp only [List.getLast?_singleton,Option.mem_some_iff] at hl
      subst l
      have hq' : q∈(run ((b.1.val:ℤ)-(a.1.val:ℤ))).head? := by
        cases he : run ((b.1.val:ℤ)-(a.1.val:ℤ)) with
        | nil => exact False.elim (hn he)
        | cons q' qs => simpa [he] using hq
      have hq0 := hm q (List.mem_of_mem_head? hq')
      simp [hq0] at he

theorem normal_reduced (r k : ℕ) (w : List (SourceLetter r)) (hw : FreeGroup.IsReduced w) :
    FreeGroup.IsReduced (normal r k w) := by
  cases w with
  | nil => exact pos_reduced _
  | cons a w =>
    apply prepend_sign _ _ a.2 ?_ (inner_reduced r k a w hw) ?_
    · intro l hl
      cases ha : a.2 <;> simp only [start,ha,Bool.false_eq_true,↓reduceIte] at hl
      · exact neg_sign _ l hl
      · exact pos_sign _ l hl
    · simp

theorem inner_signs (r k : ℕ) (a : SourceLetter r) (w : List (SourceLetter r))
    (h : ∀ l∈inner r k a w,l.2=true) : ∀ l∈a::w,l.2=true := by
  induction w generalizing a with
  | nil => simpa [inner] using h (1,a.2) (by simp [inner])
  | cons b w ih =>
    have ha : a.2=true := h (1,a.2) (by simp [inner])
    have hb := ih b (fun l hl=>h l (by simp only [inner,List.mem_cons,List.mem_append];exact Or.inr (Or.inr hl)))
    simpa only [List.mem_cons,forall_eq_or_imp] using And.intro ha hb

theorem normal_signs (r k : ℕ) (w : List (SourceLetter r))
    (h : ∀ l∈normal r k w,l.2=true) : ∀ l∈w,l.2=true := by
  cases w with
  | nil => simp
  | cons a w => exact inner_signs r k a w (fun l hl=>h l (List.mem_append_right _ hl))

def startValue (r : ℕ) (a : SourceLetter r) : FreeGroup (Fin 2) :=
  if a.2 then positiveFree stem * FreeGroup.of 0 ^ a.1.val
  else (FreeGroup.of 0 ^ (r-a.1.val))⁻¹
def endValue (r : ℕ) (a : SourceLetter r) : FreeGroup (Fin 2) :=
  if a.2 then FreeGroup.of 0 ^ (r-a.1.val)
  else (FreeGroup.of 0 ^ a.1.val)⁻¹ * (positiveFree stem)⁻¹
def central (a : Letter) : FreeGroup (Fin 2) := if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹

theorem mk_cons {α : Type*} (l : α×Bool) (w : List (α×Bool)) :
    FreeGroup.mk (l::w)=(if l.2 then FreeGroup.of l.1 else (FreeGroup.of l.1)⁻¹)*FreeGroup.mk w := by
  rw [show l::w=[l]++w from rfl,←FreeGroup.mul_mk]
  congr 1
  cases l with | mk i s => cases s <;> rfl

@[simp] theorem positiveFree_zeros (i : ℕ) :
    positiveFree (List.replicate i 0)=FreeGroup.of (0:Fin 2)^i := by
  simp [positiveFree,evalPositive]
@[simp] theorem positiveFree_ones (i : ℕ) :
    positiveFree (List.replicate i 1)=FreeGroup.of (1:Fin 2)^i := by
  simp [positiveFree,evalPositive]

theorem start_eval (r : ℕ) (a : SourceLetter r) : FreeGroup.mk (start r a)=startValue r a := by
  cases ha : a.2 <;> simp [start,startValue,ha]

theorem run_eval (z : ℤ) : FreeGroup.mk (run z)=FreeGroup.of (0:Fin 2)^z := by
  unfold run
  split_ifs with h
  · have he : List.replicate z.toNat ((0:Fin 2),true)=pos (List.replicate z.toNat 0) := by
      simp [pos,CodeCancellation.positiveLetters]
    rw [he]
    rw [CodeCancellation.mk_positiveLetters,positiveFree_zeros,←zpow_natCast,Int.toNat_of_nonneg h]
  · have hn : 0≤ -z := by omega
    have he : List.replicate (-z).toNat ((0:Fin 2),false)=neg (List.replicate (-z).toNat 0) := by
      simp [neg,CodeCancellation.negativeLetters,CodeCancellation.positiveLetters,FreeGroup.invRev]
    rw [he,CodeCancellation.mk_negativeLetters,positiveFree_zeros,←zpow_natCast,Int.toNat_of_nonneg hn]
    simp

theorem endNegative_eval (k : ℕ) :
    FreeGroup.mk (endNegative k)=(positiveFree stem)⁻¹*positiveFree (suffix k) := by
  cases k with
  | zero =>
    simp [endNegative,mk_cons,stem,suffix,CodeCancellation.positiveFree_cons,
      CodeCancellation.positiveFree_nil,←FreeGroup.one_eq_mk,mul_assoc]
  | succ k =>
    simp [endNegative,mk_cons,stem,suffix,
      CodeCancellation.positiveFree_cons,CodeCancellation.positiveFree_nil,pow_succ]
    group

theorem ending_eval (r k : ℕ) (a : SourceLetter r) :
    FreeGroup.mk (ending r k a)=endValue r a*positiveFree (suffix k) := by
  cases ha : a.2 <;> simp [ending,endValue,ha,←FreeGroup.mul_mk,endNegative_eval,mul_assoc]

theorem code_split (r : ℕ) (i : Fin r) :
    BooneCollinsWords.chiLetter r i = stem ++ List.replicate i.val 0 ++ [1] ++
      List.replicate (r-i.val) 0 := by
  rw [BooneCollinsWords.chiLetter_eq]
  rw [show i.val+2=2+i.val by omega,List.replicate_add]
  simp [stem,List.append_assoc]

theorem code_letter (r : ℕ) (a : SourceLetter r) :
    code r (FreeGroup.mk [a])=startValue r a*central (1,a.2)*endValue r a := by
  rcases a with ⟨i,s⟩
  cases s <;>
    simp [mk_cons,code,startValue,endValue,central,code_split,
      CodeCancellation.positiveFree_cons,mul_assoc]

theorem gap_eval (r : ℕ) (a b : SourceLetter r) :
    FreeGroup.mk (gap r a b)=endValue r a*startValue r b := by
  have hai : (a.1.val:ℤ)≤r := by exact_mod_cast a.1.isLt.le
  have hbi : (b.1.val:ℤ)≤r := by exact_mod_cast b.1.isLt.le
  rcases a with ⟨i,s⟩
  rcases b with ⟨j,t⟩
  cases s <;> cases t <;>
    simp only [gap,startValue,endValue,Bool.false_eq_true,
      Bool.true_eq_false,↓reduceIte,CodeCancellation.mk_positiveLetters,
      CodeCancellation.mk_negativeLetters,CodeCancellation.positiveFree_append,
      positiveFree_zeros,run_eval]
  · simp [mul_assoc]
  · group
  · simp only [←zpow_natCast,Int.natCast_sub i.isLt.le,Int.natCast_sub j.isLt.le]
    group
  · group

theorem inner_eval (r k : ℕ) (a : SourceLetter r) (w : List (SourceLetter r)) :
    FreeGroup.mk (inner r k a w)=(startValue r a)⁻¹ * code r (FreeGroup.mk (a::w)) *
      positiveFree (suffix k) := by
  induction w generalizing a with
  | nil =>
    rw [inner,mk_cons,ending_eval,code_letter]
    change central (1,a.2)*(endValue r a*positiveFree (suffix k))=_
    group
  | cons b w ih =>
    rw [inner,mk_cons,←FreeGroup.mul_mk,gap_eval,ih]
    rw [show a::b::w=[a]++(b::w) from rfl,←FreeGroup.mul_mk,map_mul,code_letter]
    change central (1,a.2)*((endValue r a*startValue r b)*
      ((startValue r b)⁻¹*code r (FreeGroup.mk (b::w))*positiveFree (suffix k)))=_
    group

theorem normal_eval (r k : ℕ) (w : List (SourceLetter r)) :
    FreeGroup.mk (normal r k w)=code r (FreeGroup.mk w)*positiveFree (suffix k) := by
  cases w with
  | nil => simp [normal,←FreeGroup.one_eq_mk]
  | cons a w =>
    rw [normal,←FreeGroup.mul_mk,start_eval,inner_eval]
    group

def positive {α : Type*} (w : List α) : FreeGroup α := FreeGroup.mk (w.map fun i=>(i,true))

@[simp] theorem positive_nil {α : Type*} : positive ([] : List α)=1 := rfl
@[simp] theorem positive_cons {α : Type*} (i : α) (w : List α) :
    positive (i::w)=FreeGroup.of i*positive w := by simp [positive,mk_cons]
@[simp] theorem positive_append {α : Type*} (u v : List α) :
    positive (u++v)=positive u*positive v := by simp [positive,←FreeGroup.mul_mk]

theorem positive_of_signs {α : Type*} [DecidableEq α] (g : FreeGroup α)
    (h : ∀ l∈g.toWord,l.2=true) : g=positive (g.toWord.map Prod.fst) := by
  apply (FreeGroup.mk_toWord (x:=g)).symm.trans
  change FreeGroup.mk g.toWord=FreeGroup.mk ((g.toWord.map Prod.fst).map fun i=>(i,true))
  congr 1
  simp only [List.map_map]
  conv_lhs => rw [←List.map_id g.toWord]
  apply List.map_congr_left
  intro a ha
  rcases a with ⟨i,b⟩
  simp only [id_eq,Function.comp_apply,Prod.mk.injEq,true_and]
  exact h (i,b) ha

@[simp] theorem code_positive (r : ℕ) (w : List (Fin r)) :
    code r (positive w)=positiveFree (BooneCollinsWords.chi r w) := by
  induction w with
  | nil => simp [BooneCollinsWords.chi]
  | cons i w ih =>
    rw [positive_cons,map_mul,ih]
    change code r (FreeGroup.of i)*positiveFree (BooneCollinsWords.chi r w)=
      positiveFree (BooneCollinsWords.chiLetter r i++BooneCollinsWords.chi r w)
    rw [show code r (FreeGroup.of i)=positiveFree (BooneCollinsWords.chiLetter r i) from
      FreeGroup.lift_apply_of,CodeCancellation.positiveFree_append]

/-- The complete source alphabet reflects positivity, including the compiler's
extra terminal zero and arbitrary string of ones. -/
theorem code_mul_suffix_positive (r k : ℕ) (g : FreeGroup (Fin r)) (Q : PositiveWord)
    (h : code r g*positiveFree (suffix k)=positiveFree Q) :
    ∃ w : List (Fin r),g=positive w ∧ Q=BooneCollinsWords.chi r w++suffix k := by
  have hn := normal_reduced r k g.toWord FreeGroup.isReduced_toWord
  have he : normal r k g.toWord=pos Q := by
    have he := congrArg FreeGroup.toWord (normal_eval r k g.toWord)
    rw [FreeGroup.mk_toWord,h,CodeCancellation.positiveFree_toWord,
      FreeGroup.toWord_mk,hn.reduce_eq] at he
    exact he
  have hg := positive_of_signs g (normal_signs r k g.toWord (fun l hl=>pos_sign Q l (he ▸ hl)))
  refine ⟨g.toWord.map Prod.fst,hg,?_⟩
  apply BorisovCStage.positiveFree_injective
  rw [BorisovCStage.positiveFree_eq_eval,BorisovCStage.positiveFree_eq_eval]
  change positiveFree Q=positiveFree _
  calc
    positiveFree Q=code r g*positiveFree (suffix k) := h.symm
    _=code r (positive (g.toWord.map Prod.fst))*positiveFree (suffix k) :=
      congrArg (fun z=>code r z*positiveFree (suffix k)) hg
    _=_ := by rw [code_positive,CodeCancellation.positiveFree_append]

theorem code_injective (r : ℕ) : Function.Injective (code r) := by
  have hk (g : FreeGroup (Fin r)) (h : code r g=1) : g=1 := by
    have hh : code r g*positiveFree (suffix 0)=positiveFree (suffix 0) := by rw [h,one_mul]
    obtain ⟨w,hg,hw⟩ := code_mul_suffix_positive r 0 g (suffix 0) hh
    have hempty : BooneCollinsWords.chi r w=[] := by
      have hh : BooneCollinsWords.chi r w++suffix 0=[]++suffix 0 := by
        simpa only [List.nil_append] using hw.symm
      exact List.append_cancel_right hh
    have hwempty : w=[] := by
      cases w with
      | nil => rfl
      | cons i w =>
        have hz : 0∈BooneCollinsWords.chi r (i::w) := by
          exact List.mem_append_left _ (BooneCollinsWords.chiLetter_support r i).1
        rw [hempty] at hz
        exact False.elim (List.not_mem_nil hz)
    simpa [hwempty] using hg
  intro g h he
  apply mul_inv_eq_one.mp
  apply hk
  simp [he]

theorem lift_positive {α β : Type*} (f : α → List β) (w : List α) :
    FreeGroup.lift (fun i=>positive (f i)) (positive w)=positive (w.flatMap f) := by
  induction w with
  | nil => simp
  | cons i w ih => simp only [positive_cons,map_mul,FreeGroup.lift_apply_of,ih,
      List.flatMap_cons,positive_append]

/-- Input words admit a positive retraction, and both machine boundaries
are erased by that retraction. Paired-letter input encodings have this form. -/
structure Input (α : Type*) (r : ℕ) where
  words : α → List (Fin r)
  left : List (Fin r)
  right : List (Fin r)
  retract : Fin r → List α
  retract_words : ∀ i,(words i).flatMap retract=[i]
  retract_left : left.flatMap retract=[]
  retract_right : right.flatMap retract=[]

namespace Input
variable {α : Type*} {r : ℕ} (D : Input α r)

def source : FreeGroup α →* FreeGroup (Fin r) := FreeGroup.lift (fun i=>positive (D.words i))
def retraction : FreeGroup (Fin r) →* FreeGroup α := FreeGroup.lift (fun i=>positive (D.retract i))
theorem retraction_source : D.retraction.comp D.source=MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro i
  rw [MonoidHom.comp_apply,source,FreeGroup.lift_apply_of,MonoidHom.id_apply,
    retraction,lift_positive,D.retract_words]
  simp

theorem source_injective : Function.Injective D.source := by
  intro g h he
  have hh := congrArg D.retraction he
  change (D.retraction.comp D.source) g=(D.retraction.comp D.source) h at hh
  simpa only [D.retraction_source,MonoidHom.id_apply] using hh

@[simp] theorem retraction_left : D.retraction (positive D.left)=1 := by
  rw [retraction,lift_positive,D.retract_left,positive_nil]
@[simp] theorem retraction_right : D.retraction (positive D.right)=1 := by
  rw [retraction,lift_positive,D.retract_right,positive_nil]
@[simp] theorem retraction_source_apply (g : FreeGroup α) : D.retraction (D.source g)=g :=
  DFunLike.congr_fun D.retraction_source g

def hom : FreeGroup α →* FreeGroup (Fin 2) where
  toFun g := code r (positive D.left)*code r (D.source g)*(code r (positive D.left))⁻¹
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

theorem hom_injective : Function.Injective D.hom := by
  intro g h he
  change code r (positive D.left)*code r (D.source g)*(code r (positive D.left))⁻¹ =
    code r (positive D.left)*code r (D.source h)*(code r (positive D.left))⁻¹ at he
  exact D.source_injective (code_injective r (mul_left_cancel (mul_right_cancel he)))

def marker (k : ℕ) : PositiveWord := BooneCollinsWords.chi r (D.left++D.right)++suffix k
def spelling (k : ℕ) (w : List α) : PositiveWord :=
  BooneCollinsWords.chi r (D.left++w.flatMap D.words++D.right)++suffix k

theorem hom_mul_marker (k : ℕ) (g : FreeGroup α) :
    D.hom g*positiveFree (D.marker k)=
      code r (positive D.left*D.source g*positive D.right)*positiveFree (suffix k) := by
  simp only [hom,MonoidHom.coe_mk,OneHom.coe_mk,marker,BooneCollinsWords.chi_append,
    CodeCancellation.positiveFree_append,map_mul,code_positive]
  group

theorem positive_spelling (k : ℕ) (w : List α) :
    D.hom (positive w)*positiveFree (D.marker k)=positiveFree (D.spelling k w) := by
  rw [D.hom_mul_marker]
  have hs : D.source (positive w)=positive (w.flatMap D.words) := lift_positive _ _
  rw [hs,←positive_append,←positive_append,code_positive,←CodeCancellation.positiveFree_append]
  rfl

/-- Positivity of a signed conjugated input word followed by its marker
recovers a positive input and the exact fixed-boundary compiler spelling. -/
theorem hom_mul_marker_positive (k : ℕ) (g : FreeGroup α) (Q : PositiveWord)
    (h : D.hom g*positiveFree (D.marker k)=positiveFree Q) :
    ∃ w : List α,g=positive w ∧ Q=D.spelling k w := by
  rw [D.hom_mul_marker] at h
  obtain ⟨v,hv,_⟩ := code_mul_suffix_positive r k
    (positive D.left*D.source g*positive D.right) Q h
  have hg : g=positive (v.flatMap D.retract) := by
    have hh := congrArg D.retraction hv
    rw [map_mul,map_mul,D.retraction_left,D.retraction_right,
      D.retraction_source_apply,one_mul,mul_one] at hh
    simpa only [retraction,lift_positive] using hh
  refine ⟨v.flatMap D.retract,hg,?_⟩
  apply BorisovCStage.positiveFree_injective
  rw [BorisovCStage.positiveFree_eq_eval,BorisovCStage.positiveFree_eq_eval]
  change positiveFree Q=positiveFree _
  calc
    positiveFree Q=D.hom g*positiveFree (D.marker k) := by rw [D.hom_mul_marker];exact h.symm
    _=D.hom (positive (v.flatMap D.retract))*positiveFree (D.marker k) :=
      congrArg (fun z=>D.hom z*positiveFree (D.marker k)) hg
    _=positiveFree (D.spelling k (v.flatMap D.retract)) := D.positive_spelling k _

end Input

end
end UniversalGroup.HigmanCode
