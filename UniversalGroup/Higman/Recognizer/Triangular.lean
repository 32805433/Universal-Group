module

public import UniversalGroup.Coding.SourceMarker
public import Mathlib.Algebra.Ring.Nat

@[expose] public section

/-! Binary triangularization of finite nonempty Thue rules. The original
alphabet is doubled. A shared fresh head expands to either side of each old
relation, so no identification of old letters is introduced. -/
namespace UniversalGroup.HigmanTriangular
open Thue Coding.SourceMarker
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {α I : Type}
variable (L R : I → List α) (hL : ∀ i, L i ≠ []) (hR : ∀ i, R i ≠ [])

abbrev Base (α : Type) := α × Fin 2

def doubleLetter (a : α) : List (Base α) := [(a,0),(a,1)]
def doubleWord (w : List α) : List (Base α) := w.flatMap doubleLetter

def side (i : I) (b : Bool) : List (Base α) :=
  doubleWord (if b then R i else L i)

def source : ThueSystem α := Set.range (fun i => (L i, R i))
def doubledSource : ThueSystem (Base α) :=
  Set.range (fun i => (doubleWord (L i), doubleWord (R i)))

include hL hR in
theorem side_length (i : I) (b : Bool) : 2 ≤ (side L R i b).length := by
  have hl (w : List α) : (doubleWord w).length = 2*w.length := by
    induction w with
    | nil => rfl
    | cons a w ih => simp [doubleWord, doubleLetter, Nat.add_mul, Nat.mul_comm, Nat.add_assoc]
  have hn : (if b then R i else L i) ≠ [] := by cases b <;> simp [hL i, hR i]
  rw [side, hl]
  have := List.length_pos_iff.mpr hn
  omega

abbrev TailIndex := Σ i : I, Σ b : Bool, Fin (side L R i b).length
abbrev Alphabet := Base α ⊕ (I ⊕ TailIndex L R)

abbrev base (a : Base α) : Alphabet L R := Sum.inl a
abbrev head (i : I) : Alphabet L R := Sum.inr (Sum.inl i)
abbrev tail (i : I) (b : Bool) (k : Fin (side L R i b).length) : Alphabet L R :=
  Sum.inr (Sum.inr ⟨i,b,k⟩)

def symbol (i : I) (b : Bool) (k : Fin (side L R i b).length) : Alphabet L R :=
  if k.val = 0 then head L R i
  else if k.val+1 = (side L R i b).length then base L R ((side L R i b)[k.val])
  else tail L R i b k

abbrev Row := Σ i : I, Σ b : Bool, Fin ((side L R i b).length-1)

def rowLeft (p : Row L R) : Alphabet L R :=
  symbol L R p.1 p.2.1 ⟨p.2.2.val,by have := p.2.2.isLt; omega⟩

def rowRight (p : Row L R) : Alphabet L R × Alphabet L R :=
  (base L R ((side L R p.1 p.2.1)[p.2.2.val]'(by have := p.2.2.isLt; omega)),
   symbol L R p.1 p.2.1 ⟨p.2.2.val+1,by have := p.2.2.isLt; omega⟩)

def rules : ThueSystem (Alphabet L R) :=
  Set.range (fun p : Row L R => ([rowLeft L R p], [ (rowRight L R p).1, (rowRight L R p).2]))

def lift (w : List α) : List (Alphabet L R) :=
  (doubleWord w).map (base L R)

def decodeLetter : Alphabet L R → List (Base α)
  | .inl a => [a]
  | .inr (.inl i) => doubleWord (L i)
  | .inr (.inr ⟨i,b,k⟩) => (side L R i b).drop k.val

def decode (w : List (Alphabet L R)) : List (Base α) := w.flatMap (decodeLetter L R)

@[simp] theorem decode_lift (w : List α) : decode L R (lift L R w) = doubleWord w := by
  simp [decode, lift, List.flatMap_map, decodeLetter]

theorem symbol_decode (i : I) (b : Bool) (k : Fin (side L R i b).length) :
    ThueEq (doubledSource L R) (decodeLetter L R (symbol L R i b k))
      ((side L R i b).drop k.val) := by
  by_cases hk : k.val = 0
  · simp only [symbol, hk, ite_eq_left, head, decodeLetter, List.drop_zero]
    cases b with
    | false => exact Relation.ReflTransGen.refl
    | true => exact relation_eq ⟨i,rfl⟩
  · by_cases hlast : k.val+1 = (side L R i b).length
    · have hd : (side L R i b).drop k.val = [(side L R i b)[k.val]] := by
        rw [List.drop_eq_getElem_cons k.isLt, List.drop_eq_nil_iff.mpr (by omega)]
      simp only [symbol, hk, hlast, ite_eq_left, base, decodeLetter]
      rw [hd]
      exact Relation.ReflTransGen.refl
    · simp only [symbol, hk, hlast, tail, decodeLetter]
      exact Relation.ReflTransGen.refl

theorem row_decode (p : Row L R) :
    ThueEq (doubledSource L R) (decode L R [rowLeft L R p])
      (decode L R [(rowRight L R p).1,(rowRight L R p).2]) := by
  let k : Fin (side L R p.1 p.2.1).length := ⟨p.2.2.val,by have := p.2.2.isLt; omega⟩
  let k' : Fin (side L R p.1 p.2.1).length := ⟨p.2.2.val+1,by have := p.2.2.isLt; omega⟩
  have h₁ := symbol_decode L R p.1 p.2.1 k
  have h₂ := thueEq_context
    [(side L R p.1 p.2.1)[k.val]] [] (thueEq_symm (symbol_decode L R p.1 p.2.1 k'))
  have hd := List.drop_eq_getElem_cons k.isLt
  have h : ThueEq (doubledSource L R)
      (decodeLetter L R (symbol L R p.1 p.2.1 k))
      ([(side L R p.1 p.2.1)[k.val]] ++ decodeLetter L R (symbol L R p.1 p.2.1 k')) := by
    apply h₁.trans
    simpa only [ThueEq, List.append_nil, List.singleton_append, hd, k, k'] using h₂
  simpa [decode, rowLeft, rowRight, k, k', decodeLetter] using h

theorem reflection {u v : List (Alphabet L R)} (h : ThueEq (rules L R) u v) :
    ThueEq (doubledSource L R) (decode L R u) (decode L R v) := by
  apply substitute_eq (decodeLetter L R) ?_ h
  rintro x y ⟨p,hp⟩
  cases hp
  exact row_decode L R p

include hL hR in
/-- Every shared head expands through binary suffix rows to either original
side, literally as a word in the doubled old alphabet. -/
theorem expand_symbol (i : I) (b : Bool) (k : Fin (side L R i b).length) :
    ThueEq (rules L R) [symbol L R i b k]
      (((side L R i b).drop k.val).map (base L R)) := by
  by_cases hn : k.val+1 < (side L R i b).length
  · let p : Row L R := ⟨i,b,⟨k.val,by omega⟩⟩
    have hs : ThueEq (rules L R) [symbol L R i b k]
        [base L R ((side L R i b)[k.val]), symbol L R i b ⟨k.val+1,hn⟩] := by
      exact relation_eq ⟨p,rfl⟩
    have ht := expand_symbol i b ⟨k.val+1,hn⟩
    have hc := thueEq_context [base L R ((side L R i b)[k.val])] [] ht
    apply hs.trans
    simpa only [ThueEq, List.append_nil, List.singleton_append,
      List.drop_eq_getElem_cons k.isLt, List.map_cons] using hc
  · have hk : k.val+1 = (side L R i b).length := by omega
    have hk0 : k.val ≠ 0 := by have := side_length L R hL hR i b; omega
    have hd : (side L R i b).drop k.val = [(side L R i b)[k.val]] := by
      rw [List.drop_eq_getElem_cons k.isLt, List.drop_eq_nil_iff.mpr (by omega)]
    simp only [symbol, hk0, hk, ite_eq_left, hd, List.map_cons, List.map_nil]
    exact Relation.ReflTransGen.refl
termination_by (side L R i b).length-k.val

include hL hR in
theorem expand_head (i : I) (b : Bool) :
    ThueEq (rules L R) [head L R i] ((side L R i b).map (base L R)) := by
  have hn := side_length L R hL hR i b
  simpa [symbol] using expand_symbol L R hL hR i b ⟨0,by omega⟩

include hL hR in
theorem relation_forward (i : I) : ThueEq (rules L R) (lift L R (L i)) (lift L R (R i)) :=
  (thueEq_symm (expand_head L R hL hR i false)).trans (expand_head L R hL hR i true)

include hL hR in
theorem forward {u v : List α} (h : ThueEq (source L R) u v) :
    ThueEq (rules L R) (lift L R u) (lift L R v) := by
  have hcode (w : List α) : w.flatMap (fun a => lift L R [a]) = lift L R w := by
    simp [lift, doubleWord, List.map_flatMap, doubleLetter]
  rw [←hcode, ←hcode]
  apply substitute_eq (fun a => lift L R [a]) ?_ h
  rintro x y ⟨i,hxy⟩
  cases hxy
  rw [hcode,hcode]
  exact relation_forward L R hL hR i

def undoubleLetter (a : Base α) : List α := if a.2 = 0 then [a.1] else []
def undouble (w : List (Base α)) : List α := w.flatMap undoubleLetter

@[simp] theorem undouble_double (w : List α) : undouble (doubleWord w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp_all [undouble, doubleWord, doubleLetter, undoubleLetter]

theorem doubled_reflection {u v : List (Base α)} (h : ThueEq (doubledSource L R) u v) :
    ThueEq (source L R) (undouble u) (undouble v) := by
  apply substitute_eq undoubleLetter ?_ h
  rintro x y ⟨i,hxy⟩
  cases hxy
  change ThueEq (source L R) (undouble (doubleWord (L i))) (undouble (doubleWord (R i)))
  rw [undouble_double,undouble_double]
  exact relation_eq ⟨i,rfl⟩

include hL hR in
theorem equivalence (u v : List α) :
    ThueEq (source L R) u v ↔ ThueEq (rules L R) (lift L R u) (lift L R v) := by
  refine ⟨forward L R hL hR, fun h => ?_⟩
  have hh := doubled_reflection L R (reflection L R h)
  simpa using hh

end
end UniversalGroup.HigmanTriangular
