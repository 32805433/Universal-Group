module

public import UniversalGroup.Coding.Data
public import UniversalGroup.Coding.Thue.Core

@[expose] public section

/-! The marker semigroup before triangularization and binary compression. -/
namespace UniversalGroup.Coding.SourceMarker

open Thue
set_option maxHeartbeats 600000
local instance {α : Type*} (S : ThueSystem α) : Trans (ThueEq S) (ThueEq S) (ThueEq S) :=
  ⟨Relation.ReflTransGen.trans⟩

/-- Applying a word substitution is sound when each defining relation is sound. -/
theorem substitute_eq {α β : Type*} {S : ThueSystem α} {T : ThueSystem β}
    (f : α → List β)
    (hf : ∀ x y, (x,y) ∈ S → ThueEq T (x.flatMap f) (y.flatMap f))
    {X Y : List α} (h : ThueEq S X Y) :
    ThueEq T (X.flatMap f) (Y.flatMap f) := by
  have hs : ∀ X Y, ThueStep S X Y → ThueEq T (X.flatMap f) (Y.flatMap f) := by
    intro X Y hstep
    obtain ⟨l,r,x,y,hxy,hwords⟩ := hstep
    rcases hwords with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa only [List.flatMap_append] using thueEq_context (l.flatMap f) (r.flatMap f) (hf x y hxy)
    · simpa only [List.flatMap_append] using thueEq_context (l.flatMap f) (r.flatMap f)
        (thueEq_symm (hf x y hxy))
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans (hs _ _ hstep)

/-- Every relation holds as a derivation without additional context. -/
theorem relation_eq {α : Type*} {S : ThueSystem α} {x y : List α}
    (h : (x,y) ∈ S) : ThueEq S x y :=
  Relation.ReflTransGen.single ⟨[],[],x,y,h,Or.inl ⟨by simp,by simp⟩⟩

abbrev Alphabet := Fin 3
def letter (i : Fin 2) : Alphabet := i.castSucc
def marker : Alphabet := 2
def lift (w : PositiveWord) : List Alphabet := w.map letter

def eraseLetter (x : Alphabet) : PositiveWord :=
  if h : x.val < 2 then [⟨x.val,h⟩] else []
def erase (w : List Alphabet) : PositiveWord := w.flatMap eraseLetter

@[simp] theorem lift_append (u v : PositiveWord) : lift (u++v) = lift u ++ lift v := by
  simp [lift]
@[simp] theorem erase_letter (i : Fin 2) : eraseLetter (letter i) = [i] := by
  simp [eraseLetter,letter,i.isLt]
@[simp] theorem erase_marker : eraseLetter marker = [] := by decide
@[simp] theorem erase_lift (w : PositiveWord) : erase (lift w) = w := by
  simp [erase,lift,List.flatMap_map]
@[simp] theorem erase_single_marker : erase [marker] = [] := by simp [erase]
@[simp] theorem erase_append (u v : List Alphabet) : erase (u++v) = erase u ++ erase v := by
  simp [erase]
@[simp] theorem marker_ne_letter (i : Fin 2) : marker ≠ letter i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [marker,letter] at hv
  omega

variable (G : PreparedInput)

def left : Fin (G.relatorCount + 2) → List Alphabet :=
  Fin.addCases (fun i => lift (G.relators i) ++ [marker]) (fun i => [letter i,marker])
def right : Fin (G.relatorCount + 2) → List Alphabet :=
  Fin.addCases (fun _ => [marker]) (fun i => [marker,letter i])
def rules : ThueSystem Alphabet := Set.range fun i => (left G i,right G i)

@[simp] theorem left_primary (i : Fin G.relatorCount) :
    left G (Fin.castAdd 2 i) = lift (G.relators i) ++ [marker] := by simp [left]
@[simp] theorem right_primary (i : Fin G.relatorCount) :
    right G (Fin.castAdd 2 i) = [marker] := by simp [right]
@[simp] theorem left_shift (i : Fin 2) :
    left G (Fin.natAdd G.relatorCount i) = [letter i,marker] := by simp [left]
@[simp] theorem right_shift (i : Fin 2) :
    right G (Fin.natAdd G.relatorCount i) = [marker,letter i] := by simp [right]

theorem primary (i : Fin G.relatorCount) :
    ThueEq (rules G) (lift (G.relators i) ++ [marker]) [marker] := by
  apply relation_eq
  exact ⟨Fin.castAdd 2 i,by simp⟩

theorem shift (i : Fin 2) : ThueEq (rules G) [letter i,marker] [marker,letter i] := by
  apply relation_eq
  exact ⟨Fin.natAdd G.relatorCount i,by simp⟩

theorem commute_marker (w : PositiveWord) :
    ThueEq (rules G) (lift w ++ [marker]) ([marker] ++ lift w) := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | cons i w ih =>
      have h₁ := thueEq_context [letter i] [] ih
      have h₂ := thueEq_context [] (lift w) (shift G i)
      calc
        ThueEq (rules G) _ (letter i :: marker :: lift w) := by simpa [lift,List.append_assoc] using h₁
        ThueEq (rules G) _ _ := by simpa [lift,List.append_assoc] using h₂

/-- A derivation ending at the marker may be placed in any input-word context. -/
theorem marked_context (l r x y : PositiveWord)
    (h : ThueEq (rules G) (lift x ++ [marker]) (lift y ++ [marker])) :
    ThueEq (rules G) (lift (l++x++r) ++ [marker]) (lift (l++y++r) ++ [marker]) := by
  have h₁ := thueEq_context (lift (l++x)) [] (commute_marker G r)
  have h₂ := thueEq_context (lift l) (lift r) h
  have h₃ := thueEq_context (lift (l++y)) [] (thueEq_symm (commute_marker G r))
  calc
    ThueEq (rules G) _ (lift l ++ (lift x ++ [marker]) ++ lift r) := by
      simpa only [lift_append,List.append_nil,List.append_assoc] using h₁
    ThueEq (rules G) _ (lift l ++ (lift y ++ [marker]) ++ lift r) := h₂
    ThueEq (rules G) _ _ := by
      simpa only [lift_append,List.append_nil,List.append_assoc] using h₃

theorem forward {u v : PositiveWord} (h : PositiveEq G.monoidRules u v) :
    ThueEq (rules G) (lift u ++ [marker]) (lift v ++ [marker]) := by
  have hs : ∀ X Y, PositiveStep G.monoidRules X Y →
      ThueEq (rules G) (lift X ++ [marker]) (lift Y ++ [marker]) := by
    intro X Y hstep
    obtain ⟨l,r,x,y,⟨i,hi⟩,hwords⟩ := hstep
    cases hi
    rcases hwords with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa [lift] using marked_context G l r (G.relators i) [] (primary G i)
    · exact thueEq_symm (by
        simpa [lift] using marked_context G l r (G.relators i) [] (primary G i))
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans (hs _ _ hstep)

theorem erase_eq {u v : List Alphabet} (h : ThueEq (rules G) u v) :
    PositiveEq G.monoidRules (erase u) (erase v) := by
  change ThueEq G.monoidRules (erase u) (erase v)
  apply substitute_eq eraseLetter ?_ h
  rintro x y ⟨i,hi⟩
  rcases Prod.mk.inj hi with ⟨rfl,rfl⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    change ThueEq G.monoidRules (erase (left G (Fin.castAdd 2 j)))
      (erase (right G (Fin.castAdd 2 j)))
    simpa only [left_primary,right_primary,erase_append,erase_lift,erase_single_marker,
      List.append_nil] using (relation_eq (S := G.monoidRules) ⟨j,rfl⟩)
  · intro j
    simp only [left_shift,right_shift,List.flatMap_cons,List.flatMap_nil,erase_letter,
      erase_marker,List.append_nil,List.nil_append]
    exact Relation.ReflTransGen.refl

theorem recognizes (w : PositiveWord) :
    PositiveEq G.monoidRules w [] ↔ ThueEq (rules G) (lift w ++ [marker]) [marker] := by
  constructor
  · intro h
    simpa [lift] using forward G h
  · intro h
    simpa only [erase_append, erase_lift, erase_single_marker, List.append_nil] using erase_eq G h

/-- Marker multiplicity is an invariant of the source semigroup. -/
theorem count_marker_eq {u v : List Alphabet} (h : ThueEq (rules G) u v) :
    u.count marker = v.count marker := by
  have hrow : ∀ i, (left G i).count marker = (right G i).count marker := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      have hz : (lift (G.relators j)).count marker = 0 := by
        apply List.count_eq_zero.mpr
        simp only [lift,List.mem_map]
        rintro ⟨a,_,ha⟩
        exact marker_ne_letter a ha.symm
      simp only [left_primary,right_primary,List.count_append,hz,Nat.zero_add]
    · intro j
      simp only [left_shift,right_shift,List.count_cons]
      omega
  induction h with
  | refl => rfl
  | tail _ hs ih =>
      obtain ⟨l,r,x,y,⟨i,hi⟩,hw⟩ := hs
      cases hi
      rcases hw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · simpa only [List.count_append,hrow] using ih
      · simpa only [List.count_append,← hrow] using ih

end UniversalGroup.Coding.SourceMarker
