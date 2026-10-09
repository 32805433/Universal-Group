module

public import UniversalGroup.Computability.Enumerable
public import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section

/-! Effective operations on signed free-group words. -/
namespace UniversalGroup.RecursiveWords
variable {α : Type} [Primcodable α] [DecidableEq α]

abbrev W (α : Type) := List (α×Bool)

omit [DecidableEq α] in
theorem invRev_primrec : Primrec (@FreeGroup.invRev α) :=
  Primrec.list_reverse.comp (Primrec.list_map Primrec.id
    ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.not.comp (Primrec.snd.comp Primrec.snd))).to₂)

def prepend (z : (α×Bool) × W α) : W α :=
  z.2.casesOn [z.1] fun y t =>
    if z.1.1=y.1 ∧ z.1.2= !y.2 then t else z.1::y::t

theorem prepend_primrec : Primrec (@prepend α _) := by
  have hf : Primrec (fun z : ((α×Bool)×W α)×((α×Bool)×W α) => z.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hg : Primrec (fun z : ((α×Bool)×W α)×((α×Bool)×W α) => z.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun z : ((α×Bool)×W α)×((α×Bool)×W α) => z.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hc : PrimrecPred (fun z : ((α×Bool)×W α)×((α×Bool)×W α) =>
      z.1.1.1=z.2.1.1 ∧ z.1.1.2= !z.2.1.2) :=
    (Primrec.eq.comp (Primrec.fst.comp hf) (Primrec.fst.comp hg)).and
      (Primrec.eq.comp (Primrec.snd.comp hf) (Primrec.not.comp (Primrec.snd.comp hg)))
  exact Primrec.list_casesOn Primrec.snd
    (Primrec.list_cons.comp Primrec.fst (Primrec.const []))
    (Primrec.ite hc ht (Primrec.list_cons.comp hf (Primrec.list_cons.comp hg ht))).to₂

theorem reduce_primrec : Primrec (@FreeGroup.reduce α _) := by
  have h := Primrec.list_foldr (α:=W α) Primrec.id (Primrec.const [])
    (prepend_primrec.comp Primrec.snd).to₂
  apply h.of_eq
  intro w
  induction w with
  | nil => rfl
  | cons a w ih =>
    change prepend (a,List.foldr (fun b s=>prepend (b,s)) [] w)=FreeGroup.reduce (a::w)
    change List.foldr (fun b s=>prepend (b,s)) [] w=FreeGroup.reduce w at ih
    rw [ih]
    rfl

end UniversalGroup.RecursiveWords
