module

public import UniversalGroup.Computability.WordProblem

@[expose] public section

/-!
# Changing the finite generators of a recursive presentation

Finite tables of representatives are primitive recursive, even when chosen
noncomputably. Substitution therefore pulls back the recursively enumerable
word problem to the kernel of any specified finite generating tuple.
-/
namespace UniversalGroup.RecursiveGeneratorTransfer
noncomputable section

variable {α : Type} [Primcodable α] {n : ℕ}
abbrev RawWord (α : Type) := List (α × Bool)

def substitute (table : Fin n → RawWord α) (w : RawWord (Fin n)) : RawWord α :=
  w.flatMap fun l => if l.2 then table l.1 else FreeGroup.invRev (table l.1)

theorem substitute_primrec (table : Fin n → RawWord α) : Primrec (substitute table) := by
  have ht : Primrec (fun l : Fin n × Bool => table l.1) :=
    (Primrec.dom_finite table).comp Primrec.fst
  have hl : Primrec (fun l : Fin n × Bool =>
      if l.2 then table l.1 else FreeGroup.invRev (table l.1)) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const true)) ht
      (RecursiveWords.invRev_primrec.comp ht)
  exact Primrec.list_flatMap Primrec.id (hl.comp Primrec.snd).to₂

omit [Primcodable α] in
theorem mk_substitute (table : Fin n → RawWord α) (w : RawWord (Fin n)) :
    FreeGroup.mk (substitute table w) =
      FreeGroup.lift (fun i=>FreeGroup.mk (table i)) (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    cases l with | mk i s => cases s <;>
      simpa [substitute,List.flatMap_cons,←FreeGroup.mul_mk,←FreeGroup.inv_mk,
        FreeGroup.lift_mk] using ih

variable (R : RecursivePresentation α) (f : FreeGroup (Fin n) →* R.Group)

/-- A finite list of words representing the prescribed finite generating tuple. -/
theorem exists_representatives :
    ∃ table : Fin n → RawWord α, ∀ i,
      PresentedGroup.mk R.relSet (FreeGroup.mk (table i))=f (FreeGroup.of i) := by
  classical
  have h (i : Fin n) : ∃ v : FreeGroup α, PresentedGroup.mk R.relSet v=f (FreeGroup.of i) :=
    QuotientGroup.mk'_surjective _ _
  choose v hv using h
  exact ⟨fun i=>(v i).toWord,fun i=>by simpa only [FreeGroup.mk_toWord] using hv i⟩

theorem substitution_evaluates (table : Fin n → RawWord α)
    (ht : ∀ i,PresentedGroup.mk R.relSet (FreeGroup.mk (table i))=f (FreeGroup.of i))
    (w : RawWord (Fin n)) :
    PresentedGroup.mk R.relSet (FreeGroup.mk (substitute table w))=f (FreeGroup.mk w) := by
  have h : (PresentedGroup.mk R.relSet).comp
      (FreeGroup.lift fun i=>FreeGroup.mk (table i))=f := by
    apply FreeGroup.ext_hom
    intro i
    simpa only [MonoidHom.comp_apply,FreeGroup.lift_apply_of] using ht i
  rw [mk_substitute]
  exact DFunLike.congr_fun h _

/-- Word representatives of the kernel remain recursively enumerable. -/
theorem kernel_enumerable : REPred (fun w : RawWord (Fin n) => f (FreeGroup.mk w)=1) := by
  obtain ⟨table,ht⟩ := exists_representatives R f
  have h := RecursiveEnumerable.comp (RecursiveWordProblem.word_problem_enumerable R)
    (substitute_primrec table).to_comp
  apply h.of_eq
  intro w
  rw [substitution_evaluates R f table ht]

def presentation : RecursivePresentation (Fin n) :=
  ⟨{w | f (FreeGroup.mk w)=1},kernel_enumerable R f⟩

theorem relSet_eq_ker : (presentation R f).relSet = (f.ker : Set (FreeGroup (Fin n))) := by
  ext g
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact hw
  · intro hg
    refine ⟨g.toWord,?_,FreeGroup.mk_toWord⟩
    change f (FreeGroup.mk g.toWord)=1
    rw [FreeGroup.mk_toWord]
    exact hg

theorem normalClosure_eq_ker : Subgroup.normalClosure (presentation R f).relSet=f.ker := by
  rw [relSet_eq_ker,Subgroup.normalClosure_eq_self]

/-- The transferred presentation represents precisely the original group. -/
def equiv (hf : Function.Surjective f) : (presentation R f).Group ≃* R.Group :=
  QuotientGroup.liftEquiv (Subgroup.normalClosure (presentation R f).relSet) hf
    (normalClosure_eq_ker R f)

@[simp] theorem equiv_of (hf : Function.Surjective f) (i : Fin n) :
    equiv R f hf (PresentedGroup.of i)=f (FreeGroup.of i) :=
  QuotientGroup.liftEquiv_mk _ hf (normalClosure_eq_ker R f) (FreeGroup.of i)

theorem exists_equiv_of_surjective (hf : Function.Surjective f) :
    ∃ S : RecursivePresentation (Fin n), Nonempty (S.Group ≃* R.Group) :=
  ⟨presentation R f,⟨equiv R f hf⟩⟩

end
end UniversalGroup.RecursiveGeneratorTransfer
