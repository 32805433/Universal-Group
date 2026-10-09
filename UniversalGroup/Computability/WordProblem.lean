module

public import UniversalGroup.Higman.Enumeration
public import UniversalGroup.Computability.Words

@[expose] public section

/-!
# Recursive enumerability of consequences of defining relations

A consequence is certified by a finite product of conjugates of defining
relators and their inverses. All certificate entries are finite words.
-/

namespace UniversalGroup.RecursiveWordProblem

variable {α : Type} [Primcodable α]

abbrev RawWord (α : Type) := List (α × Bool)
abbrev Factor (α : Type) := RawWord α × RawWord α × Bool

/-- A word spelling one signed conjugate of a defining relator. -/
def factorWord (p : Factor α) : RawWord α :=
  p.1 ++ (if p.2.2 then p.2.1 else FreeGroup.invRev p.2.1) ++ FreeGroup.invRev p.1

def factorValue (p : Factor α) : FreeGroup α :=
  FreeGroup.mk p.1 * (if p.2.2 then FreeGroup.mk p.2.1 else (FreeGroup.mk p.2.1)⁻¹) *
    (FreeGroup.mk p.1)⁻¹

omit [Primcodable α] in
theorem mk_factorWord (p : Factor α) : FreeGroup.mk (factorWord p) = factorValue p := by
  rcases p with ⟨c, r, b⟩
  cases b <;> simp [factorWord, factorValue, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, mul_assoc]

/-- Flatten a certificate into the word it represents. -/
def certificateWord (ps : List (Factor α)) : RawWord α := ps.flatMap factorWord

omit [Primcodable α] in
theorem mk_certificateWord (ps : List (Factor α)) :
    FreeGroup.mk (certificateWord ps) = (ps.map factorValue).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [certificateWord, List.flatMap_cons, ← FreeGroup.mul_mk,
        mk_factorWord, List.map_cons, List.prod_cons]
      exact congrArg (factorValue p * ·) ih

def Valid (R : RecursivePresentation α) (ps : List (Factor α)) : Prop :=
  ∀ p ∈ ps, p.2.1 ∈ R.relators

private def flip (p : Factor α) : Factor α := (p.1, p.2.1, !p.2.2)

omit [Primcodable α] in
private theorem value_flip (p : Factor α) : factorValue (flip p) = (factorValue p)⁻¹ := by
  rcases p with ⟨c, r, b⟩
  cases b <;> simp [factorValue, flip]

/-- Every element of the normal closure has a finite signed-conjugate certificate. -/
theorem normalClosure_certificate (R : RecursivePresentation α) (g : FreeGroup α) :
    g ∈ Subgroup.normalClosure R.relSet ↔
      ∃ ps, Valid R ps ∧ (ps.map factorValue).prod = g := by
  classical
  constructor
  · intro hg
    change g ∈ Subgroup.closure (Group.conjugatesOfSet R.relSet) at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
        obtain ⟨r, hr, rfl⟩ := ha
        obtain ⟨c, rfl⟩ := isConj_iff.mp hc
        refine ⟨[(c.toWord, r, true)], ?_, ?_⟩
        · simpa [Valid] using hr
        · simp [factorValue, FreeGroup.mk_toWord]
    | one => exact ⟨[], by simp [Valid], rfl⟩
    | mul x y hx hy ihx ihy =>
        obtain ⟨xs, hxs, rfl⟩ := ihx
        obtain ⟨ys, hys, rfl⟩ := ihy
        refine ⟨xs ++ ys, ?_, by simp⟩
        intro p hp
        exact (List.mem_append.mp hp).elim (hxs p) (hys p)
    | inv x hx ih =>
        obtain ⟨ps, hps, rfl⟩ := ih
        refine ⟨ps.reverse.map flip, ?_, ?_⟩
        · intro p hp
          obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
          exact hps p (List.mem_reverse.mp hp')
        · simp only [List.map_map, Function.comp_def, value_flip, List.map_reverse,
            List.prod_inv_reverse]

  · rintro ⟨ps, hps, rfl⟩
    have hfactor (p : Factor α) (hp : p ∈ ps) :
        factorValue p ∈ Subgroup.normalClosure R.relSet := by
      rcases p with ⟨c, r, b⟩
      have hr : FreeGroup.mk r ∈ Subgroup.normalClosure R.relSet :=
        Subgroup.subset_normalClosure ⟨r, hps _ hp, rfl⟩
      have hs : (if b then FreeGroup.mk r else (FreeGroup.mk r)⁻¹) ∈
          Subgroup.normalClosure R.relSet := by
        cases b
        · exact Subgroup.inv_mem _ hr
        · exact hr
      exact Subgroup.Normal.conj_mem (inferInstance : (Subgroup.normalClosure R.relSet).Normal)
        _ hs (FreeGroup.mk c)
    clear hps
    induction ps with
    | nil => exact Subgroup.one_mem _
    | cons p ps ih =>
        exact Subgroup.mul_mem _ (hfactor p (by simp))
          (ih fun q hq => hfactor q (by simp [hq]))

/-- Word triviality is equivalent to existence of a valid finite certificate. -/
theorem word_eq_one_iff (R : RecursivePresentation α) (w : RawWord α) :
    PresentedGroup.mk R.relSet (FreeGroup.mk w) = 1 ↔
      ∃ ps, Valid R ps ∧ FreeGroup.mk (certificateWord ps) = FreeGroup.mk w := by
  rw [PresentedGroup.mk_eq_one_iff, normalClosure_certificate]
  simp only [mk_certificateWord]

/-- A signed-conjugate spelling is a primitive recursive operation. -/
theorem factorWord_primrec : Primrec (@factorWord α) := by
  have hr : Primrec (fun p : Factor α => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : PrimrecPred (fun p : Factor α => p.2.2 = true) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const true)
  exact Primrec.list_append.comp
    (Primrec.list_append.comp Primrec.fst
      (Primrec.ite hs hr (RecursiveWords.invRev_primrec.comp hr)))
    (RecursiveWords.invRev_primrec.comp Primrec.fst)

/-- Flattening certificates is primitive recursive. -/
theorem certificateWord_primrec : Primrec (@certificateWord α) :=
  Primrec.list_flatMap Primrec.id (factorWord_primrec.comp Primrec.snd).to₂

/-- Validity only requires finitely many searches in the given relator set. -/
theorem valid_enumerable (R : RecursivePresentation α) : REPred (Valid R) :=
  RecursiveEnumerable.forall_mem_list
    (RecursiveEnumerable.comp R.enumerable (Primrec.fst.comp Primrec.snd).to_comp)

/-- The word problem of every recursively presented group is recursively
 enumerable, although in general it is undecidable. -/
theorem word_problem_enumerable (R : RecursivePresentation α) :
    REPred (fun w : RawWord α => PresentedGroup.mk R.relSet (FreeGroup.mk w) = 1) := by
  classical
  have hv : REPred (fun z : RawWord α × List (Factor α) => Valid R z.2) :=
    RecursiveEnumerable.comp (valid_enumerable R) Computable.snd
  have hred : PrimrecPred (fun z : RawWord α × List (Factor α) =>
      FreeGroup.reduce (certificateWord z.2) = FreeGroup.reduce z.1) :=
    Primrec.eq.comp
      (RecursiveWords.reduce_primrec.comp (certificateWord_primrec.comp Primrec.snd))
      (RecursiveWords.reduce_primrec.comp Primrec.fst)
  have heq : REPred (fun z : RawWord α × List (Factor α) =>
      FreeGroup.mk (certificateWord z.2) = FreeGroup.mk z.1) := by
    apply hred.computablePred.to_re.of_eq
    intro z
    exact FreeGroup.toWord_inj (x := FreeGroup.mk (certificateWord z.2))
      (y := FreeGroup.mk z.1)
  apply (RecursiveEnumerable.exists_re (RecursiveEnumerable.and hv heq)).of_eq
  intro w
  exact (word_eq_one_iff R w).symm

end UniversalGroup.RecursiveWordProblem
