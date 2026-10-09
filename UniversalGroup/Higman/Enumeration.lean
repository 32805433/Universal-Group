module

public import UniversalGroup.Foundations.Presentation
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.CoprodI

@[expose] public section

/-!
# An effective presentation of the free product of all finite presentations

Finite relator tables have a primitive recursive validity predicate. Give
valid presentations disjoint generator slots, kill unused slots, and rename
these slots by natural-number codes. Both presentation comparisons are proved
by explicit inverse homomorphisms. No embedding theorem is used here.
-/

namespace UniversalGroup

/-- Finite presentations, including their generator and relator counts.
There is no need to decide whether two codes present isomorphic groups. -/
abbrev PresentationCode := Σ n : ℕ, Σ m : ℕ, FP n m

/-- The group represented by a finite presentation code. -/
abbrev PresentationCode.group (p : PresentationCode) := p.2.2.Group

/-- An explicit group containing every finitely presented group. -/
abbrev AllFinitePresentations := Monoid.CoprodI PresentationCode.group

/-- Each finite presentation is one factor of the universal free product. -/
def allFinitePresentationsEmbedding (Q : FP n m) :
    GroupEmbedding Q.Group AllFinitePresentations where
  hom := Monoid.CoprodI.of (M := PresentationCode.group)
    (i := (⟨n, m, Q⟩ : PresentationCode))
  injective := Monoid.CoprodI.of_injective (M := PresentationCode.group) ⟨n, m, Q⟩

theorem allFinitePresentations_universal : IsUniversal AllFinitePresentations := by
  intro n m Q
  exact ⟨(allFinitePresentationsEmbedding Q).hom,
    (allFinitePresentationsEmbedding Q).injective⟩

/-- A recursively enumerable set of defining words on an effectively coded
alphabet. No decision procedure for equality in the presented group is assumed. -/
structure RecursivePresentation (α : Type) [Primcodable α] where
  relators : Set (List (α × Bool))
  enumerable : REPred (fun w => w ∈ relators)

namespace RecursivePresentation

variable {α : Type} [Primcodable α]

def relSet (R : RecursivePresentation α) : Set (FreeGroup α) :=
  FreeGroup.mk '' R.relators

abbrev Group (R : RecursivePresentation α) := PresentedGroup R.relSet

end RecursivePresentation

namespace Enumeration

/-- A finite table of signed natural-number words, with its alphabet bound. -/
abbrev Table := ℕ × List (List (ℕ × Bool))
abbrev Letter := Table × ℕ
abbrev RawWord := List (Letter × Bool)

def Valid (p : Table) : Prop := ∀ w ∈ p.2, ∀ l ∈ w, l.1 < p.1

def Live (g : Letter) : Prop := Valid g.1 ∧ g.2 < g.1.1

instance (p : Table) : Decidable (Valid p) := inferInstanceAs (Decidable (∀ w ∈ p.2, ∀ l ∈ w, l.1 < p.1))
instance (g : Letter) : Decidable (Live g) := inferInstanceAs (Decidable (Valid g.1 ∧ g.2 < g.1.1))

def tagged (p : Table) (w : List (ℕ × Bool)) : RawWord :=
  w.map fun l => ((p, l.1), l.2)

def first (w : RawWord) : Letter := (w.head?.getD default).1

/-- Original table rows, together with relations killing unused alphabet slots.
The empty word is included so that empty rows need no special encoding. -/
def Relator (w : RawWord) : Prop :=
  w = [] ∨
    (Valid (first w).1 ∧ ∃ r ∈ (first w).1.2, tagged (first w).1 r = w) ∨
    (¬ Live (first w) ∧ w = [(first w, true)])

private theorem valid_primrec : PrimrecPred Valid := by
  have h : PrimrecRel (fun (l : ℕ × Bool) (n : ℕ) => l.1 < n) :=
    Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact h.forall_mem_list.forall_mem_list.comp Primrec.snd Primrec.fst

private theorem live_primrec : PrimrecPred Live :=
  (valid_primrec.comp Primrec.fst).and
    (Primrec.nat_lt.comp Primrec.snd (Primrec.fst.comp Primrec.fst))

private theorem tagged_primrec : Primrec₂ tagged := by
  exact Primrec.list_map Primrec.snd
    ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd) |>.pair
      (Primrec.snd.comp Primrec.snd)).to₂

private theorem first_primrec : Primrec first :=
  Primrec.fst.comp (Primrec.option_getD_default.comp Primrec.list_head?)

theorem relator_primrec : PrimrecPred Relator := by
  have h : PrimrecRel (fun (r : List (ℕ × Bool)) (w : RawWord) =>
      tagged (first w).1 r = w) :=
    Primrec.eq.comp
      (tagged_primrec.comp (Primrec.fst.comp (first_primrec.comp Primrec.snd)) Primrec.fst)
      Primrec.snd
  exact (Primrec.eq.comp Primrec.id (Primrec.const [])).or
    (((valid_primrec.comp (Primrec.fst.comp first_primrec)).and
      (h.exists_mem_list.comp (Primrec.snd.comp (Primrec.fst.comp first_primrec)) Primrec.id)).or
    ((live_primrec.comp first_primrec).not.and
      (Primrec.eq.comp Primrec.id
        (Primrec.list_cons.comp (first_primrec.pair (Primrec.const true))
          (Primrec.const [])))))

def forget (w : Word n) : List (ℕ × Bool) := w.map fun l => (l.1.val, l.2)

def bounded (n : ℕ) (w : List (ℕ × Bool)) : Word n :=
  w.filterMap fun l => if h : l.1 < n then some (⟨l.1, h⟩, l.2) else none

@[simp] theorem bounded_forget (w : Word n) : bounded n (forget w) = w := by
  induction w with
  | nil => rfl
  | cons l w ih => simp_all [bounded, forget, l.1.isLt]

theorem forget_bounded (w : List (ℕ × Bool)) (h : ∀ l ∈ w, l.1 < n) :
    forget (bounded n w) = w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simpa [bounded, forget, h.1] using congrArg (l :: ·) (ih h.2)

def table (p : PresentationCode) : Table :=
  (p.1, List.ofFn fun i => forget (p.2.2.relator i))

def presentation (p : Table) : PresentationCode :=
  ⟨p.1, p.2.length, ⟨fun i => bounded p.1 p.2[i]⟩⟩

@[simp] theorem presentation_fst (p : Table) : (presentation p).1 = p.1 := rfl

theorem table_valid (p : PresentationCode) : Valid (table p) := by
  intro w hw l hl
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
  obtain ⟨⟨j, s⟩, _, rfl⟩ := List.mem_map.mp hl
  exact j.isLt

@[simp] theorem presentation_table (p : PresentationCode) : presentation (table p) = p := by
  rcases p with ⟨n, m, ⟨rels⟩⟩
  dsimp [table, presentation]
  simp only [List.getElem_ofFn, bounded_forget]
  congr 3 <;> try simp
  apply (Fin.heq_fun_iff (by simp)).mpr
  intro i
  rfl

theorem table_presentation (p : Table) (h : Valid p) : table (presentation p) = p := by
  rcases p with ⟨n, rows⟩
  apply Prod.ext (by rfl)
  apply List.ext_getElem
  · simp [table, presentation]
  · intro i hi hj
    simpa [table, presentation] using forget_bounded rows[i] (h _ (List.getElem_mem _))

/-- The recursive presentation is first constructed on explicitly labelled slots. -/
def rawPresentation : RecursivePresentation Letter :=
  ⟨{w | Relator w}, relator_primrec.computablePred.to_re⟩

theorem tagged_relator (p : Table) (hp : Valid p) (w : List (ℕ × Bool))
    (hw : w ∈ p.2) : Relator (tagged p w) := by
  cases w with
  | nil => exact Or.inl rfl
  | cons l w => exact Or.inr (Or.inl ⟨hp, _, hw, rfl⟩)

theorem dead_relator (g : Letter) (hg : ¬ Live g) : Relator [(g, true)] :=
  Or.inr (Or.inr ⟨hg, rfl⟩)

private theorem lift_tagged {H : Type*} [Group H] (x : Letter → H)
    (p : Table) (w : Word n) :
    FreeGroup.lift x (FreeGroup.mk (tagged p (forget w))) =
      Word.eval (fun i => x (p, i.val)) w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rcases l with ⟨i, s⟩
    cases s <;> simp_all [tagged, forget, Word.eval, FreeGroup.lift_mk]

def intoRaw (p : PresentationCode) : p.group →* rawPresentation.Group :=
  p.2.2.homOfRelators (fun i => PresentedGroup.of (table p, i.val)) (by
    intro i
    rw [← lift_tagged]
    rw [show FreeGroup.lift (PresentedGroup.of (rels := rawPresentation.relSet)) =
      PresentedGroup.mk rawPresentation.relSet by ext; rfl]
    exact PresentedGroup.one_of_mem ⟨_, tagged_relator _ (table_valid p) _
      (List.mem_ofFn.mpr ⟨i, rfl⟩), rfl⟩)

def rawForward : AllFinitePresentations →* rawPresentation.Group :=
  Monoid.CoprodI.lift intoRaw

def universalGenerator (p : PresentationCode) (i : Fin p.1) : AllFinitePresentations :=
  Monoid.CoprodI.of (generators p.2.2 i)

def universalGeneratorNat (p : PresentationCode) (i : ℕ) : AllFinitePresentations :=
  if h : i < p.1 then universalGenerator p ⟨i, h⟩ else 1

def rawValues (g : Letter) : AllFinitePresentations :=
  if Valid g.1 then universalGeneratorNat (presentation g.1) g.2 else 1

@[simp] theorem rawValues_table (p : PresentationCode) (i : Fin p.1) :
    rawValues (table p, i.val) = universalGenerator p i := by
  simp only [rawValues, ite_eq_left (table_valid p), presentation_table]
  exact dite_eq_left i.isLt

theorem rawValues_dead (g : Letter) (hg : ¬ Live g) : rawValues g = 1 := by
  by_cases hp : Valid g.1
  · simp only [rawValues, ite_eq_left hp, universalGeneratorNat]
    exact dite_eq_right (fun hi => hg ⟨hp, hi⟩)
  · simp [rawValues, hp]

theorem rawValues_relator (w : RawWord) (h : Relator w) :
    FreeGroup.lift rawValues (FreeGroup.mk w) = 1 := by
  rcases h with rfl | ⟨hp, r, hr, he⟩ | ⟨hg, he⟩
  · rfl
  · let p := (first w).1
    have ht := table_presentation p hp
    have hr' : r ∈ (table (presentation p)).2 := by rw [ht]; exact hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr'
    rw [← he]
    conv_lhs => arg 2; arg 1; arg 1; change p; rw [← ht]
    rw [lift_tagged]
    simp only [rawValues_table]
    change Word.eval ((Monoid.CoprodI.of (M := PresentationCode.group)
      (i := presentation p)) ∘ generators (presentation p).2.2) _ = 1
    rw [← Word.map_eval]
    have hx := (presentation p).2.2.relator_eq_one i
    change Word.eval (generators (presentation p).2.2) _ = 1 at hx
    rw [hx, map_one]
  · rw [he]
    simpa [FreeGroup.lift_mk] using rawValues_dead (first w) hg

def rawBackward : rawPresentation.Group →* AllFinitePresentations :=
  PresentedGroup.toGroup (f := rawValues) (fun r hr => by
    obtain ⟨w, hw, rfl⟩ := hr
    exact rawValues_relator w hw)

theorem rawBackward_forward : rawBackward.comp rawForward = MonoidHom.id _ := by
  apply Monoid.CoprodI.ext_hom
  intro p
  apply PresentedGroup.ext
  intro i
  simp [rawForward, rawBackward, intoRaw, universalGenerator, generators]

theorem rawForward_backward : rawForward.comp rawBackward = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro g
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, rawBackward, PresentedGroup.toGroup.of]
  by_cases hg : Live g
  · have hi : g.2 < (presentation g.1).1 := hg.2
    rw [rawValues, ite_eq_left hg.1, universalGeneratorNat, dite_eq_left hi]
    simp only [universalGenerator, rawForward, Monoid.CoprodI.lift_of,
      intoRaw, generators, FP.homOfRelators_of]
    rw [table_presentation g.1 hg.1]
  · rw [rawValues_dead g hg, map_one]
    symm
    exact PresentedGroup.one_of_mem ⟨[(g, true)], dead_relator g hg, rfl⟩

/-- Each finite presentation has exactly its own factor; unused slots are trivial. -/
def rawEquiv : AllFinitePresentations ≃* rawPresentation.Group :=
  MonoidHom.toMulEquiv rawForward rawBackward
    rawBackward_forward rawForward_backward

/-- Decode a natural-number slot. Codes outside the encoding range use the
default slot, which is itself killed in `rawPresentation`. -/
def decodeSlot (i : ℕ) : Letter := (Encodable.decode (α := Letter) i).getD default

@[simp] theorem decodeSlot_encode (g : Letter) : decodeSlot (Encodable.encode g) = g := by
  simp [decodeSlot]

def decodeWord (w : List (ℕ × Bool)) : RawWord :=
  w.map fun l => (decodeSlot l.1, l.2)

def encodeWord (w : RawWord) : List (ℕ × Bool) :=
  w.map fun l => (Encodable.encode l.1, l.2)

@[simp] theorem decodeWord_encodeWord (w : RawWord) : decodeWord (encodeWord w) = w := by
  simp [decodeWord, encodeWord, List.map_map, Function.comp_def]

def aliasRelator (i : ℕ) : List (ℕ × Bool) :=
  [(i, true), (Encodable.encode (decodeSlot i), false)]

def NatRelator (w : List (ℕ × Bool)) : Prop :=
  Relator (decodeWord w) ∨ w = aliasRelator (w.head?.getD default).1

private theorem decodeSlot_primrec : Primrec decodeSlot :=
  Primrec.option_getD_default.comp Primrec.decode

private theorem decodeWord_primrec : Primrec decodeWord :=
  Primrec.list_map Primrec.id
    ((decodeSlot_primrec.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)).to₂

private theorem aliasRelator_primrec : Primrec aliasRelator :=
  Primrec.list_cons.comp (Primrec.id.pair (Primrec.const true))
    (Primrec.list_cons.comp
      ((Primrec.encode.comp decodeSlot_primrec).pair (Primrec.const false)) (Primrec.const []))

theorem natRelator_primrec : PrimrecPred NatRelator :=
  (relator_primrec.comp decodeWord_primrec).or
    (Primrec.eq.comp Primrec.id (aliasRelator_primrec.comp
      (Primrec.fst.comp (Primrec.option_getD_default.comp Primrec.list_head?))))

def natPresentation : RecursivePresentation ℕ :=
  ⟨{w | NatRelator w}, natRelator_primrec.computablePred.to_re⟩

private theorem lift_mapped_word {A B H : Type*} [Group H] (f : A → B) (v : B → H)
    (w : List (A × Bool)) :
    FreeGroup.lift v (FreeGroup.mk (w.map fun l => (f l.1, l.2))) =
      FreeGroup.lift (fun a => v (f a)) (FreeGroup.mk w) := by
  simp [FreeGroup.lift_mk, List.map_map, Function.comp_def]

private theorem lift_generators {A : Type*} (rels : Set (FreeGroup A)) :
    FreeGroup.lift (PresentedGroup.of (rels := rels)) = PresentedGroup.mk rels := by
  ext
  rfl

def rawToNat : rawPresentation.Group →* natPresentation.Group :=
  PresentedGroup.toGroup (f := fun g => PresentedGroup.of (Encodable.encode g)) (by
    rintro r ⟨w, hw, rfl⟩
    rw [← lift_mapped_word Encodable.encode (PresentedGroup.of (rels := natPresentation.relSet)), lift_generators]
    apply PresentedGroup.one_of_mem
    refine ⟨encodeWord w, ?_, rfl⟩
    change NatRelator (encodeWord w)
    apply Or.inl
    rw [decodeWord_encodeWord]
    exact hw)

def natToRaw : natPresentation.Group →* rawPresentation.Group :=
  PresentedGroup.toGroup (f := fun i => PresentedGroup.of (decodeSlot i)) (by
    rintro r ⟨w, hw, rfl⟩
    rcases hw with hw | hw
    · rw [← lift_mapped_word decodeSlot (PresentedGroup.of (rels := rawPresentation.relSet)), lift_generators]
      exact PresentedGroup.one_of_mem ⟨decodeWord w, hw, rfl⟩
    · rw [hw]
      simp [aliasRelator, FreeGroup.lift_mk])

theorem natToRaw_rawToNat : natToRaw.comp rawToNat = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro g
  simp [rawToNat, natToRaw]

theorem rawToNat_natToRaw : rawToNat.comp natToRaw = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, rawToNat, natToRaw,
    PresentedGroup.toGroup.of]
  have h : PresentedGroup.mk natPresentation.relSet (FreeGroup.mk (aliasRelator i)) = 1 :=
    PresentedGroup.one_of_mem ⟨aliasRelator i, Or.inr rfl, rfl⟩
  rw [← lift_generators] at h
  simpa [aliasRelator, FreeGroup.lift_mk] using (mul_inv_eq_one.mp h).symm

def natEquiv : rawPresentation.Group ≃* natPresentation.Group :=
  MonoidHom.toMulEquiv rawToNat natToRaw natToRaw_rawToNat rawToNat_natToRaw

end Enumeration

/-- Enumerate all finite presentations on disjoint natural-number slots.
The table-row predicate is in fact primitive recursive. -/
theorem allFinitePresentations_recursive :
    ∃ R : RecursivePresentation ℕ,
      Nonempty (AllFinitePresentations ≃* R.Group) :=
  ⟨Enumeration.natPresentation, ⟨Enumeration.rawEquiv.trans Enumeration.natEquiv⟩⟩

end UniversalGroup
