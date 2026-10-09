module

public import Mathlib.Computability.Reduce

@[expose] public section

/-! Closure properties of recursively enumerable predicates, with explicit
bounded computation certificates. -/
namespace UniversalGroup.RecursiveEnumerable

variable {α β : Type} [Primcodable α] [Primcodable β]

/-- Every r.e. predicate has a primitive recursive certificate verifier. -/
theorem certificate {p : α → Prop} (hp : REPred p) :
    ∃ q : α × ℕ → Prop, PrimrecPred q ∧ ∀ a, p a ↔ ∃ k, q (a,k) := by
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp hp
  let q : α × ℕ → Prop := fun z => (Nat.Partrec.Code.evaln z.2 c (Encodable.encode z.1)).isSome
  have hq : PrimrecPred q := by
    apply Primrec.primrecPred
    simpa [q] using (Primrec.option_isSome.comp
      (Nat.Partrec.Code.primrec_evaln.comp
        ((Primrec.snd.pair (Primrec.const c)).pair (Primrec.encode.comp Primrec.fst))))
  refine ⟨q,hq,fun a=>?_⟩
  have hd : (Nat.Partrec.Code.eval c (Encodable.encode a)).Dom ↔ p a := by
    rw [hc]
    simp [Part.assert]
  rw [←hd,Part.dom_iff_mem]
  simp only [Nat.Partrec.Code.evaln_complete]
  change (∃ x k, x ∈ Nat.Partrec.Code.evaln k c (Encodable.encode a)) ↔
    ∃ k, (Nat.Partrec.Code.evaln k c (Encodable.encode a)).isSome
  simp only [Option.isSome_iff_exists]
  aesop

/-- Existential search over a decidable computable relation is r.e. -/
theorem exists_nat {q : α × ℕ → Prop} (hq : ComputablePred q) :
    REPred (fun a => ∃ k, q (a,k)) := by
  classical
  have hc : Computable (fun z : α × ℕ => if q z then some () else none) :=
    by simpa [Bool.cond_decide] using
      hq.decide.cond (Computable.const (some ())) (Computable.const none)
  have hh := (Partrec.rfindOpt hc.to₂).dom_re
  apply hh.of_eq
  intro a
  simp [Nat.rfindOpt_dom]

theorem comp {p : β → Prop} (hp : REPred p) {f : α → β} (hf : Computable f) :
    REPred (fun a=>p (f a)) := hp.comp hf

theorem exists_of_primrec {q : α × β → Prop} (hq : PrimrecPred q) :
    REPred (fun a=>∃ b,q (a,b)) := by
  let q' : α × ℕ → Prop := fun z => ∃ b∈(Encodable.decode (α:=β) z.2).toList,q (z.1,b)
  have hq' : PrimrecPred q' := by
    have hb : PrimrecRel (fun b a => q (a,b)) := hq.comp (Primrec.snd.pair Primrec.fst)
    exact hb.exists_mem_list.comp
      (Primrec.optionToList.comp (Primrec.decode.comp Primrec.snd)) Primrec.fst
  apply (exists_nat hq'.computablePred).of_eq
  intro a
  constructor
  · rintro ⟨k,b,_,hb⟩; exact ⟨b,hb⟩
  · rintro ⟨b,hb⟩
    exact ⟨Encodable.encode b,b,by simp,hb⟩

theorem exists_re {q : α × β → Prop} (hq : REPred q) :
    REPred (fun a=>∃ b,q (a,b)) := by
  obtain ⟨v,hv,hviff⟩ := certificate hq
  have hh : PrimrecPred (fun z : α × (β×ℕ) => v ((z.1,z.2.1),z.2.2)) :=
    hv.comp ((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd))
  apply (exists_of_primrec hh).of_eq
  intro a
  simp only [Prod.exists,←hviff]

theorem and {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred (fun a=>p a ∧ q a) := by
  have hh := (hp.bind (hq.comp Computable.fst).to₂).dom_re
  apply hh.of_eq
  intro a
  simp [Part.assert]

theorem or {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred (fun a=>p a ∨ q a) := by
  obtain ⟨f,hf,h⟩ := Partrec.merge' hp hq
  apply hf.dom_re.of_eq
  intro a
  simpa [Part.assert] using (h a).2

/-- A finite conjunction of r.e. predicates is r.e. uniformly in its list. -/
theorem forall_mem_list {p : α → Prop} (hp : REPred p) :
    REPred (fun L : List α => ∀ a∈L,p a) := by
  obtain ⟨q,hq,hiff⟩ := certificate hp
  have hv : PrimrecPred (fun z : List α × List (α×ℕ) =>
      z.2.map Prod.fst=z.1 ∧ ∀ c∈z.2,q c) :=
    (Primrec.eq.comp
      (Primrec.list_map Primrec.snd (Primrec.fst.comp Primrec.snd).to₂) Primrec.fst).and
      (hq.forall_mem_list.comp Primrec.snd)
  apply (exists_of_primrec hv).of_eq
  intro L
  constructor
  · rintro ⟨cs,hcs,hqcs⟩ a ha
    change cs.map Prod.fst=L at hcs
    rw [←hcs] at ha
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    exact (hiff c.1).mpr ⟨c.2,hqcs c hc⟩
  · intro h
    induction L with
    | nil => exact ⟨[],rfl,by simp⟩
    | cons a L ih =>
      obtain ⟨k,hk⟩ := (hiff a).mp (h a (by simp))
      obtain ⟨cs,hcs,hqcs⟩ := ih (fun b hb=>h b (by simp [hb]))
      exact ⟨(a,k)::cs,by simp [hcs],by simpa using And.intro hk hqcs⟩

end UniversalGroup.RecursiveEnumerable
