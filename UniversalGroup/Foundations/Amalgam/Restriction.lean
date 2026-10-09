module

public import UniversalGroup.Foundations.Amalgam.Centralizing
public import Mathlib.Algebra.Group.Subgroup.Finite

@[expose] public section

/-! Restricting the simulator factor in a centralizing amalgam preserves embeddings. -/

namespace UniversalGroup.AmalgamRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem normalWord_reduced {ι : Type*} {F : ι → Type*} [∀ i, Group (F i)]
    {E : Type*} [Group E] {φ : ∀ i, E →* F i}
    (d : Monoid.PushoutI.NormalWord.Transversal φ) (w : Monoid.PushoutI.NormalWord d) :
    Monoid.PushoutI.Reduced φ w.toWord := by
  intro x hx hr
  have hn := w.normalized x.1 x.2 hx
  have hs := congrArg Subtype.val
    ((d.compl x.1).equiv_snd_eq_self_of_mem_of_one_mem (Subgroup.one_mem _) hn)
  have hz := congrArg Subtype.val
    ((d.compl x.1).equiv_snd_eq_one_of_mem_of_one_mem (d.one_mem x.1) hr)
  exact w.ne_one x hx (hs.symm.trans hz)

/-- A reduced amalgam word representing an element of one factor has letters
only from that factor. -/
private theorem reduced_indices {ι : Type*} {F : ι → Type*} [∀ i, Group (F i)]
    {E : Type*} [Group E] {φ : ∀ i, E →* F i}
    (hφ : ∀ i, Function.Injective (φ i)) (w : Monoid.CoprodI.Word F)
    (hw : Monoid.PushoutI.Reduced φ w) (i : ι)
    (hmem : Monoid.PushoutI.ofCoprodI (φ := φ) w.prod ∈
      (Monoid.PushoutI.of (φ := φ) i).range) :
    ∀ x ∈ w.toList, x.1 = i := by
  classical
  obtain ⟨d⟩ := Monoid.PushoutI.NormalWord.transversal_nonempty φ hφ
  obtain ⟨w', hp, hi⟩ := hw.exists_normalWord_prod_eq d
  obtain ⟨g, hg⟩ := hmem
  have hex : ∃ v : Monoid.PushoutI.NormalWord d,
      v.prod = Monoid.PushoutI.of (φ := φ) i g ∧
        ∀ x ∈ v.toList, x.1 = i := by
    by_cases hgr : g ∈ (φ i).range
    · obtain ⟨e, rfl⟩ := hgr
      refine ⟨⟨Monoid.CoprodI.Word.empty, e, by simp⟩, ?_, ?_⟩
      · simp [Monoid.PushoutI.NormalWord.prod, Monoid.PushoutI.of_apply_eq_base]
      · simp [Monoid.CoprodI.Word.empty]
    · let v := Monoid.PushoutI.NormalWord.cons g
        (Monoid.PushoutI.NormalWord.empty : Monoid.PushoutI.NormalWord d)
          (by simp [Monoid.CoprodI.Word.fstIdx, Monoid.PushoutI.NormalWord.empty, Monoid.CoprodI.Word.empty]) hgr
      refine ⟨v, by simp [v], ?_⟩
      intro x hx
      have hx' := hx
      simp [v] at hx'
      exact congrArg Sigma.fst hx'
  obtain ⟨v, hv, hi'⟩ := hex
  have hsame : w' = v := Monoid.PushoutI.NormalWord.prod_injective (hp.trans (hg.symm.trans hv.symm))
  intro x hx
  have hx' : x.1 ∈ v.toList.map Sigma.fst := by
    rw [← hsame, hi]
    exact List.mem_map_of_mem hx
  obtain ⟨y, hy, heq⟩ := List.mem_map.mp hx'
  exact heq.symm.trans (hi' y hy)

universe u
variable {K : Type u} [Group K] (V H : Subgroup K) (G : Type u) [Group G]
open CentralizingAmalgam

abbrev Common := V.comap H.subtype
abbrev Source := Model (Common V H) G
abbrev Target := Model V G

def commonMap : Common V H →* V where
  toFun x := ⟨x, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def factorMap : ∀ i, Factor (Common V H) G i →* Factor V G i
  | .base => H.subtype
  | .product => (commonMap V H).prodMap (MonoidHom.id G)

theorem factorMap_injective (i : Side) : Function.Injective (factorMap V H G i) := by
  cases i
  · exact Subtype.val_injective
  · intro x y h
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : V × G => (z.1 : K)) h
    · change (commonMap V H x.1, x.2) = (commonMap V H y.1, y.2) at h
      exact congrArg (fun z : V × G => z.2) h

/-- Include the subgroup factor and retain the input factor. -/
def hom : Source V H G →* Target V G :=
  CentralizingAmalgam.lift (Common V H) G ((ofBase V G).comp H.subtype) (ofInput V G) (by
    intro x g
    exact commute V G (commonMap V H x) g)

@[simp] theorem hom_ofBase (x : H) :
    hom V H G (ofBase (Common V H) G x) = ofBase V G (x : K) := by
  exact lift_ofBase (Common V H) G _ _ _ x

@[simp] theorem hom_ofInput (g : G) :
    hom V H G (ofInput (Common V H) G g) = ofInput V G g := by
  exact lift_ofInput (Common V H) G _ _ _ g

@[simp] theorem hom_ofProduct (x : Common V H × G) :
    hom V H G (ofProduct (Common V H) G x) =
      ofProduct V G (commonMap V H x.1, x.2) := by
  rw [hom, lift_ofProduct]
  change ofBase V G (commonMap V H x.1) * ofInput V G x.2 = _
  rw [identifies V G (commonMap V H x.1)]
  change ofProduct V G (commonMap V H x.1, 1) * ofProduct V G (1, x.2) = _
  rw [← map_mul]
  simp

theorem hom_factor (i : Side) (x : Factor (Common V H) G i) :
    hom V H G (Monoid.PushoutI.of (φ := diagram (Common V H) G) i x) =
      Monoid.PushoutI.of (φ := diagram V G) i (factorMap V H G i x) := by
  cases i
  · exact hom_ofBase V H G x
  · exact hom_ofProduct V H G x

theorem hom_common (x : Common V H) :
    hom V H G (Monoid.PushoutI.base (diagram (Common V H) G) x) =
      Monoid.PushoutI.base (diagram V G) (commonMap V H x) := by
  rw [← Monoid.PushoutI.of_apply_eq_base (diagram (Common V H) G) Side.base x]
  rw [hom_factor]
  exact Monoid.PushoutI.of_apply_eq_base (diagram V G) Side.base (commonMap V H x)

private theorem factorMap_preimage (i : Side) (x : Factor (Common V H) G i)
    (hx : factorMap V H G i x ∈ (diagram V G i).range) :
    x ∈ (diagram (Common V H) G i).range := by
  cases i
  · change x.val ∈ V.subtype.range at hx
    obtain ⟨v, hv⟩ := hx
    have hxV : x.val ∈ V := hv ▸ v.property
    exact ⟨⟨x, hxV⟩, rfl⟩
  · obtain ⟨v, hv⟩ := hx
    change (v, (1 : G)) = (commonMap V H x.1, x.2) at hv
    refine ⟨x.1, Prod.ext rfl ?_⟩
    exact congrArg (fun z : V × G => z.2) hv

private def mapLetter (x : Σ i, Factor (Common V H) G i) : Σ i, Factor V G i :=
  ⟨x.1, factorMap V H G x.1 x.2⟩

private def mapWord (w : Monoid.CoprodI.Word (Factor (Common V H) G)) :
    Monoid.CoprodI.Word (Factor V G) where
  toList := w.toList.map (mapLetter V H G)
  ne_one := by
    intro l hl
    obtain ⟨x, hx, hxl⟩ := List.mem_map.mp hl
    subst l
    intro h
    apply w.ne_one x hx
    apply factorMap_injective V H G x.1
    rw [map_one]
    exact h
  chain_ne := by
    rw [List.isChain_map]
    exact w.chain_ne

private theorem mapWord_reduced (w : Monoid.CoprodI.Word (Factor (Common V H) G))
    (hw : Monoid.PushoutI.Reduced (diagram (Common V H) G) w) :
    Monoid.PushoutI.Reduced (diagram V G) (mapWord V H G w) := by
  rintro x hx hr
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact hw y hy (factorMap_preimage V H G y.1 y.2 hr)

private theorem hom_word (w : Monoid.CoprodI.Word (Factor (Common V H) G)) :
    hom V H G (Monoid.PushoutI.ofCoprodI (φ := diagram (Common V H) G) w.prod) =
      Monoid.PushoutI.ofCoprodI (φ := diagram V G) (mapWord V H G w).prod := by
  simp only [Monoid.CoprodI.Word.prod, map_list_prod, List.map_map, mapWord]
  congr 1
  apply List.map_congr_left
  intro x hx
  change hom V H G (Monoid.PushoutI.of (φ := diagram (Common V H) G) x.1 x.2) =
    Monoid.PushoutI.of (φ := diagram V G) x.1 (factorMap V H G x.1 x.2)
  exact hom_factor V H G x.1 x.2

private theorem word_mem_base (w : Monoid.CoprodI.Word (Factor (Common V H) G))
    (h : ∀ x ∈ w.toList, x.1 = Side.base) :
    Monoid.PushoutI.ofCoprodI (φ := diagram (Common V H) G) w.prod ∈
      (ofBase (Common V H) G).range := by
  simp only [Monoid.CoprodI.Word.prod, map_list_prod, List.map_map]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  have he := h y hy
  rcases y with ⟨i, y⟩
  cases he
  exact ⟨y, Monoid.PushoutI.ofCoprodI_of _ _⟩

/-- An element of the restricted amalgam mapping into the original simulator
factor already belongs to its own simulator factor. -/
theorem preimage_base (x : Source V H G) (hx : hom V H G x ∈ (ofBase V G).range) :
    x ∈ (ofBase (Common V H) G).range := by
  classical
  obtain ⟨d⟩ := Monoid.PushoutI.NormalWord.transversal_nonempty
    (diagram (Common V H) G) (diagram_injective (Common V H) G)
  let w : Monoid.PushoutI.NormalWord d := Monoid.PushoutI.NormalWord.equiv x
  have hw : w.prod = x := Monoid.PushoutI.NormalWord.equiv.symm_apply_apply x
  have hn := mapWord_reduced V H G w.toWord (normalWord_reduced d w)
  have ht : Monoid.PushoutI.ofCoprodI (φ := diagram V G) (mapWord V H G w.toWord).prod ∈
      (ofBase V G).range := by
    have hh : hom V H G x =
        Monoid.PushoutI.base (diagram V G) (commonMap V H w.head) *
          Monoid.PushoutI.ofCoprodI (φ := diagram V G) (mapWord V H G w.toWord).prod := by
      rw [← hw, Monoid.PushoutI.NormalWord.prod, map_mul, hom_common, hom_word]
    have he : Monoid.PushoutI.base (diagram V G) (commonMap V H w.head) ∈
        (ofBase V G).range := ⟨_, Monoid.PushoutI.of_apply_eq_base _ Side.base _⟩
    exact (Subgroup.mul_mem_cancel_left _ he).mp (hh ▸ hx)
  have hi := reduced_indices (diagram_injective V G) (mapWord V H G w.toWord) hn Side.base ht
  rw [← hw, Monoid.PushoutI.NormalWord.prod]
  apply Subgroup.mul_mem
  · exact ⟨_, Monoid.PushoutI.of_apply_eq_base _ Side.base _⟩
  · apply word_mem_base
    intro y hy
    exact hi (mapLetter V H G y) (List.mem_map_of_mem hy)

theorem hom_injective : Function.Injective (hom V H G) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  obtain ⟨a, rfl⟩ := preimage_base V H G x (hx ▸ Subgroup.one_mem _)
  rw [hom_ofBase] at hx
  have ha : a = 1 := Subtype.ext (ofBase_injective V G (by simpa using hx))
  rw [ha, map_one]

section Congruence
variable {K' : Type u} [Group K'] (V' : Subgroup K')

/-- Maps of a centralizing amalgam are determined by the simulator and input. -/
theorem amalgam_hom_ext {N : Type*} [Group N] {f g : Model V G →* N}
    (hb : ∀ k, f (ofBase V G k) = g (ofBase V G k))
    (hi : ∀ x, f (ofInput V G x) = g (ofInput V G x)) : f = g := by
  let : Nonempty Side := ⟨Side.base⟩
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  apply MonoidHom.ext
  intro x
  cases i
  · exact hb x
  · have hx : ofProduct V G x = ofBase V G x.1 * ofInput V G x.2 := by
      rw [identifies V G x.1]
      change ofProduct V G x = ofProduct V G (x.1, 1) * ofProduct V G (1, x.2)
      rw [← map_mul]
      simp
    change f (ofProduct V G x) = g (ofProduct V G x)
    rw [hx, map_mul, map_mul, hb, hi]

variable (e : K ≃* K') (hV : ∀ k, k ∈ V ↔ e k ∈ V')

/-- Transport the simulator factor through a subgroup-preserving isomorphism. -/
def congrHom : Model V G →* Model V' G :=
  CentralizingAmalgam.lift V G ((ofBase V' G).comp e.toMonoidHom) (ofInput V' G) (by
    intro v g
    exact commute V' G ⟨e v, (hV v).mp v.property⟩ g)

@[simp] theorem congrHom_ofBase (k : K) :
    congrHom V G V' e hV (ofBase V G k) = ofBase V' G (e k) :=
  lift_ofBase V G _ _ _ k

@[simp] theorem congrHom_ofInput (g : G) :
    congrHom V G V' e hV (ofInput V G g) = ofInput V' G g :=
  lift_ofInput V G _ _ _ g

include hV in
theorem symm_preserves (k : K') : k ∈ V' ↔ e.symm k ∈ V := by
  simpa using (hV (e.symm k)).symm

/-- The input group is fixed while the simulator is transported by `e`. -/
def congrEquiv : Model V G ≃* Model V' G where
  toFun := congrHom V G V' e hV
  invFun := congrHom V' G V e.symm (symm_preserves V V' e hV)
  map_mul' := map_mul _
  left_inv x := by
    have h : (congrHom V' G V e.symm (symm_preserves V V' e hV)).comp
        (congrHom V G V' e hV) = MonoidHom.id _ := by
      apply amalgam_hom_ext <;> intro y <;> simp
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h : (congrHom V G V' e hV).comp
        (congrHom V' G V e.symm (symm_preserves V V' e hV)) = MonoidHom.id _ := by
      apply amalgam_hom_ext <;> intro y <;> simp
    exact DFunLike.congr_fun h x

@[simp] theorem congrEquiv_ofBase (k : K) :
    congrEquiv V G V' e hV (ofBase V G k) = ofBase V' G (e k) :=
  congrHom_ofBase V G V' e hV k

@[simp] theorem congrEquiv_ofInput (g : G) :
    congrEquiv V G V' e hV (ofInput V G g) = ofInput V' G g :=
  congrHom_ofInput V G V' e hV g

@[simp] theorem congrEquiv_symm_ofBase (k : K') :
    (congrEquiv V G V' e hV).symm (ofBase V' G k) = ofBase V G (e.symm k) :=
  congrHom_ofBase V' G V e.symm (symm_preserves V V' e hV) k

@[simp] theorem congrEquiv_symm_ofInput (g : G) :
    (congrEquiv V G V' e hV).symm (ofInput V' G g) = ofInput V G g :=
  congrHom_ofInput V' G V e.symm (symm_preserves V V' e hV) g

@[simp] theorem toBase_hom (x : Source V H G) :
    toBase V G (hom V H G x) = (toBase (Common V H) G x : K) := by
  have h : (toBase V G).comp (hom V H G) =
      H.subtype.comp (toBase (Common V H) G) := by
    apply amalgam_hom_ext <;> intro y <;>
      simp only [MonoidHom.comp_apply, hom_ofBase, hom_ofInput, toBase_ofBase, toBase_ofInput]
    all_goals rfl
  exact DFunLike.congr_fun h x

end Congruence

end
end UniversalGroup.AmalgamRestriction
