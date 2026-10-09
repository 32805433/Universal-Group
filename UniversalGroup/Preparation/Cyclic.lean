module

public import UniversalGroup.Preparation.Reflections

@[expose] public section

/-! Cyclic order-four copies used by the preparation HNN extensions. -/

namespace UniversalGroup.PreparationCyclic
noncomputable section

abbrev C4 := Multiplicative (ZMod 4)
def generator : C4 := Multiplicative.ofAdd 1

@[simp] theorem generator_fourthPower : generator^4=1 := by decide

variable {H : Type*} [Group H]

/-- The cyclic homomorphism determined by an element whose fourth power is one. -/
def hom (x : H) (hx : x^4=1) : C4 →* H where
  toFun z := x ^ z.toAdd.val
  map_one' := by simp
  map_mul' z w := by
    change x ^ (z.toAdd+w.toAdd).val = x ^ z.toAdd.val * x ^ w.toAdd.val
    rw [ZMod.val_add,← pow_add]
    conv_rhs => rw [← Nat.mod_add_div (z.toAdd.val+w.toAdd.val) 4]
    rw [pow_add,pow_mul,hx,one_pow,mul_one]

@[simp] theorem hom_generator (x : H) (hx : x^4=1) : hom x hx generator=x := by
  change x ^ (1:ZMod 4).val=x
  rw [show (1:ZMod 4).val=1 by decide,pow_one]

theorem generator_pow_val (x : C4) : generator ^ x.toAdd.val=x := by
  change Multiplicative.ofAdd ((x.toAdd.val:ℕ) • (1:ZMod 4))=x
  simp

/-- Homomorphisms from C4 are determined by its distinguished generator. -/
theorem hom_ext {f g : C4 →* H} (h : f generator=g generator) : f=g := by
  apply MonoidHom.ext
  intro x
  rw [←generator_pow_val x,map_pow,map_pow,h]

theorem hom_injective (x : H) (hx : x^4=1) (rho : H →* C4)
    (hrho : rho x=generator) : Function.Injective (hom x hx) := by
  have hh : rho.comp (hom x hx)=MonoidHom.id C4 := by
    apply hom_ext
    simpa only [MonoidHom.comp_apply,hom_generator,MonoidHom.id_apply] using hrho
  intro a b hab
  have h := congrArg rho hab
  simpa only [← MonoidHom.comp_apply,hh,MonoidHom.id_apply] using h

/-- The common-order input obtained by multiplying the reflection generators
by an independent central element of order four. -/
abbrev ReflectionProduct (Q : FP n m) := (PreparationReflections.presentation Q).Group × C4

def reflectionValues (Q : FP n m) : Fin (n+n+1) → ReflectionProduct Q :=
  Fin.lastCases (1,generator) (fun i => (PreparationReflections.involutions Q i,generator))

@[simp] theorem reflectionValues_projection (Q : FP n m) (i : Fin (n+n+1)) :
    (reflectionValues Q i).2=generator := by
  refine Fin.lastCases ?_ (fun j=>?_) i <;> simp [reflectionValues]

theorem reflectionValues_fourthPower (Q : FP n m) (i : Fin (n+n+1)) :
    reflectionValues Q i ^4=1 := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp [reflectionValues,generator_fourthPower]
  · have h := PreparationReflections.involutions_squared Q j
    have h4 : PreparationReflections.involutions Q j ^4=1 := by
      calc
        _=(PreparationReflections.involutions Q j ^2)^2 := by rw [←pow_mul]
        _=1 := by rw [h,one_pow]
    simp [reflectionValues,h4,generator_fourthPower]

/-- These order-four elements generate the reflection product. -/
theorem reflectionValues_generate (Q : FP n m) :
    Subgroup.closure (Set.range (reflectionValues Q))=⊤ := by
  let S := Subgroup.closure (Set.range (reflectionValues Q))
  have hz : ((1,generator) : ReflectionProduct Q)∈S := by
    exact Subgroup.subset_closure ⟨Fin.last (n+n),by simp [reflectionValues]⟩
  have hi (i : Fin (n+n)) : ((PreparationReflections.involutions Q i,1) :
      ReflectionProduct Q)∈S := by
    have h : reflectionValues Q i.castSucc∈S := Subgroup.subset_closure ⟨_,rfl⟩
    have hm:=S.mul_mem h (S.inv_mem hz)
    simpa [reflectionValues] using hm
  have hleft : ∀g : (PreparationReflections.presentation Q).Group,(g,1)∈S := by
    have hle : Subgroup.closure (Set.range (PreparationReflections.involutions Q)) ≤
        S.comap (MonoidHom.inl _ C4) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i,rfl⟩
      exact hi i
    rw [PreparationReflections.involutions_generate] at hle
    intro g
    exact hle (Subgroup.mem_top g)
  have hright (z : C4) : ((1,z) : ReflectionProduct Q)∈S := by
    have h:=S.pow_mem hz z.toAdd.val
    simpa only [Prod.pow_mk,one_pow,generator_pow_val] using h
  apply top_unique
  rintro ⟨g,z⟩ _
  exact (by simpa using S.mul_mem (hleft g) (hright z))

end
end UniversalGroup.PreparationCyclic
