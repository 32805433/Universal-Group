module

public import UniversalGroup.Simulator.Recognition.Algebra

@[expose] public section

/-!
# Forward simulation of the positive rewriting system

Each positive rewrite is multiplication on the left by an element of
`⟨c,d⟩` and on the right by an element of `⟨c,e⟩`. Since `f` centralizes
the former and `q = t f⁻¹` the latter, a recognized word gives an element
of `⟨c,d,T⟩`. No subgroup-intersection theorem is used.
-/

namespace UniversalGroup.SimulatorRecognitionForward
noncomputable section
set_option maxHeartbeats 800000

private theorem pow_mul_eq_mul_pow_of_mul_eq {G : Type*} [Group G]
    {a b c : G} (h : a * b = b * c) (n : ℕ) :
    a ^ n * b = b * c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc, ih, ← mul_assoc, h, mul_assoc, ← pow_succ']

private theorem evalPositive_append {G : Type*} [Group G]
    (s₁ s₂ : G) (u v : List (Fin 2)) :
    evalPositive s₁ s₂ (u ++ v) =
      evalPositive s₁ s₂ u * evalPositive s₁ s₂ v := by
  simp [evalPositive]

private theorem evalPositive_commute {G : Type*} [Group G]
    (s₁ s₂ c : G) (h₁ : Commute s₁ c) (h₂ : Commute s₂ c)
    (w : List (Fin 2)) :
    Commute (evalPositive s₁ s₂ w) c := by
  induction w with
  | nil => simp [evalPositive]
  | cons a w ih =>
      change Commute
        ((if a = 0 then s₁ else s₂) * evalPositive s₁ s₂ w) c
      apply Commute.mul_left
      · by_cases ha : a = 0 <;> simp [ha, h₁, h₂]
      · exact ih

private theorem d_transport {G : Type*} [Group G]
    (d s₁ s₂ : G)
    (hd : ∀ s ∈ ({s₁, s₂} : Set G), d ^ 4 * s = s * d)
    (u : List (Fin 2)) (i : ℕ) :
    d ^ (i * 4 ^ u.length) * evalPositive s₁ s₂ u =
      evalPositive s₁ s₂ u * d ^ i := by
  induction u with
  | nil => simp [evalPositive]
  | cons a u ih =>
      have hs : d ^ 4 * (if a = 0 then s₁ else s₂) =
          (if a = 0 then s₁ else s₂) * d := by
        by_cases ha : a = 0
        · simpa [ha] using hd s₁ (by simp)
        · simpa [ha] using hd s₂ (by simp)
      have hexp : i * 4 ^ (a :: u).length = 4 * (i * 4 ^ u.length) := by
        simp only [List.length_cons, pow_succ]
        ac_rfl
      calc
        d ^ (i * 4 ^ (a :: u).length) *
              evalPositive s₁ s₂ (a :: u) =
            (d ^ 4) ^ (i * 4 ^ u.length) *
              ((if a = 0 then s₁ else s₂) *
                evalPositive s₁ s₂ u) := by
          rw [hexp, pow_mul]
          rfl
        _ = ((d ^ 4) ^ (i * 4 ^ u.length) *
              (if a = 0 then s₁ else s₂)) *
                evalPositive s₁ s₂ u := by rw [← mul_assoc]
        _ = ((if a = 0 then s₁ else s₂) *
              d ^ (i * 4 ^ u.length)) *
                evalPositive s₁ s₂ u := by
          rw [pow_mul_eq_mul_pow_of_mul_eq hs]
        _ = (if a = 0 then s₁ else s₂) *
              (d ^ (i * 4 ^ u.length) *
                evalPositive s₁ s₂ u) := by rw [mul_assoc]
        _ = (if a = 0 then s₁ else s₂) *
              (evalPositive s₁ s₂ u * d ^ i) := by rw [ih]
        _ = evalPositive s₁ s₂ (a :: u) * d ^ i := by
          simp only [evalPositive, List.map_cons, List.prod_cons, mul_assoc]

private theorem e_transport {G : Type*} [Group G]
    (e s₁ s₂ : G)
    (he : ∀ s ∈ ({s₁, s₂} : Set G), e * s = s * e ^ 4)
    (u : List (Fin 2)) (i : ℕ) :
    e ^ i * evalPositive s₁ s₂ u =
      evalPositive s₁ s₂ u * e ^ (i * 4 ^ u.length) := by
  induction u generalizing i with
  | nil => simp [evalPositive]
  | cons a u ih =>
      have hs : e * (if a = 0 then s₁ else s₂) =
          (if a = 0 then s₁ else s₂) * e ^ 4 := by
        by_cases ha : a = 0
        · simpa [ha] using he s₁ (by simp)
        · simpa [ha] using he s₂ (by simp)
      have hexp : 4 * i * 4 ^ u.length = i * 4 ^ (a :: u).length := by
        simp only [List.length_cons, pow_succ]
        ac_rfl
      calc
        e ^ i * evalPositive s₁ s₂ (a :: u) =
            (e ^ i * (if a = 0 then s₁ else s₂)) *
              evalPositive s₁ s₂ u := by
          simp only [evalPositive, List.map_cons, List.prod_cons, mul_assoc]
        _ = ((if a = 0 then s₁ else s₂) * (e ^ 4) ^ i) *
              evalPositive s₁ s₂ u := by
          rw [pow_mul_eq_mul_pow_of_mul_eq hs]
        _ = (if a = 0 then s₁ else s₂) *
              (e ^ (4 * i) * evalPositive s₁ s₂ u) := by
          rw [pow_mul, mul_assoc]
        _ = (if a = 0 then s₁ else s₂) *
              (evalPositive s₁ s₂ u *
                e ^ (4 * i * 4 ^ u.length)) := by rw [ih]
        _ = evalPositive s₁ s₂ (a :: u) *
              e ^ (i * 4 ^ (a :: u).length) := by
          rw [hexp]
          simp only [evalPositive, List.map_cons, List.prod_cons, mul_assoc]

private theorem pack_context {G : Type*} [Group G]
    (dI dn en L X R eJ : G) (hd : dI * L = L * dn)
    (he : en * R = R * eJ) :
    dI * (L * X * R) * eJ = L * (dn * X * en) * R := by
  calc
    dI * (L * X * R) * eJ = (dI * L) * X * (R * eJ) := by
      simp only [mul_assoc]
    _ = (L * dn) * X * (en * R) := by rw [hd, ← he]
    _ = L * (dn * X * en) * R := by simp only [mul_assoc]

private theorem conjugate_context {G : Type*} [Group G]
    (c L X Y R : G) (hL : Commute L c) (hR : Commute R c)
    (hXY : c⁻¹ * X * c = Y) :
    c⁻¹ * (L * X * R) * c = L * Y * R := by
  have hcL : c⁻¹ * L = L * c⁻¹ :=
    (Commute.inv_left_iff.mpr hL.symm).eq
  calc
    c⁻¹ * (L * X * R) * c = (c⁻¹ * L) * X * (R * c) := by
      simp only [mul_assoc]
    _ = (L * c⁻¹) * X * (c * R) := by rw [hcL, hR.eq]
    _ = L * (c⁻¹ * X * c) * R := by simp only [mul_assoc]
    _ = L * Y * R := by rw [hXY]

open SimulatorRelations
variable (D : CodeWords)

/-- The left coefficient subgroup for positive simulation. -/
def CD : Subgroup (simulatorL D).Group := Subgroup.closure {c D, d D}
/-- The right coefficient subgroup for positive simulation. -/
def CE : Subgroup (simulatorL D).Group := Subgroup.closure {c D, e D}

private theorem c_mem_CD : c D ∈ CD D := Subgroup.subset_closure (by simp)
private theorem d_mem_CD : d D ∈ CD D := Subgroup.subset_closure (by simp)
private theorem c_mem_CE : c D ∈ CE D := Subgroup.subset_closure (by simp)
private theorem e_mem_CE : e D ∈ CE D := Subgroup.subset_closure (by simp)

private theorem d_positive (w : PositiveWord) (i : ℕ) :
    d D ^ (i * 4 ^ w.length) * positive D w = positive D w * d D ^ i := by
  apply d_transport
  intro x hx
  rcases hx with rfl | hx
  · exact d_power D 0
  · exact Set.mem_singleton_iff.mp hx ▸ d_power D 1

private theorem e_positive (w : PositiveWord) (i : ℕ) :
    e D ^ i * positive D w = positive D w * e D ^ (i * 4 ^ w.length) := by
  apply e_transport
  intro x hx
  rcases hx with rfl | hx
  · exact e_power D 0
  · exact Set.mem_singleton_iff.mp hx ▸ e_power D 1

private theorem positive_c (w : PositiveWord) : Commute (positive D w) (c D) :=
  evalPositive_commute _ _ _ (c_s D 0).symm (c_s D 1).symm w

private theorem positive_append (w v : PositiveWord) :
    positive D (w ++ v) = positive D w * positive D v :=
  evalPositive_append _ _ w v

/-- A single rule, with arbitrary positive contexts, is a double-coset move. -/
theorem rule_simulation (l r : PositiveWord) (i : Fin 3) :
    ∃ a ∈ CD D, ∃ b ∈ CE D,
      positive D (l ++ D.E i ++ r) = a * positive D (l ++ D.F i ++ r) * b := by
  let n := i.val + 1
  let I := n * 4 ^ l.length
  let J := n * 4 ^ r.length
  have hd := d_positive D l n
  have he := e_positive D r n
  have hpack (w : PositiveWord) :
      d D ^ I * positive D (l ++ w ++ r) * e D ^ J =
        positive D l * (d D ^ n * positive D w * e D ^ n) * positive D r := by
    rw [positive_append, positive_append]
    exact pack_context _ _ _ _ _ _ _ hd he
  have hh : (c D)⁻¹ * (d D ^ I * positive D (l ++ D.F i ++ r) * e D ^ J) * c D =
      d D ^ I * positive D (l ++ D.E i ++ r) * e D ^ J := by
    rw [hpack, hpack]
    exact conjugate_context _ _ _ _ _ (positive_c D l) (positive_c D r)
      (rewriting_normalized D i)
  refine ⟨(d D ^ I)⁻¹ * (c D)⁻¹ * d D ^ I,
    (CD D).mul_mem ((CD D).mul_mem ((CD D).inv_mem ((CD D).pow_mem (d_mem_CD D) I))
      ((CD D).inv_mem (c_mem_CD D))) ((CD D).pow_mem (d_mem_CD D) I),
    e D ^ J * c D * (e D ^ J)⁻¹,
    (CE D).mul_mem ((CE D).mul_mem ((CE D).pow_mem (e_mem_CE D) J) (c_mem_CE D))
      ((CE D).inv_mem ((CE D).pow_mem (e_mem_CE D) J)), ?_⟩
  have h := congrArg (fun z => (d D ^ I)⁻¹ * z * (e D ^ J)⁻¹) hh
  simpa [mul_assoc] using h.symm

/-- Forward simulation in the literal thirteen-relator group. -/
theorem simulation {w v : PositiveWord} (hwv : PositiveEq D.rules w v) :
    ∃ a ∈ CD D, ∃ b ∈ CE D, positive D w = a * positive D v * b := by
  have hstep {w v : PositiveWord} (hh : PositiveStep D.rules w v) :
      ∃ a ∈ CD D, ∃ b ∈ CE D, positive D w = a * positive D v * b := by
    rcases hh with ⟨l,r,x,y,⟨i,hxy⟩,h⟩
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hxy
    obtain ⟨a,ha,b,hb,heq⟩ := rule_simulation D l r i
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨a,ha,b,hb,heq⟩
    · refine ⟨a⁻¹,(CD D).inv_mem ha,b⁻¹,(CE D).inv_mem hb,?_⟩
      rw [heq]
      group
  induction hwv with
  | refl => exact ⟨1,(CD D).one_mem,1,(CE D).one_mem,by simp⟩
  | @tail v z h hz ih =>
    obtain ⟨a,ha,b,hb,heq⟩ := ih
    obtain ⟨a',ha',b',hb',heq'⟩ := hstep hz
    refine ⟨a*a',(CD D).mul_mem ha ha',b'*b,(CE D).mul_mem hb' hb,?_⟩
    rw [heq,heq']
    group

/-- The simulator's `f` centralizes all left simulation coefficients. -/
theorem f_commute_CD {x : (simulatorL D).Group} (hx : x ∈ CD D) : Commute (f D) x := by
  apply PositiveEvaluation.commute_closure (MonoidHom.id _) (f D) {c D,d D} ?_ hx
  intro z hz
  rcases hz with rfl | hz
  · exact (c_f D).symm
  · exact Set.mem_singleton_iff.mp hz ▸ (d_f D).symm

/-- The normalized stable letter `q=t*f⁻¹` centralizes all right coefficients. -/
theorem q_commute_CE {x : (simulatorL D).Group} (hx : x ∈ CE D) : Commute (q D) x := by
  apply PositiveEvaluation.commute_closure (MonoidHom.id _) (q D) {c D,e D} ?_ hx
  intro z hz
  rcases hz with rfl | hz
  · exact (c_q D).symm
  · exact Set.mem_singleton_iff.mp hz ▸ (e_q D).symm

/-- The distinguished generator `T` of the centralizer subgroup. -/
def target : (simulatorL D).Group := (simulatorL D).evalWord (simulatorLWords.T D)

theorem target_eq : target D = positive D D.P * q D * (positive D D.P)⁻¹ * f D := by
  simp [target, SimulatorWords.T, SimulatorWords.positive, FP.evalWord,
    simulatorLWords, positive, q, t, f, s, evalPositive, generators, mul_assoc]

theorem delta_eq (w : PositiveWord) : simulatorDelta D w =
    positive D (w.flatMap D.code ++ D.P) * q D *
      (positive D (w.flatMap D.code ++ D.P))⁻¹ * f D := by
  simp [simulatorDelta, SimulatorWords.delta, SimulatorWords.T, SimulatorWords.bar,
    SimulatorWords.positive, FP.evalWord, simulatorLWords, positive, q, t, f, s,
    evalPositive, generators, List.prod_append, mul_assoc]

theorem CD_le_D : CD D ≤ simulatorD D := by
  rw [CD, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · exact Subgroup.subset_closure ⟨0, by simp [FP.evalWord, simulatorLWords, c, generators]⟩
  · subst x
    exact Subgroup.subset_closure ⟨1, by simp [FP.evalWord, simulatorLWords, d, generators]⟩

theorem target_mem_D : target D ∈ simulatorD D :=
  Subgroup.subset_closure ⟨2, rfl⟩

/-- Simulation to the marker expresses `Δ(w)` as a conjugate of `T`
by an element of `⟨c,d⟩`. -/
theorem delta_conjugate (w : PositiveWord)
    (hw : PositiveEq D.rules (w.flatMap D.code ++ D.P) D.P) :
    ∃ a ∈ CD D, simulatorDelta D w = a * target D * a⁻¹ := by
  obtain ⟨a,ha,b,hb,heq⟩ := simulation D hw
  refine ⟨a,ha,?_⟩
  have hq : b * q D * b⁻¹ = q D := (q_commute_CE D hb).symm.mul_inv_cancel
  have hf : a⁻¹ * f D = f D * a⁻¹ := (f_commute_CD D ha).inv_right.symm.eq
  calc
    simulatorDelta D w = a * (positive D D.P * (b * q D * b⁻¹) *
        (positive D D.P)⁻¹) * a⁻¹ * f D := by
      rw [delta_eq,heq]
      group
    _ = a * (positive D D.P * q D * (positive D D.P)⁻¹) * a⁻¹ * f D := by rw [hq]
    _ = a * (positive D D.P * q D * (positive D D.P)⁻¹ * f D) * a⁻¹ := by
      simp only [mul_assoc]
      rw [hf]
    _ = a * target D * a⁻¹ := by rw [target_eq]

/-- Forward recognition in the literal simulator, before invoking a coding datum. -/
theorem delta_mem_D_of_positiveEq (w : PositiveWord)
    (hw : PositiveEq D.rules (w.flatMap D.code ++ D.P) D.P) :
    simulatorDelta D w ∈ simulatorD D := by
  obtain ⟨a,ha,heq⟩ := delta_conjugate D w hw
  rw [heq]
  exact (simulatorD D).mul_mem
    ((simulatorD D).mul_mem (CD_le_D D ha) (target_mem_D D))
    ((simulatorD D).inv_mem (CD_le_D D ha))

/-- A recognized input word supplies an element of the centralizer subgroup. -/
theorem delta_mem_D (G : PreparedInput) (datum : ValievDatum G) (w : PositiveWord)
    (hw : PositiveEq G.monoidRules w []) :
    simulatorDelta datum.toCodeWords w ∈ simulatorD datum.toCodeWords :=
  delta_mem_D_of_positiveEq datum.toCodeWords w ((datum.recognizes w).mp hw)

/-- The entire recognition subgroup lies in the centralizer subgroup. -/
theorem recognition_le_D (G : PreparedInput) (datum : ValievDatum G) :
    recognitionSubgroup G datum.toCodeWords ≤ simulatorD datum.toCodeWords := by
  rw [recognitionSubgroup, Subgroup.closure_le]
  rintro x ⟨w,hw,rfl⟩
  exact delta_mem_D G datum w hw

end
end UniversalGroup.SimulatorRecognitionForward
