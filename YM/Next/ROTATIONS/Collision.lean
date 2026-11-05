import YM.Next.ROTATIONS.Fold
/-!
# Tested distributions with finite collision power

Only the functional on separable Schwartz profiles is needed. Extension is by a common
finite-jet subtraction in product coordinates. No assertion Hartogs growth / positive
Fourier distribution on arbitrary test profiles. -/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe Word OS Row Metric
open scoped Topology ContDiff NNReal ENNReal BigOperators

def rad (x : E4) := ‖x.ofLp‖
def ScaleCap (D : ℕ) (f : E4 → ℂ) := ∃ C : ℝ,0≤C ∧ ∀ (x : E4) (r : ℝ),0<r → r≤1 → r ≤ rad x →
    ‖f x‖ ≤ C*r⁻¹^D
lemma ScaleCap.loosen {d D f} (hp : d≤D) (hd : ScaleCap d f) : ScaleCap D f := by
  obtain ⟨C,hC,h⟩ := hd; refine ⟨C,hC,fun x r hr he hh => (h _ _ hr he hh).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_inv₀ hr).mpr he) hp) hC
lemma rad_pos {x : E4} (h : x≠0) : 0 < rad x := by
  refine norm_pos_iff.mpr ?_; intro hk; apply h; exact (WithLp.ofLp_injective 2) hk

private lemma vanish_power (f : Panels) (D) (j : Axis) (h : flat D (f j)) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ y : E4,rad y ≤ 1 → ‖tensor f y‖ ≤ C*(rad y)^D := by
  have he (k : ℕ) (_ : 0≤k) (hk : k<0+D) : iteratedFDeriv ℝ k (f j) 0 = 0 := norm_eq_zero.mp <| by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,h _ (by omega),norm_zero]
  obtain ⟨C,hC,h⟩ := earnings _ ((f j).smooth ⊤) 0 D he 1
  let c := ∏ l∈Finset.univ.erase j, SchwartzMap.seminorm ℝ 0 0 (f l)
  have hc : 0≤c := Finset.prod_nonneg fun i hi => apply_nonneg _ _
  refine ⟨C*c,mul_nonneg hC hc,fun y hy => ?_⟩
  have H : ‖y j‖ ≤ rad y := norm_le_pi_norm y.ofLp j
  have hu := h (y j) (H.trans hy); rw [norm_iteratedFDeriv_zero] at hu
  rw [tensor_at, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),norm_mul,norm_prod]
  rw [mul_right_comm C]
  exact mul_le_mul (hu.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) H _) hC))
    (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (f i).norm_le_seminorm ℝ _))
    (Finset.prod_nonneg fun i _ => norm_nonneg _) (mul_nonneg hC (pow_nonneg (norm_nonneg _) _))

lemma radical (f : Panels) (D) (j : Axis) (h : flat D (f j)) (k : E4 → ℂ) (hk : ScaleCap D k)
    (hm : Measurable k) : Integrable (fun p : E4 => k p * tensor f p) := by
  let s := {x : E4| rad x≤1}
  have hl : s = (PiLp.continuousLinearEquiv 2 ℝ _).toHomeomorph.symm '' closedBall (0:Axis→ℝ) 1 := by
    ext x
    let e : E4 ≃L[ℝ] (Axis→ℝ) := PiLp.continuousLinearEquiv 2 ℝ _
    change rad x ≤ 1 ↔ ∃ a ∈ closedBall (0:Axis→ℝ) 1, e.symm a=x
    constructor
    · intro hx; exact ⟨e x, by rw [mem_closedBall,dist_zero_right]; exact hx, by simp⟩
    rintro ⟨a,h,rfl⟩; change ‖e (e.symm a)‖≤_; rw [e.apply_symm_apply]; simpa using h
  have hs : IsCompact s := hl ▸ (isCompact_closedBall _ _).image ((PiLp.continuousLinearEquiv 2 ℝ _).symm.continuous)
  obtain ⟨C,hC,hp⟩ := hk
  obtain ⟨K,hK,hq⟩ := vanish_power f D j h
  let L x := k x * tensor f x
  have ha : Measurable L := hm.mul (tensor f).continuous.measurable
  change Integrable L
  refine (show IntegrableOn L (s∪sᶜ) → Integrable L from fun h => by simpa using h) (integrableOn_union.mpr ?_)
  constructor
  · refine Integrable.mono' (integrableOn_const (C:=C*K) hs.measure_lt_top.ne) ha.aestronglyMeasurable ?_
    have he : ∀ᵐ p : E4, p≠0 := by simp only [ae_iff]; simp
    filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hs.measurableSet] with x hx hl
    have hr := rad_pos hx
    exact (norm_mul ..).trans_le ((mul_le_mul (hp x (rad x) hr hl le_rfl) (hq x hl) (norm_nonneg _) ((hp x (rad x) hr hl le_rfl).trans' (norm_nonneg _))).trans_eq (by rw [inv_pow]; field_simp))
  · refine (tensor f).integrable.integrableOn.bdd_mul (c:=C) hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hs.measurableSet.compl] with x hx
    simpa using hp x 1 zero_lt_one le_rfl (le_of_not_ge hx)

/-- Product Taylor subtraction. Along a polar direction chosen in the spectral argument it
agrees exactly when the needed temporal moments are killed. -/
def projections (f : Panels) (D) := fun j => collect D (f j)
def battle (g : E4→ℂ) (D : ℕ) (f : Panels) (y : E4) := g y * (tensor f y - tensor (projections f D) y)
lemma battle_int (g : E4→ℂ) (D) (f : Panels) (hp : ScaleCap D g) (hr : Measurable g) : Integrable (battle g D f) := by
  classical
  let b := projections f D
  let L (s : Finset Axis) (i) := if i∈s then f i else b i
  have he s : Integrable (fun x => g x*(tensor (L s) x-tensor b x)) := by
    induction s using Finset.induction_on with
    | empty => simp only [L,Finset.notMem_empty,↓reduceIte,sub_self,mul_zero]; exact integrable_zero ..
    | insert i s hi ih =>
      let q := update (L s) i (f i-b i)
      have h : Integrable (fun x => g x*tensor q x) := radical q D i (by unfold q; rw [update_self]; exact missed D (f i)) _ hp hr
      refine (h.add ih).congr (ae_of_all _ fun x => ?_)
      have ht : tensor (L (insert i s)) x=tensor q x+tensor (L s) x := by
        rw [show L (insert i s) = update (L s) i (f i) by ext1 j; by_cases hh : j=i <;> simp [L,hh]]
        rw [tensor_update _ _ _ x,tensor_update _ _ _ x]
        have hh := tensor_update (L s) i (L s i) x
        rw [update_eq_self] at hh
        rw [hh,_root_.sub_apply,show L s i=b i by simp [L,hi]]; ring
      dsimp only [Pi.add_apply]; rw [ht]; ring
  have hp := he Finset.univ
  rw [show L Finset.univ=f by simp [L]] at hp
  exact hp

def panelChange (f : Panels) (i : Axis) : Form →ₗ[ℂ] Probe E4 where
  toFun g := tensor (update f i g)
  map_add' g h := by ext1 x; simp only [_root_.add_apply,tensor_update,add_mul]
  map_smul' z g := by
    ext1 x; simp only [_root_.smul_apply,tensor_update]; exact mul_assoc ..

abbrev Paper := MultilinearMap ℂ (fun _ : Axis => Form) ℂ

abbrev axisDec : DecidableEq Axis := inferInstance

def article (g : E4→ℂ) (D : ℕ) (hp : ScaleCap D g) (hr : Measurable g) : Paper where
  toFun f := ∫ y,battle g D f y
  map_update_add' {u} f i x y := by
    have H : u=axisDec := Subsingleton.elim _ _
    subst u
    rw [← integral_add (battle_int g D (update f i x) hp hr) (battle_int g D (update f i y) hp hr)]
    congr 1; funext p
    have hh (x : Form) : projections (update f i x) D = update (projections f D) i (collect D x) := by
      funext j; by_cases h : j=i <;> simp [projections,h]
    simp only [battle,tensor_update, _root_.add_apply,hh,collect_add]; ring
  map_update_smul' {u} f i z x := by
    have H : u=axisDec := Subsingleton.elim _ _
    subst u
    rw [← integral_smul]
    congr 1; funext p
    have hh (x : Form) : projections (update f i x) D = update (projections f D) i (collect D x) := by
      funext j; by_cases h : j=i <;> simp [projections,h]
    simp only [battle,tensor_update,_root_.smul_apply, hh,collect_scale,smul_eq_mul]; ring
lemma article_test {g D hp hr} (f : Panels) (i : Axis) (hf : flat D (f i)) :
    article g D hp hr f= ∫ y,g y*tensor f y := by
  change (∫ y,battle _ _ _ y)=_
  congr 1; funext y; unfold battle; rw [show tensor (projections f D) y=0 from ?_,sub_zero]
  rw [tensor_at]; exact Finset.prod_eq_zero (Finset.mem_univ i) (by unfold projections; rw [all_miss _ _ hf]; rfl)

/-- coordinate-line integration by parts, not through the collision. -/
lemma integrate_both (f g F G : E4→ℂ) (a : Axis)
    (h : Integrable (fun p => f p*g p)) (ht : Integrable (fun p => f p*G p)) (hk : Integrable (fun p => F p*g p))
    (hf : ∀ x : Tang,x≠0 → ∀ t, HasDerivAt (fun u : ℝ => f (make a (u,x))) (F (make a (t,x))) t)
    (hg : ∀ x : Tang,x≠0 → ∀ t, HasDerivAt (fun u : ℝ => g (make a (u,x))) (G (make a (t,x))) t) :
    ∫ p, f p*G p= -(∫ p,F p*g p) := by
  have hh := make_pres a
  have he (f : E4→ℂ) (h : Integrable f) := (hh.integrable_comp_emb (make a).measurableEmbedding).2 h
  have hv (f : E4→ℂ) (h : Integrable f) :
      integral volume f=∫ x : Tang,∫ t : ℝ, f (make a (t,x)) := (hh.integral_comp' f).symm.trans (integral_prod_symm (μ:=volume) (ν:=volume) _ (he f h))
  rw [hv _ ht,hv _ hk, ← integral_neg]; apply integral_congr_ae
  have hl (f : E4→ℂ) (h : Integrable f) : ∀ᵐ x : Tang, Integrable (fun t => f (make a (t,x))) := by
    exact Integrable.prod_left_ae (μ:=volume) (ν:=volume) (f:=fun z : ℝ × Tang => f (make a z)) (he f h)
  have hq : ∀ᵐ x : Tang,x≠0 := by simp only [ae_iff];simp
  filter_upwards [hl _ ht,hl _ hk,hl _ h,hq] with x h₁ h₂ h₃ hx
  exact integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable (L:=ContinuousLinearMap.mul ℝ ℂ) (fun t _ => hf _ hx _) (fun t _ => hg _ hx _) h₁ h₂ h₃

def moved (i : Axis) (f : Panels) := update f i (prime (f i))
theorem moved_deriv (i : Axis) (f : Panels) (x : Tang) (t) : HasDerivAt (fun t => tensor f (make i (t,x)))
    (tensor (moved i f) (make i (t,x))) t := by
  simp_rw [tensor_made]; rw [moved, update_self, tests_update]
  exact ((f i).hasDerivAt t).mul_const _
lemma made_of_ne (i : Axis) (x : Tang) (hx : x≠0) (t) : make i (t,x) ≠ 0 := by
  intro h; apply hx; ext1 j; change ((t,x) : ℝ × Tang).2 j = _; rw [← make_other i (t,x) j,h]; rfl
end YM.Outer
