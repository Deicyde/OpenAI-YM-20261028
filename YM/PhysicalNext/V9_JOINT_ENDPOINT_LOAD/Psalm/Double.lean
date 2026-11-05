import YM.Next.WARD_BIN.Flags
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Line

/-!
# The negative-log principal E singleton's nonlinear remainder :
parameter-uniform input currencies, including for its lambda derivative and
honest secant proof at the SAME procedure. No estimates on products with
partners by independently applying this singleton!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm.Solo
open Filter Function Set Lattice Wilson RG Tree Pressure Precision Bid Next.SectorChange ProjectorNext.Equivariance
    Heir AnalyticBridge.LocalGaussian AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {f : Side} {V : Config G f} {n : ℕ} {X : Support f} {o : Site f} {P : BudgetPoint} {F : Config G f → ℝ}
    {θ τ K : ℝ} {H : ℝ → ℝ → ℝ}

/-- H γ y is the *coefficient* of Γ, so actual remainder sign refers to `γ*H γ y`. Only E enters with
this substitution. No reinterpretation of equality of logs at a
vanishing cutoff. Individual derivatives bought using scalar kernel calculus
at fixed γ; joint derivatives and covariance scoring later. -/
structure Wholesome (H : ℝ → ℝ → ℝ) : Prop where
  joint : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1*H p.1 p.2)
  each γ : ContDiff ℝ ∞ (H γ)
  flat γ : H γ 0 = 0
  quiet γ : fderiv ℝ (H γ) 0 = 0



structure Marked (H : ℝ → ℝ → ℝ) (n : ℕ) (K : ℝ) : Prop extends Wholesome H where
  fees {f : Side} {G : Gauge} (V : Config G f) (F : Config G f → ℝ) (test : Directions G f → Prop) {τ : ℝ} : τ ≤ 1 → Ticket test n V τ 1 F →
    ∀ γ : ℝ, |γ| ≤ 1 → Ticket test n V (K*τ^2) 1 (H γ ∘ F)
lemma Marked.cost (h : Marked H P.order K) (hF : P.Regular X F) (hτ : P.supBounds o X F τ) (he : τ≤1) (γ : ℝ) (hγ : |γ|≤1) : P.supBounds o X (H γ ∘ F) (K*τ^2) := by
  have hh V (hV : Healthy P.threshold X V) : Ticket (P.dirBound o) P.order V τ 1 F := ⟨hF.smooth V hV,hτ.1,zero_le_one,fun l hl h => by simpa only [one_pow,mul_one] using hτ.2 V hV l hl h⟩
  refine ⟨(h.fees 1 F _ he (hh 1 (flat_ok ..)) γ hγ).price_nonneg,fun V hV l hl hA => ?_⟩
  simpa only [one_pow,mul_one] using (h.fees V F _ he (hh V hV) γ hγ).price l hl hA

def transform (φ : ℝ → ℝ) (θ γ x : ℝ) := φ (γ*θ*x)/γ
lemma transform_diff (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hv : φ 0=0) (hd : fderiv ℝ φ 0=0) (θ : ℝ) : Wholesome (transform φ θ) := by
  unfold transform
  have he (p : ℝ×ℝ) : p.1*(φ (p.1*θ*p.2)/p.1)=φ (p.1*θ*p.2) := by
    by_cases h : p.1=0; · rw [h,zero_mul,zero_mul,zero_mul,hv]
    field_simp
  refine ⟨by simp_rw [he]; fun_prop, fun γ => by fun_prop,fun γ => by rw [mul_zero,hv,zero_div],fun γ=>?_⟩
  let f (x:ℝ):=γ*θ*x
  have h := hφ.differentiable (by simp)
  change fderiv ℝ ((fun x : ℝ => x/γ) ∘ (φ ∘ f)) 0=0; rw [fderiv_comp, fderiv_comp, show f 0=0 from mul_zero _, hd]; simp
  all_goals fun_prop

lemma unitize {D : Directions G f → Prop} {w r : ℝ} (hr : 1 ≤ r) (h : Ticket D n V w r F) : Ticket D n V (w*r^n) 1 F := ⟨h.smooth,mul_nonneg h.price_nonneg (by positivity),zero_le_one,
    fun l hl hA => by rw [one_pow,mul_one]; exact (h.price l hl hA).trans (by gcongr; exact h.price_nonneg)⟩

lemma marked_of_pos {H : ℝ→ℝ→ℝ} (h : Wholesome H) (he : ∀ {f : Side} {G : Gauge} (V : Config G f) (F : Config G f → ℝ) (test : Directions G f → Prop) {τ : ℝ}, 0 < τ → τ ≤ 1 → Ticket test n V τ 1 F →
    ∀ γ : ℝ, |γ| ≤ 1 → Ticket test n V (K*τ^2) 1 (H γ ∘ F)) : Marked H n K := by
  refine ⟨h, fun {f G} V F test {τ} hτ hF γ hγ => ?_⟩
  rcases eq_or_lt_of_le hF.price_nonneg with hT|hT; swap; exact he _ _ _ hT hτ hF _ hγ
  subst τ
  have hh := he _ _ _ zero_lt_one le_rfl (hF.mono zero_le_one le_rfl) γ hγ
  refine ⟨hh.smooth,(by simp),zero_le_one,fun l hl hA => ?_⟩
  have ht : ContinuousAt (fun τ : ℝ => (K*τ^2)*(1:ℝ)^l.length) 0 := by fun_prop
  refine ge_of_tendsto (ht.tendsto.mono_left nhdsWithin_le_nhds : Tendsto _ (𝓝[>] (0:ℝ)) _) ?_
  filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ)),nhdsWithin_le_nhds (α:=ℝ) (ge_mem_nhds zero_lt_one)] with τ hτ he'
  exact (he V F _ hτ he' (hF.mono (show 0<τ from hτ).le le_rfl) γ hγ).price l hl hA

theorem double (φ : ℝ→ℝ) (h : ContDiff ℝ ∞ φ) (h0 : φ 0=0) (hd : fderiv ℝ φ 0=0) (n : ℕ) :
    ∃ K : ℝ, 0≤K ∧ ∀ θ : ℝ, |θ| ≤ 1 → Marked (transform φ θ) n (K*θ^2) := by
  obtain ⟨K,hK,hf⟩ := Farewell.still h h0 hd (s:=1) zero_le_one n
  have hw : 1 ≤ climbing n 2 := one_le_two.trans (climbing_le n zero_le_two)
  refine ⟨K* (climbing n 2)^n,by positivity,fun θ hθ => marked_of_pos (transform_diff φ h h0 hd θ) (fun {f G} V F test {τ} ht ht' hT γ hγ => ?_)⟩
  by_cases h₁ : γ*θ=0
  · simpa [transform,Function.comp_apply,Function.comp_def,h₁,h0] using (Ticket.pure (E:=ℝ) (D:=test) (k:=n) (U:=V) (r:=1) zero_le_one 0).mono (by rw [norm_zero]; positivity : ‖(0:ℝ)‖ ≤ K* (climbing n 2)^n * θ^2 * τ^2) le_rfl
  let x:= |γ*θ| *τ; have hx : 0<x := mul_pos (abs_pos.mpr h₁) ht
  have he : x ≤ 1 := mul_le_one₀ (by rw [abs_mul]; exact mul_le_one₀ hγ (abs_nonneg θ) hθ) ht.le ht'
  let a := γ*θ/x; let f W := a • F W
  have ha : |a| *τ = 1 := by unfold a; rw [abs_div,abs_of_pos hx]; unfold x; field_simp
  have ht : Ticket test n V 1 1 f := ha ▸ hT.indiv a
  let g := fun y : ℝ => φ (x • y)
  have hg : ContDiff ℝ ∞ g := by unfold g; fun_prop
  have hp := (ht.tip.inspect (hf x ⟨hx,he⟩ _ ht.base) ((hg.of_le (budgetThrough n)).contDiffAt)).indiv γ⁻¹
  rw [show (1+(1:ℝ))*1=2 from by norm_num] at hp
  apply (unitize hw hp).agree ?_ |>.mono ?_ le_rfl
  · exact Eventually.of_forall (fun W => by simp only [Function.comp_apply,f,a,smul_eq_mul,inv_mul_eq_div,transform]; field_simp [hx.ne'])
  have hγ' : γ ≠ 0 := by intro h; rw [h,zero_mul] at h₁; contradiction
  have hEq : ‖γ⁻¹‖*x^2 ≤ θ^2*τ^2 := by
    rw [Real.norm_eq_abs,abs_inv,inv_mul_eq_div, div_le_iff₀ (abs_pos.mpr hγ')]; unfold x; rw [abs_mul,mul_pow,mul_pow,sq_abs θ,sq (|γ|)]
    nlinarith only [mul_le_mul_of_nonneg_right hγ (show 0≤ θ^2*τ^2*|γ| by positivity)]
  linarith only [mul_le_mul_of_nonneg_right hEq (show 0≤K*(climbing n 2)^n by positivity)]
end YM.PhysicalNext.JointLoad.Psalm.Solo
