import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.Next.STATIONARY.OneLoop.Bubbles






set_option autoImplicit false
/-!
# Normalized rate at Earth's angular coordinate, hand to influence.
Uses unit-period torus parameterization, half-open cube with full product
volume. All ∫ use Bochner. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate _root_.Pointwise NNReal ENNReal
variable {G : Gauge} {σ C : ℝ}

section volume
abbrev Gaia := EuclideanSpace ℝ Axis
abbrev exileE : Gaia ≃ᵐ Track := (MeasurableEquiv.toLp 2 (Track)).symm
def cradle : Set Track := {x | ∀ i, x i∈ Set.Ioc (-Real.pi) Real.pi}
def boundsEarth := exileE ⁻¹' cradle
lemma cradle_meas : MeasurableSet cradle := by exact MeasurableSet.univ_pi' fun i => measurableSet_Ioc
lemma earth_meas : MeasurableSet boundsEarth := cradle_meas.preimage exileE.measurable
lemma cradleFront (v) (h : v∈ cradle) : FrontBox v := fun i=> abs_le.mpr ⟨(h i).1.le,(h i).2⟩
def cartWeight : ℝ := ((2*Real.pi)^4)⁻¹
lemma cart_weight_pos : 0<cartWeight := by unfold cartWeight; positivity
lemma earth_bounded (p : Gaia) (h : p∈boundsEarth) : p∈ closedBall 0 (2*Real.pi) := by
  rw [mem_closedBall,dist_zero_right]; exact orbit_boundary _ (cradleFront _ h)
lemma earth_oaks : volume boundsEarth ≠ ⊤ := ((measure_mono (fun _ hp=> earth_bounded _ hp : boundsEarth ⊆ _)).trans_lt (isCompact_closedBall (α:=Gaia) _ _).measure_lt_top).ne
lemma orbs {p : Gaia} (hp : ‖p‖≤1) : p∈boundsEarth := by
  have hv : ∀ i,|exileE p i|≤1 := fun i=> (show |exileE p i|≤‖exileE p‖ from by simpa using norm_le_pi_norm (exileE p) i).trans ((orbit_at _).trans hp)
  change ∀ i,_; intro i; have h := abs_le.mp (hv i); have he := Real.pi_gt_three; constructor <;> linarith [h.1,h.2]

lemma guildDraw (f : Momentum→ℂ) (hp : Firm σ C f) : stock f = (cartWeight:ℂ)* ∫ p : Gaia in boundsEarth, f (axes (exileE p)) := by
  let c := 2*Real.pi
  have hc : 0<c := by unfold c; positivity
  let g p := veils f 0 p
  have hf : stock f = ∫ p,g p ∂globe Axis := by
    have ht := adoption hp.1 (x:=0) (hp.in_range (p:=0) (by simp))
    rw [show Laurent.lens f 0=f by funext i; simp [Laurent.lens], neg_zero,mode_zero,one_mul] at ht; exact ht.symm
  let a (_ : Axis) := - (1/2:ℝ)
  let S : Set Track:= {x | ∀ i,x i∈Set.Ioc (a i) (a i+1)}
  have he (x : Track) : g (Laurent.dress _ x)= f (axes (c • x)) := by
    unfold g; rw [hp.1.steps (hp.in_range (p:=0) (by simp)),zero_add]; apply congr_arg f; ext1 i; simp [c,axes,walk]
  have hS : c • S=cradle := by
    ext p; rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne'];
    have he i : p i/c ∈ Set.Ioc (a i) (a i+1) ↔ p i ∈ Set.Ioc (-Real.pi) Real.pi := by rw [Set.mem_Ioc,Set.mem_Ioc, lt_div_iff₀ hc,div_le_iff₀ hc]; unfold a c; constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    change (∀ i, (c⁻¹ • p) i∈ _)↔∀ i,_
    simp only [Pi.smul_apply,smul_eq_mul, inv_mul_eq_div,he]
  rw [hf,show (∫ p,g p ∂globe Axis)= ∫ p in S,g (Laurent.dress _ p) from UnitAddTorus.integral_preimage g a]
  simp_rw [he];
  change (∫ x : Track in S, (f ∘ axes) (c • x))= _
  rw [Measure.setIntegral_comp_smul_of_pos (f:= f ∘ axes) volume S hc]
  rw [show Module.finrank ℝ Track=4 from Module.finrank_fin_fun ℝ, hS]
  let T := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp Axis
  have h : Measure.map exileE volume=volume := T.map_eq
  rw [← h,setIntegral_map_equiv]; simp only [Complex.real_smul]; rfl
end volume
end YM.Stationary
end

/-!
# Parametric tilt integrability. Raw exponent compact B, differentiate twice
on actual angular torus. Does not bound derivative in µ. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal
variable {G : Gauge} {σ C : ℝ}

section compact
variable (f : ℝ× Gaia →ℂ)
-- Transposes needed t on left.
def plunge (g : ℝ× Gaia →ℂ) (x : ℝ× Gaia) := deriv (fun t : ℝ=> g (t,x.2)) x.1
lemma plunge_green (h : ContDiff ℝ ω f) : ContDiff ℝ ω (plunge f) := by
  have ht (x : ℝ×Gaia) : plunge f x=fderiv ℝ f x (1,0) := by
    unfold plunge; let T:=fun t:ℝ=> (t,x.2)
    have hx : T x.1=x := rfl
    apply HasDerivAt.deriv
    have hu : HasFDerivAt f (fderiv ℝ f x) (T x.1) := by rw [hx]; exact h.differentiable (by simp) _ |>.hasFDerivAt
    exact hu.comp_hasDerivAt x.1 ((hasDerivAt_id x.1).prodMk (hasDerivAt_const ..))
  rw [funext ht]; exact (h.fderiv_right (m:=ω) (by simp)|>.clm_apply (contDiff_const (c:=(1,0))))
lemma astute (f : Gaia →ℂ) (he : Continuous f) : IntegrableOn f boundsEarth volume := (he.continuousOn.integrableOn_compact (isCompact_closedBall (0:Gaia) (2*Real.pi))).mono_set (fun _ h=> earth_bounded _ h)
lemma plunge_ride (h : ContDiff ℝ ω f) (t : ℝ) : deriv (fun t : ℝ=> ∫ x : Gaia in boundsEarth, f (t,x)) t=∫ x : Gaia in boundsEarth, plunge f (t,x) := by
  let S := (closedBall t 1) ×ˢ (closedBall (0:Gaia) (2*Real.pi))
  have hs : IsCompact S := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have he := plunge_green f h
  obtain ⟨A,hA⟩ := (hs.image he.continuous.norm).bddAbove
  let ν : Measure Gaia := volume.restrict boundsEarth
  let F t x := f (t,x); let V t x := plunge f (t,x)
  have hI (x : Gaia)  : ContDiff ℝ ω (fun v=> F v x) := h.comp (contDiff_id.prodMk contDiff_const)
  have hp t : Continuous (F t) := h.continuous.comp (continuous_const.prodMk continuous_id)
  have hz t : Continuous (V t) := he.continuous.comp (continuous_const.prodMk continuous_id)
  haveI : IsFiniteMeasure ν := by unfold ν; exact ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 earth_oaks⟩
  have hw (x y) : HasDerivAt (fun v => F v x) (V y x) y := ((hI x).differentiable (by simp) y).hasDerivAt
  apply HasDerivAt.deriv
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F) (F':=V) (μ:=ν) (Metric.ball_mem_nhds t zero_lt_one) (Eventually.of_forall (fun x=> (hp x).aestronglyMeasurable)) (astute (F t) (hp t)) (hz t |>.aestronglyMeasurable) ?_ (integrable_const A) (Eventually.of_forall (fun x y _ => hw x y))).2
  filter_upwards [ae_restrict_mem earth_meas] with x hx y hy
  exact hA ⟨(y,x),⟨ball_subset_closedBall hy,earth_bounded _ hx⟩,rfl⟩
lemma plunge_dive {x : ℝ→ℂ} : flareY 2 x=deriv (deriv x) 0 := by change iteratedFDeriv ℝ 2 x 0 (fun _=>1)=_; rw [← iteratedDeriv_eq_iteratedFDeriv,iteratedDeriv_succ]; simp
lemma plunge_fare (h : ContDiff ℝ ω f) : flareY 2 (fun t : ℝ=> ∫ x in boundsEarth,f (t,x))= ∫ x in boundsEarth, flareY 2 (fun t : ℝ=> f (t,x)) := by
  simp_rw [plunge_dive]; rw [funext (plunge_ride f h),plunge_ride (plunge f) (plunge_green f h) 0]; rfl
end compact

lemma stroll_size {f : Momentum → Momentum → ℂ} (hf : Firm σ C (starTrack f)) : ContDiff ℝ ω (fun z : ℝ× Gaia => f (axes (z.1 • (step (0:Axis) : Track))) (axes (exileE z.2))) := by
  let L z : Corn (Album Axis) := Sum.elim ((z:ℝ× Gaia).1 • step (0:Axis)) (exileE z.2)
  have he : ContDiff ℝ ω L := by
    apply contDiff_pi.mpr; intro i; unfold L
    rcases i with i|i
    · simp only [Sum.elim_inl,Pi.smul_apply,smul_eq_mul]; fun_prop
    change ContDiff ℝ ω (fun z : ℝ× Gaia => z.2 i); fun_prop
  have hp : ContDiff ℝ ω ((starTrack f) ∘ axes) := contDiff_iff_contDiffAt.mpr fun x=> (hf.analytic_real x).contDiffAt
  exact hp.comp he
lemma keel_hold {Y : Award G} (b : G.ColorIndex) (hf : ∀ i j,Firm σ C (starTrack (Y i j))) : Continuous (fun x : Gaia=> keelRay Y b (exileE x)) := by
  let T : Fslot G:= (coord 1,b); let L := Y T T
  let f : ℝ× Gaia→ℂ := fun z=> L (axes (z.1 • step (0:Axis))) (axes (exileE z.2))
  have hp : ContDiff ℝ ω f := stroll_size (hf _ _)
  have hv x : keelRay Y b (exileE x)=(1/2:ℂ)*plunge (plunge f) (0,x) := by unfold keelRay strolls; rw [plunge_dive]; rfl
  simp_rw [hv]; exact continuous_const.mul ((plunge_green _ (plunge_green _ hp)).continuous.comp (continuous_const.prodMk continuous_id))
end YM.Stationary
end

/-!
# Log-transverse fine energy. Momentum integral authorized by same Vane.
Whole, not annulus.
 -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {G : Gauge} {F : Award G} {σ C : ℝ}

lemma polar_clock (h : ∀ i j,Firm σ C (starTrack (F i j))) (b : G.ColorIndex) : alphaPay b (profitable F)=cartWeight* ∫ x in boundsEarth,(keelRay F b (exileE x)).re := by
  let k : Fslot G := (coord 1,b); let A:=F k k; let L:= pressLens (profitable F) ![b,b] 1 1
  let p : Track := step (0:Axis); let Y t x := A (axes ((t:ℝ) • p)) (axes (exileE x))
  let P := fun t : ℝ => (∫ x in boundsEarth,Y t x)
  let K := fun t : ℝ => L (t • p)
  have ht (t) : K t=(2:ℂ)⁻¹ * (cartWeight:ℂ)*P t := by
    change (2:ℂ)⁻¹*stock (A (axes (t • p)))=_; have hu := h k k; rw [guildDraw (A (axes (t • p))) (stock_take A hu (p:=(axes _)) (Work.F07.realStrip σ hu.width_pos (axes_real (t • p)))),mul_assoc]
  have hy : ContDiff ℝ ω (Function.uncurry Y) := stroll_size (h k k)
  have hl := h k k
  have hs := hl.width_pos
  have he : AnalyticAt ℝ L 0 := priceL (profit F hs hl.budget_nonneg h).1 ![b,b] 1 1
  have hv := AnalyticAt.comp (x:=(0:ℝ)) (g:=L) (f:=fun t : ℝ=> t • p) (by rw [zero_smul]; exact he) (ContDiffAt.analyticAt (by fun_prop))
  let c := (2:ℂ)⁻¹*(cartWeight:ℂ)
  have hc : c≠0 := mul_ne_zero (by norm_num) (by exact_mod_cast cart_weight_pos.ne')
  have hP : AnalyticAt ℝ P 0 := by rw [show P=(fun t=> c⁻¹*K t) from funext (fun t=> by rw [ht]; change P t=c⁻¹*(c*P t); field_simp)]; exact analyticAt_const.mul hv
  have hQ := plunge_fare (Function.uncurry Y) hy
  have hx : (2:ℂ) * speedy L 2 p = (cartWeight:ℂ)*(∫ x in boundsEarth, keelRay F b (exileE x)) := by
    change _= (cartWeight:ℂ)*(∫ x in boundsEarth, (1/2:ℂ)*flareY 2 (fun t=> Y t x))
    unfold speedy Tensor.diagonal Tensor.coeff; rw [_root_.smul_apply,← sipRay (u:=2) (0:Track) p he]
    rw [show (fun t : ℝ=> L (0+t • p))=K from funext (fun _=> by rw [zero_add]), funext ht, show flareY 2 (fun t=> (2:ℂ)⁻¹ * (cartWeight:ℂ)*P t) =_ from flare_scale (n:=2) hP c, show flareY 2 P=∫ x in boundsEarth, flareY 2 (fun t=> Y t x) from hQ,integral_const_mul]; unfold c
    simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast]; norm_num [Nat.factorial]; ring
  unfold alphaPay leapTip; change 2 * (speedy L 2 p).re=_
  rw [show ∫ x in boundsEarth,(keelRay F b (exileE x)).re=_ from integral_re (astute _ (keel_hold b h))];
  have hc := congr_arg Complex.re hx; simpa [Complex.mul_re] using hc
end YM.Stationary
end

/-!
# Euclidean annulus of the kinetic determinant. Half-open radial shell
`µ < norm p ≤ 1` (Full denominator estimates allowed on it and on edges).
dimension = finrank, measure = Haar volume, before per-period cost normal.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal
variable {G : Gauge} {σ μ C : ℝ}

def orbShell (μ : ℝ) := {k : Gaia | ‖k‖∈Set.Ioc μ 1}
lemma shell_meas : MeasurableSet (orbShell μ) := measurableSet_Ioc.preimage continuous_norm.measurable
lemma shell_def : orbShell μ= closedBall (0:Gaia) 1 \ closedBall 0 μ := by ext; simp [orbShell]; tauto
lemma shell_on {x} (h : x∈orbShell μ) : x∈boundsEarth := orbs h.2
lemma solidGaia {μ : ℝ} (h : 0≤μ) : volume.real (closedBall (0:Gaia) μ)= μ^4*(Real.pi^2/2) := by
  unfold Measure.real; rw [InnerProductSpace.volume_closedBall_of_dim_even (k:=2) (by simp [Gaia])]; norm_num [h,Nat.factorial,ENNReal.toReal_ofReal, Real.pi_pos.le]; left; positivity

-- Polar law constant. `⊆ ` positions
lemma shell_turn (μ : ℝ) (h : 0<μ) (he : μ≤1) (f : ℝ→ℝ) : ∫ x : Gaia in orbShell μ,f ‖x‖= 2*Real.pi^2 * ∫ y : ℝ in μ..(1:ℝ), y^3*f y := by
  let I := Set.Ioc μ 1
  rw [← integral_indicator shell_meas]
  have hp (x : Gaia) : (orbShell μ).indicator (fun x=>f ‖x‖) x= I.indicator f ‖x‖ := by
    by_cases ht : ‖x‖∈I; · rw [Set.indicator_of_mem (show x∈orbShell μ from ht),Set.indicator_of_mem ht]
    rw [Set.indicator_of_notMem (show x∉orbShell μ from ht),Set.indicator_of_notMem ht]
  simp_rw [hp]; rw [MeasureTheory.integral_fun_norm_addHaar volume,intervalIntegral.integral_of_le he]
  rw [show Module.finrank ℝ Gaia=4 from finrank_euclideanSpace_fin]
  have ht : volume.real (ball (0:Gaia) 1)=Real.pi^2/2 := by rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball,solidGaia zero_le_one]; ring
  rw [ht]
  have hx : I⊆Set.Ioi (0:ℝ) := fun i hi=> h.trans hi.1
  have hv : (∫ y in Set.Ioi (0:ℝ), y^(4-1) • I.indicator f y) = ∫ y in I, y^3*f y := by
    let F y := (y:ℝ)^3*f y
    rw [show (fun y : ℝ=> y^(4-1) • I.indicator f y)=I.indicator F from ?_,setIntegral_indicator measurableSet_Ioc,Set.inter_eq_self_of_subset_right hx]
    funext y; by_cases hy : y∈I <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem,hy,F]
  rw [hv]
  simp [I]; ring

lemma polar_m (μ : ℝ) (h : 0<μ) (he : μ≤1) : (∫ x : Gaia in orbShell μ, (‖x‖^4)⁻¹)=2*Real.pi^2*Real.log μ⁻¹ := by
  rw [shell_turn μ h he (fun x=> (x^4)⁻¹)]; apply congr_arg _
  rw [← one_div, ← integral_inv_of_pos h (a:=μ) (b:= (1:ℝ)) zero_lt_one]; refine intervalIntegral.integral_congr ?_; rw [Set.uIcc_of_le he]; intro x hx; field_simp [(h.trans_le hx.1).ne']

lemma peel_p (μ : ℝ) (h : 0<μ) (he : μ≤1) :
    (∫ x : Gaia in orbShell μ,(‖x‖^3)⁻¹)=2*Real.pi^2*(1-μ) ∧
    (∫ x : Gaia in orbShell μ,(‖x‖^6)⁻¹)=2*Real.pi^2*((μ⁻¹^2-1)/2) := by
  have hu : (0:ℝ) ∉ Set.uIcc μ 1 := by simp only [Set.uIcc_of_le he]; exact fun hc=> h.not_ge hc.1
  have hk (x : ℝ) (he : x∈ Set.uIcc μ 1) : x≠0 := fun h'=>hu (h' ▸ he)
  constructor
  · rw [shell_turn μ h he (fun x=> (x^3)⁻¹), intervalIntegral.integral_congr (g:=fun _=>1)]; norm_num
    intro x he; field_simp [(hk x he)]
  rw [shell_turn μ h he (fun x=>(x^6)⁻¹)]; apply congr_arg _
  rw [intervalIntegral.integral_congr (g:=fun x:ℝ=>x^(-3:ℤ)),integral_zpow (n:=(-3:ℤ)) (Or.inr ⟨by norm_num,hu⟩)]; norm_num; field_simp [h.ne']; ring
  intro x he; field_simp [(hk x he)]

lemma geoS (h : 0<μ) (f : Gaia→ℝ) (hf : Continuous f) (n : ℕ) : IntegrableOn (fun x:Gaia => f x/‖x‖^n) (orbShell μ) volume := by
  let S := {x:Gaia| ‖x‖∈Set.Icc μ 1}
  have he : IsClosed S := isClosed_Icc.preimage continuous_norm
  have hv : S⊆closedBall 0 (1:ℝ) := fun i hi=> by simpa using hi.2
  have hk (x : Gaia) (hx : x∈S) : ‖x‖ ≠0 := (h.trans_le hx.1).ne'
  exact ((hf.continuousOn.div (continuous_norm.pow n|>.continuousOn) (fun x hx => pow_ne_zero _ (hk x hx))).integrableOn_compact ((isCompact_closedBall (0:Gaia) (1:ℝ)).of_isClosed_subset he hv)).mono_set (fun _ he => ⟨he.1.le,he.2⟩)
end YM.Stationary
end

/-!
# Orbital rotational moments. No sphere probability convention needed,
 use actual Euclidean volume. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal
variable {G : Gauge} {μ : ℝ}

def springAx (i : Axis) := EuclideanSpace.single i (1:ℝ)
lemma spring_unit (i) : ‖springAx i‖=1 := by unfold springAx; simp
lemma springTouch (i) (x : Gaia) : inner ℝ (springAx i) x=x i := by rw [springAx,EuclideanSpace.inner_single_left]; simp
lemma geode_sum (x : Gaia) : ∑ i : Axis,(x i)^2=‖x‖^2 := by
  have ht := orbit_sqr (exileE x); exact ht.symm
lemma alpine (S : Gaia≃ₗᵢ[ℝ] Gaia) (q : Gaia→ℝ) : ∫ x in orbShell μ,q (S x)=∫ x in orbShell μ,q x := by
  let T : Gaia≃ᵐ Gaia:= S.toHomeomorph.toMeasurableEquiv
  have ht : Measure.map T volume = volume := S.measurePreserving.map_eq
  let U := orbShell μ
  have hv : T ⁻¹' U = U := by ext x; change ‖S x‖∈Set.Ioc μ 1 ↔ _; rw [LinearIsometryEquiv.norm_map]; rfl
  exact Eq.symm (by

    have hx : (∫ x in U,q x ∂Measure.map T volume)=(∫ x in U,q (T x)) := by rw [setIntegral_map_equiv,hv]
    rw [ht] at hx; exact hx)
section ann

def opJen (u x : Gaia) (n : ℕ) := (inner ℝ u x)^n /‖x‖^(4+n)
def joyAx (μ : ℝ) (u : Gaia) (n : ℕ) := ∫ x in orbShell μ, opJen u x n
lemma joy_rotate {u v : Gaia} (h : ‖(u:Gaia)‖= ‖(v:Gaia)‖) (n) : joyAx μ u n=joyAx μ v n := by
  let V : Gaia≃ₗᵢ[ℝ] Gaia := Submodule.reflection (Submodule.span ℝ {u-v})ᗮ
  have ht : V u=v := Submodule.reflection_sub h
  unfold joyAx
  refine Eq.trans ?_ (alpine V (fun x=>opJen v x n)); apply setIntegral_congr_fun shell_meas; intro x hx; unfold opJen; simp [← ht]


lemma joy_rate (u : Gaia) (a : ℝ) (n : ℕ) : joyAx μ (a • u) n=a^n * joyAx μ u n := by unfold joyAx opJen; simp_rw [real_inner_smul_left,mul_pow,mul_div_assoc,integral_const_mul]
lemma switchG (u : Gaia) (b : Axis) (n) : joyAx μ u n= ‖u‖^n*joyAx μ (springAx b) n := by rw [← joy_rate]; exact joy_rotate (by rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _),spring_unit,mul_one]) _

def snowY (p : Gaia) := (‖p‖^4)⁻¹
def landX (m : ℝ) := ∫ p in orbShell m,snowY p
def jetMix (p : Gaia) (i j : Axis) := (p i)^2*(p j)^2/‖p‖^8
def joyMix (m : ℝ) (i j : Axis) := ∫ p in orbShell m, jetMix p i j
variable (h : 0<μ)
include h
lemma joy_paid (p : Gaia) (n) : IntegrableOn (fun x=>opJen p x n) (orbShell μ) volume := geoS h (fun x=> (inner ℝ p x)^n) (by fun_prop) _
lemma joy_meal (i j : Axis) : IntegrableOn (fun x=> jetMix x i j) (orbShell μ) volume := geoS h _ (show Continuous fun x : Gaia=> (x i)^2*(x j)^2 from by fun_prop) 8
lemma joy_two (i : Axis) : joyAx μ (springAx i) 2=landX μ/4 := by
  have hp : (∑ j:Axis,joyAx μ (springAx j) 2)=landX μ := by
    unfold joyAx landX; rw [← integral_finsetSum]; swap; · intro a _; exact joy_paid h _ _
    apply setIntegral_congr_fun shell_meas; intro a ha; unfold opJen snowY
    simp_rw [springTouch,← sum_div,geode_sum a]; have hv : 0<‖a‖ := h.trans ha.1; field_simp
  simp_rw [show ∀ a,joyAx μ (springAx a) 2= joyAx μ (springAx i) 2 from fun a=>joy_rotate ((spring_unit a).trans (spring_unit i).symm) 2] at hp; simp at hp; linarith
lemma prismAx (i j : Axis) (hp : i≠j) : ‖springAx i+springAx j‖^4=4 ∧ ‖springAx i-springAx j‖^4=4 := by
  have hx : ⟪springAx i,springAx j⟫_ℝ=0 := by rw [springTouch]; simp [springAx,hp]
  constructor
  · rw [show ‖_+_‖^4=(‖springAx i+springAx j‖^2)^2 by ring,norm_add_sq_real,spring_unit,spring_unit,hx]; norm_num
  rw [show ‖_-_‖^4=(‖springAx i-springAx j‖^2)^2 by ring,norm_sub_sq_real,spring_unit,spring_unit,hx]; norm_num
-- average j in each row to get mixed formula. braces corners.
lemma joy_knot (i j : Axis) (ht : i≠j) : joyAx μ (springAx i) 4 = 3*joyMix μ i j := by
  let M := joyAx μ (springAx i) 4
  let P:=springAx i+springAx j; let Q:=springAx i-springAx j
  have hh : joyAx μ P 4 + joyAx μ Q 4=2*M + 2* joyAx μ (springAx j) 4+12*joyMix μ i j := by
    unfold M joyAx joyMix
    rw [← integral_add (joy_paid h _ 4) (joy_paid h _ 4)]; simp_rw [← integral_const_mul]; rw [← integral_add (f:=fun v=>2*opJen (springAx i) v 4) (g:=fun v=>2*opJen (springAx j) v 4) ((joy_paid h _ 4).const_mul 2) ((joy_paid h _ 4).const_mul 2), ← integral_add ?_ ((joy_meal h i j).const_mul 12)]
    · apply setIntegral_congr_fun shell_meas; intro x hx; unfold opJen jetMix P Q; simp only [inner_add_left,inner_sub_left,springTouch]; ring
    exact Integrable.add ((joy_paid h _ 4).const_mul 2) ((joy_paid h _ 4).const_mul 2)
  rw [switchG (μ:=μ) P i 4,switchG (μ:=μ) Q i 4,show ‖P‖^4=_ from (prismAx (μ:=μ) h i j ht).1,show ‖Q‖^4=_ from (prismAx (μ:=μ) h i j ht).2, joy_rotate (show ‖springAx j‖=‖springAx i‖ by rw [spring_unit,spring_unit]) 4] at hh
  unfold M at hh; linarith
lemma joy_heights (i j : Axis) (ht : i ≠ j) : joyMix μ i j = landX μ/24 := by
  let f i' := joyMix μ i i'; let A:= f i; let B:= f j
  have hp : (∑ i : Axis, f i)= joyAx μ (springAx i) 2 := by
    unfold joyAx f joyMix; rw [← integral_finsetSum]; swap; · exact fun k _ => joy_meal h i k
    apply setIntegral_congr_fun shell_meas; intro k hk; unfold opJen jetMix; simp_rw [springTouch,← sum_div,← mul_sum,geode_sum]; field_simp [((h.trans hk.1).ne')]
  have ha : A=joyAx μ (springAx i) 4 := by
    unfold A f joyMix joyAx; apply setIntegral_congr_fun shell_meas; intro x hx; unfold jetMix opJen; simp only [springTouch]; ring
  have he (a) (h' : a ≠ i) : f a=B := by
    have hx := joy_knot h i a h'.symm; have hq := joy_knot h i j ht; unfold f B; linarith
  rw [show ∑ i,f i = A + 3*B from ?_,joy_two h i] at hp
  swap
  · rw [← sum_erase_add _ _ (mem_univ i)]; simp_rw [sum_congr rfl (s₁:=_) (f:=f) (g:=fun _ => B) (fun k hk=> he k (ne_of_mem_erase hk))]; simp [Finset.card_erase_of_mem,A, Fintype.card_fin]; ring
  rw [ha,joy_knot h i j ht] at hp; unfold B f at hp; linarith
end ann
end YM.Stationary
end

/-!
# Lattice slope quantitative. Combining barriers not alter `μ`; error
estimates taken absolutely before any constrained radial pseudoscale.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal
variable {G : Gauge} {σ η μ C D : ℝ} {F : Award G}

-- continuum log at that μ. shape Greek.
lemma poleBudget (h : 0<μ) : IntegrableOn (poleVec G ∘ exileE) (orbShell μ) volume := by
  let V := fun x : Gaia=> ((exileE x) 1)^2; let U := fun x : Gaia=> 4*(x 1)^2*(x 0)^2
  have hL := geoS h V (show Continuous (fun x : Gaia=> (x 1)^2) by fun_prop) 6
  have hX := geoS h U (by unfold U; fun_prop) 8
  have ht : IntegrableOn (fun x:Gaia=> (‖x‖^4)⁻¹) (orbShell μ) volume := by simpa using geoS h (fun _=>1) continuous_const 4
  exact ((hL.sub hX).sub ht).const_mul _
lemma poleSpin (h : 0<μ) (he : μ≤1) : cartWeight*(∫ x in orbShell μ,poleVec G (exileE x))= -G.slopeConstant*Real.log μ⁻¹ := by
  let f := fun x : Gaia=> opJen (springAx 1) x 2
  let r := fun x : Gaia=> jetMix x 1 0
  have hr (x : Gaia) : poleVec G (exileE x)=4*G.casimir*(f x-4*r x-snowY x) := by
    change 4*_*((x 1)^2 / ‖x‖^6-4*(x 1)^2*(x 0)^2/‖x‖^8 - (‖x‖^4)⁻¹)=_; unfold f opJen; rw [springTouch]; unfold r jetMix snowY; ring
  simp_rw [hr]
  have hy : IntegrableOn snowY (orbShell μ) volume := by
    change IntegrableOn (fun x:Gaia=> (‖x‖^4)⁻¹) _ _; simpa using geoS h (fun _=>1) continuous_const 4
  rw [integral_const_mul,integral_sub (f:=fun x=>f x-4*r x) ((joy_paid h (springAx 1) 2).sub ((joy_meal h 1 0).const_mul 4)) hy,
    integral_sub (f:=f) (joy_paid h _ _) ((joy_meal h 1 0).const_mul 4), integral_const_mul]
  change cartWeight*(_*(joyAx μ (springAx 1) 2- _*joyMix μ 1 0- landX μ))=_
  rw [joy_two h 1,joy_heights h _ _ (by decide : (1:Axis) ≠0),show landX μ=_ from polar_m μ h he]
  unfold Gauge.slopeConstant cartWeight; field_simp; ring

section real
variable (b : G.ColorIndex) (h : ∀ i j,Firm σ C (starTrack (F i j)))
-- Outer(in Cube). Cost VolCube even including edge 0 if unit?

def costZone (A D : ℝ) := A*(Real.pi^2/2)+A*volume.real boundsEarth + D*(2*Real.pi^2+Real.pi^2)
include h
lemma absoluteGeode {A : ℝ} (hA : 0≤A) (hD : 0≤D) (hμ : 0<μ) (hp : μ≤1) (hv : Waves1 A μ (keelRay F b)) (hk : Waves2 D μ (keelRay F b) G) :
    |alphaPay b (profitable F)+ G.slopeConstant*Real.log μ⁻¹| ≤ cartWeight*costZone A D := by
  let B : Set Gaia := closedBall 0 1
  let L : Set Gaia := closedBall 0 μ
  let I := orbShell μ; let Q:=boundsEarth \ B
  let g x := (keelRay F b (exileE x)).re; let H:=fun x : Gaia=>poleVec G (exileE x)
  have hy : B⊆boundsEarth := fun _ hp=> orbs (by simpa [B] using hp)
  have hl : L⊆B := closedBall_subset_closedBall hp
  have hu : boundsEarth= (L∪I) ∪ Q := by rw [show I=B\L from shell_def,Set.union_sdiff_cancel hl]; exact (Set.union_sdiff_cancel hy).symm
  have hs : MeasurableSet L := measurableSet_closedBall; have hI : MeasurableSet I := shell_meas
  have hQ : MeasurableSet Q := earth_meas.diff measurableSet_closedBall
  have ht := astute (fun x : Gaia => keelRay F b (exileE x)) (keel_hold b h)
  have hg : IntegrableOn g boundsEarth volume := ht.re
  have hd : IntegrableOn g I volume := hg.mono_set (fun _ hv=> shell_on hv)
  have hE (x : Gaia) (hx : x∈boundsEarth) : ‖g x‖≤ A/(‖x‖+μ)^4 := by
    rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hv _ (cradleFront _ hx))
  have hB1 : ‖∫ x in L,g x‖≤A*(Real.pi^2/2) := by
    have hx x (he : x∈L) : ‖g x‖≤ A/μ^4 := by
      exact (hE x (hl.trans hy he)).trans (div_le_div_of_nonneg_left hA (pow_pos hμ 4) (pow_le_pow_left₀ hμ.le (le_add_of_nonneg_left (norm_nonneg _)) 4))
    refine (norm_setIntegral_le_of_norm_le_const ?_ hx).trans_eq ?_
    · exact (isCompact_closedBall ..).measure_lt_top
    unfold L; rw [solidGaia hμ.le]; field_simp
  have hB2 : ‖∫ x in Q,g x‖ ≤ A*volume.real boundsEarth := by
    have hx x (he : x∈Q) : ‖g x‖≤ A := by
      have hh : 1≤‖x‖ := le_of_lt (lt_of_not_ge (fun h=> he.2 (by simpa [B] using h)))
      exact (hE x he.1).trans (div_le_self hA (one_le_pow₀ (by linarith)))
    have hh : Q ⊆ boundsEarth := fun _ ht=> ht.1
    exact (norm_setIntegral_le_of_norm_le_const ((measure_mono hh).trans_lt (lt_top_iff_ne_top.2 earth_oaks)) hx).trans (mul_le_mul_of_nonneg_left (measureReal_mono hh earth_oaks) hA)
  have ht' : ‖∫ x in I,(g x-H x)‖≤ D*(2*Real.pi^2+Real.pi^2) := by
    let M x := D*(‖(x:Gaia)‖^3)⁻¹
    let P x := D*μ^2*(‖(x:Gaia)‖^6)⁻¹
    have hm v (hv : v∈I) : ‖g v-H v‖ ≤ M v+P v := by
      rw [Real.norm_eq_abs,show g v-H v=_ from (Complex.sub_re (keelRay F b (exileE v)) (H v:ℂ)).symm]
      exact (Complex.abs_re_le_norm _).trans ((hk _ (cradleFront _ (shell_on hv)) hv.1.le).trans_eq (by rw [div_eq_mul_inv,div_eq_mul_inv]; rfl))
    have hx (n : ℕ) : IntegrableOn (fun x:Gaia=> (‖x‖^n)⁻¹) I volume := by simpa using geoS hμ (fun _=>1) continuous_const n
    have hM : IntegrableOn M I volume := (hx 3).const_mul _; have hP : IntegrableOn P I volume := (hx 6).const_mul _
    refine (norm_integral_le_of_norm_le (μ:=volume.restrict I) (g:=fun x=> M x+P x) (hM.add hP) ?_).trans ?_
    · exact (ae_restrict_mem hI).mono fun i hi => hm i hi
    rw [integral_add hM hP]; unfold M P I
    rw [integral_const_mul,integral_const_mul,(peel_p μ hμ hp).1,(peel_p μ hμ hp).2]
    rw [mul_add]; apply add_le_add
    · refine mul_le_mul_of_nonneg_left ?_ hD; exact mul_le_of_le_one_right (by positivity) (by linarith)
    calc
     _ = D*Real.pi^2*(1-μ^2) := by field_simp
     _ ≤ _ := mul_le_of_le_one_right (by positivity) (by nlinarith)
  have he : (∫ x in boundsEarth,g x) = ((∫ x in L,g x)+(∫ x in I,g x))+(∫ x in Q,g x) := by
    have hy' : L∪I=B := by rw [show I=B\L from shell_def,Set.union_sdiff_cancel hl]
    conv_lhs => rw [hu]
    rw [setIntegral_union (s:=L∪I) (t:=Q) ?_ hQ ?_ ?_,setIntegral_union (s:=L) ?_ hI (hg.mono_set (hl.trans hy)) hd]
    · rw [show I=B\L from shell_def]; exact Set.disjoint_sdiff_right
    · rw [hy']; exact Set.disjoint_sdiff_right
    · rw [hy']; exact hg.mono_set hy
    exact hg.mono_set (fun _ (hh:_∈Q)=> hh.1)
  have hH := poleSpin (G:=G) hμ hp
  rw [polar_clock h b]
  rw [neg_mul] at hH
  change |cartWeight*(∫ x in boundsEarth,g x)+_|≤_
  rw [he, ← show -(cartWeight*(∫ v in I,H v))=G.slopeConstant*Real.log μ⁻¹ from neg_eq_iff_eq_neg.mpr hH];
  rw [← mul_neg,← mul_add, abs_mul, abs_of_pos cart_weight_pos]
  refine mul_le_mul_of_nonneg_left ?_ cart_weight_pos.le
  have h' : (∫ x in I,g x-H x)=(∫ x in I,g x)-(∫ x in I,H x) := integral_sub hd (poleBudget (G:=G) hμ)
  rw [show _ + -(∫ x in I,H x)= (∫ x in L,g x)+(∫ x in Q,g x)+(∫ x in I,g x-H x) by rw [h']; abel, ← Real.norm_eq_abs]
  exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add hB1 hB2)) ht')
end real
end YM.Stationary
end
