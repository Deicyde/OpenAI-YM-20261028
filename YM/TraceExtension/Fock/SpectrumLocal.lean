import YM.TraceExtension.Fock.Paley
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Fourier uniqueness on shell waves given just tests on an open neighborhood
(around each probe after additional smearing). -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
section
open Paley
variable {V : Type*} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
variable {μ : Measure V} {f : V → ℂ} (u : V → ℝ) (hu : Continuous u)
def lineBeam (μ : Measure V) (v : V → ℝ) (f : V → ℂ) (z : ℂ) := Paley.cell μ v f z

include hu
lemma air_integrable (h : ∀ i,0≤u i) (hp : Integrable f μ) : Air (lineBeam μ u f) (∫ i, ‖f i‖ ∂μ) := by
    have he (z : ℂ) (hz : z∈ high) : ∀ᵐ i∂μ, ‖Paley.weight u f z i‖ ≤ ‖f i‖ := by
        filter_upwards with i; unfold Paley.weight; rw [norm_mul,Complex.norm_exp]
        apply mul_le_of_le_one_right (norm_nonneg _); simp [mul_nonneg (h i) (show 0≤z.im from hz)]
    have hi (z : ℂ) : AEStronglyMeasurable (Paley.weight u f z) μ := hp.1.mul (show Continuous (fun i => Complex.exp (↑(u i)*z*I)) by fun_prop).aestronglyMeasurable
    have hk (z) (hz:z∈high) : Integrable (Paley.weight u f z) μ := hp.norm.mono' (hi _) (he _ hz)
    constructor
    · exact continuousOn_of_dominated (F:=Paley.weight u f) (fun i _=>hi i) he hp.norm (ae_of_all _ fun i=> (by unfold Paley.weight; fun_prop))
    · intro z hz
      let g p i := (u i:ℂ)*I * Paley.weight u f p i
      let y := z.im/2; have hy : 0<y := half_pos (show 0<z.im from hz)
      have hf i p : HasDerivAt (fun z => Paley.weight u f z i) (g p i) p := by
        convert ((((hasDerivAt_id' p).const_mul ((u i):ℂ)).mul_const I).cexp.const_mul (f i)) using 1 <;> try rfl
        dsimp only [g,Paley.weight]; ring
      have hw := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=Paley.weight u f) (F':=g) (μ:=μ)
        (show {p:ℂ| y<p.im}∈𝓝 z from (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by change y<z.im; unfold y at *; linarith)) (Eventually.of_forall hi) (hk _ (Paley.subset hz))
        ((show Continuous fun i => (u i:ℂ)*I from by fun_prop).aestronglyMeasurable.mul (hi z)) (bound:=fun i => y⁻¹*‖f i‖)
      refine (hw ?_ (hp.norm.const_mul _) (ae_of_all _ fun i p _ => hf i p)).2.differentiableAt.differentiableWithinAt
      filter_upwards with i p hh
      unfold g Paley.weight; simp only [norm_mul,norm_I, norm_real,Real.norm_of_nonneg (h i),mul_one,Complex.norm_exp]
      rw [show (↑(u i)*p*I).re= -(u i * p.im) by simp, mul_comm ‖f i‖,← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have ha := Real.add_one_le_exp (u i*p.im)
      rw [Real.exp_neg, inv_eq_one_div y, le_div_iff₀ hy, mul_right_comm,← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
      nlinarith [show y<p.im from hh, h i]
    intro z hz; exact norm_integral_le_of_norm_le hp.norm (he z hz)
end

lemma integral_null {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [SigmaFinite μ] {f : V → ℂ} (hf : Integrable f μ)
    (ht : ∀ p, (∫ x, Probe.plane p x*f x ∂μ)=0) : f=ᵐ[μ] 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable (fun g hc hg=>?_)
    let u : Probe V := (hg.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hc)
    have hp y : (∫ x, Probe.plane x y * Probe.hat u x) * f y=(Probe.pref V)* (g y • f y) := by rw [Probe.positiveFourier]; change (Probe.pref V • (↑(g y):ℂ)) * _ = _; simp [Complex.real_smul,mul_assoc]
    apply mul_left_cancel₀ (show (↑(Probe.pref V):ℂ)≠0 from by exact_mod_cast Probe.prepos.ne')
    rw [← integral_const_mul];
    simp_rw [← hp, ← integral_mul_const]; rw [integral_integral_swap]
    · have he x : (∫ y, Probe.plane x y*Probe.hat u x*f y ∂μ)=0 := by simp_rw [mul_comm (Probe.plane _ _),mul_assoc]; rw [integral_const_mul, ht x, mul_zero]
      simp_rw [he]; simp
    let K := fun a : V×V => Probe.plane a.2 a.1*Probe.hat u a.2*f a.1
    apply (hf.norm.mul_prod (Probe.hat u).integrable.norm).mono'
    · exact (show AEStronglyMeasurable K _ from ((Probe.plane_cont.comp continuous_swap |>.mul
         ((Probe.hat u).continuous.comp continuous_snd)).aestronglyMeasurable.mul hf.1.comp_fst))
    filter_upwards with a; change ‖K a‖ ≤ _; simp [K,mul_comm]

variable {n : ℕ}
def beam (b : Fin n → E4) (p : Mom n) := ∏ i, Probe.plane (momentum (p i)) (b i)
def rapid (f : Mom n→ℂ) (p : Fin n → E4) := ∫ k,f k*beam p k ∂photons n
lemma beam_norm (b : Fin n→E4) p : ‖beam b p‖=1 := by simp [beam,norm_prod]
def sweep (p : Fin n → E4) := ∀ i,p i ∈ inside
lemma sweep_open : IsOpen {p : Fin n → E4| sweep p} := by
    rw [show {p : Fin n → E4| sweep p}= ⋂ i : Fin n, (fun p=>p i) ⁻¹' inside by ext; simp [sweep]]; exact isOpen_iInter_of_finite fun i=> open_inside.preimage (continuous_apply i)
lemma spans {f : Mom n → ℂ} (hf : Integrable f (photons n)) (he : rapid f =ᶠ[𝓝 0] 0) (x : Fin n → E4) : rapid f x=0 := by
    have hh a v (ha : rapid f =ᶠ[𝓝 a] 0) (hv : sweep v) (r : ℝ) : rapid f (a+r • v)=0 := by
        let u (p : Mom n) := ∑ i, inner ℝ (v i) (momentum (p i)); let g p := f p * beam a p
        have hu : Continuous u := by unfold u; fun_prop
        have hi (p) : 0 ≤ u p := Finset.sum_nonneg fun i _=> Mink.self_pair ((show ‖spatial _‖<time (v i) from hv i).le) (by simp [Mink.cone])
        have hg : Integrable g (photons n) := by
           rw [show g=(fun p=>beam a p*f p) by funext p; unfold g; ring]
           exact hf.bdd_mul (show Continuous (beam a) from by unfold beam Probe.plane; fun_prop).aestronglyMeasurable
             (ae_of_all _ fun z => (beam_norm a z).le)
        have ht := air_integrable u hu hi hg
        have hp (t : ℝ) : rapid f (a+t • v)=lineBeam (photons n) u g t := by
            unfold rapid lineBeam Paley.cell; apply integral_congr_ae; filter_upwards with p
            unfold beam g Paley.weight u beam
            simp only [Pi.add_apply, Pi.smul_apply, Probe.plane,inner_add_right,real_inner_smul_right, ofReal_add,ofReal_mul, add_mul,Complex.exp_add,Finset.prod_mul_distrib, Complex.ofReal_sum, Finset.sum_mul, mul_assoc]
            congr 2; rw [Complex.exp_sum]; apply Finset.prod_congr rfl; intro i _; rw [real_inner_comm]; ring_nf
        rw [hp]; apply bottom_identity ht
        have hm : Continuous fun t:ℝ => a+t • v := continuous_const.add (continuous_id.smul continuous_const)
        have hw := hm.tendsto 0; rw [zero_smul,add_zero] at hw
        filter_upwards [hw.eventually ha] with t ht; rw [← hp]; exact ht
    have ht (v) (hv : sweep v) : rapid f v=0 := by simpa using hh 0 v he hv 1
    let w : Fin n → E4 := fun _ => basis timeAxis
    have hw : sweep w := fun i=> clock_inside
    have hy : Continuous fun t:ℝ => w - t • x := continuous_const.sub (continuous_id.smul continuous_const)
    have he := hy.tendsto 0; rw [zero_smul,sub_zero] at he
    obtain ⟨i,hi,hj⟩ := (((he.eventually (sweep_open.mem_nhds (x:=w) hw)).filter_mono (nhdsWithin_le_nhds (s:=Ioi 0))).and self_mem_nhdsWithin).exists
    have hi : sweep (w-i • x) := hi
    have hp : 0 < i := hj
    have hR (z : Fin n → E4) (hz : sweep z) : sweep (i⁻¹ • z) := by
        intro j; change ‖spatial (i⁻¹ • z j)‖ < time (i⁻¹ • z j); rw [rest_mul,norm_smul,Real.norm_of_nonneg (by positivity),Mink.clock_mul]; exact mul_lt_mul_of_pos_left (hz j) (by positivity)
    have hh := hh (i⁻¹ • w) (i⁻¹ • (w-i • x)) ((show ∀ᶠ j in 𝓝 (i⁻¹ • w), sweep j from sweep_open.mem_nhds (x:=i⁻¹ • w) (hR _ hw)).mono fun z hz=> ht _ hz) (hR _ hi) (-1)
    simpa [smul_sub,smul_smul,hp.ne'] using hh

lemma shell_unique (f : Mom n→ℂ) (hf : Integrable f (photons n)) (ht : rapid f=ᶠ[𝓝 0] 0) : f=ᵐ[photons n] 0 := by
    let V := PiLp 2 fun _ : Fin n => Space3
    let e : Mom n ≃ₗ[ℝ] V := (WithLp.linearEquiv 2 ℝ (Mom n)).symm
    let F := LinearEquiv.toContinuousLinearEquiv e
    let g := f ∘ F.symm
    let μ := (photons n).map F
    have he : MeasurableEmbedding F := F.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    haveI : SigmaFinite μ :=
       he.sigmaFinite_map
    have hp p : g (F p)=f p := by simp [g]
    have hh : Integrable g μ := he.integrable_map_iff.2 (hf.congr (ae_of_all _ fun x=> (hp x).symm))
    have hx (p : V) : (∫ x, Probe.plane p x*g x ∂μ)=0 := by
        let y := F.symm p
        let z : Fin n→ E4 := fun i=> position (y i) 0
        rw [show μ=(photons n).map F from rfl,he.integral_map,← spans hf ht z]; unfold rapid; apply integral_congr_ae; filter_upwards with x
        have hq : inner ℝ p (F x)=∑ i,inner ℝ (y i) (x i) := by rw [show p= F y by unfold y; simp]; rfl
        rw [hp]; unfold Probe.plane beam Probe.plane; rw [hq];
        simp [Mink.pairing,z,Finset.mul_sum,Complex.exp_sum, real_inner_comm,mul_comm]
    exact ((he.ae_map_iff).1 (integral_null hh hx)).mono fun i hi=> by change _ = (0:ℂ); rw [← hp]; exact hi
end YM.TraceExtension.Photons
