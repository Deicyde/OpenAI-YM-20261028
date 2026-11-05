import YM.TraceExtension.Wick.PolynomialField
import YM.TraceExtension.Wick.Log

/-! Exclusion against arbitrary finite polynomial field descriptions in the
sense of the mass-shell kernels. Even an infinite-component direct sum of
systems *with finite local polynomial image of the trace* and these necessary
tested two-point identities cannot work. No claim against a continuous-mass
generalized free field. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Wick
open Function Set Filter Asymptotics Metric Complex Mink Boundary MeasureTheory Measure
open scoped Topology BigOperators NNReal Classical ContDiff

abbrev Collection := List (ℂ × Track)
def atPoint (x : Collection) (t : ℝ) := (x.map fun z=> z.1 * (z.2.euclidean t:ℂ)).sum
def tests (x : Collection) (t : E4→ℂ) := (x.map fun z=> z.1*z.2.read t).sum
lemma real_profile (x : Collection) : Expands (fun p=>(atPoint x p).re) := by
    induction x with
    | nil => simp only [atPoint,List.map_nil,List.sum_nil,zero_re]; exact own board.zero_mem
    | cons y l ih =>
        simp only [atPoint,List.map_cons,List.sum_cons, add_re,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]; exact Expands.plus (Expands.scale y.2.moments_expand y.1.re) ih

lemma approximate (s : ℝ) : ∃ w : ℕ→Probe E4, (∀ n,HasCompactSupport ⇑(w n) ∧ ∀ x : E4, ‖w n x‖ ≤ Real.exp (-s*time x)) ∧
    ∀ p,Tendsto (fun n=> w n p) atTop (𝓝 (↑(Real.exp (-s*time p)):ℂ)) := by
    let h n := (Probe.keeper (X:=E4) n)
    let g n p := h n p*(↑(Real.exp (-s*time p)):ℂ)
    have hk n : HasCompactSupport (g n) := by
        have he : HasCompactSupport ⇑(h n) := by
            apply HasCompactSupport.comp_homeomorph (φ := (Probe.compress n).toHomeomorph) (f:=⇑(Probe.tint (Probe.stall (X:=E4))))
            simp only [HasCompactSupport,Probe.tint_support]; apply isCompact_closedBall
        exact he.mul_right
    have hd : ContDiff ℝ ∞ time := Mink.clockL.contDiff
    let W n : Probe E4 := (hk n).toSchwartzMap (((h n).smooth _).mul (ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul hd))))
    refine ⟨W,fun n=> ⟨hk n,fun x=> ?_⟩,fun p=>tendsto_const_nhds.congr' ?_⟩
    · change ‖g _ _‖ ≤ _; unfold g; rw [norm_mul,norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
      apply mul_le_of_le_one_left (Real.exp_nonneg _); unfold h Probe.keeper; rw [Probe.along_at,Probe.tinted,norm_real,Real.norm_of_nonneg Probe.stall.nonneg]; exact Probe.stall.le_one
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖p‖] with n hn; change _=g n p; unfold g h; rw [Probe.keeper_one (x:=p) n (le_trans hn (le_add_of_nonneg_right zero_le_one)),one_mul]

lemma reads (t : Collection) (s : ℝ) (hs : 0<s) (w : ℕ → Probe E4) (h : ∀ n p,‖w n p‖ ≤ Real.exp (-s*time p)) (hw : ∀ p, Tendsto (fun n=> w n p) atTop (𝓝 (↑(Real.exp (-s*time p)):ℂ))) :
    Tendsto (fun n=> tests t (w n)) atTop (𝓝 (atPoint t s)) := by
    have hp (W : Track) : Tendsto (fun n=> W.read (w n)) atTop (𝓝 (↑(W.euclidean s):ℂ)) := by
        rw [← W.damp_reads]; unfold Track.read
        apply tendsto_integral_of_dominated_convergence (bound:=fun p:W.Config => ‖W.weight p*Real.exp (-s*time (W.order p))‖)
        · intro n; apply Measurable.aestronglyMeasurable
          apply Measurable.smul (f:=W.weight) _ ((w n).continuous.comp W.order_cont).measurable
          unfold Track.weight; apply Finset.measurable_prod; intro i _; unfold Mode.density freq; have hf := (W.modes i).cont; fun_prop
        · exact (W.damped_int _ hs).norm
        · exact fun n => ae_of_all _ fun p=> by
             unfold Track.tariff; rw [norm_smul,norm_mul,Real.norm_of_nonneg (Real.exp_nonneg _)]; exact mul_le_mul_of_nonneg_left (h ..) (norm_nonneg _)
        exact ae_of_all _ fun p=> Tendsto.const_smul (hw (W.order p)) (W.weight p)
    induction t with
    | nil=> exact tendsto_const_nhds
    | cons t v ih=> exact (Tendsto.const_mul t.1 (hp t.2)).add ih

variable {G : Gauge} {C : Family G} {a : Extraction.Order} {S : Table C.book}
    {F : Spec.Final C a S} {μ : Measure E4} {A : ℝ}
lemma heat_value (x : ℝ) (hx : 0<x) (hs : TraceSpectrum F μ) :
    euclidean F x= ∫ p, (↑(Real.exp (-x*time p)):ℂ) ∂μ := by
    have h : x • basis timeAxis ∈ inside := by simp [inside,hx]
    rw [hs.laplace x hx,← time_lag,lag_eval μ (allows_trace hs) (u:=⟨_,h⟩), integral_complex_ofReal]; simp only [real_inner_smul_left, basis_inner,neg_mul]; rfl
lemma identifies_euclid (hs : TraceSpectrum F μ) (t : Collection) (h : ∀ f : Probe E4, HasCompactSupport ⇑f→(∫ p,f p ∂μ)=tests t f)
    (s : ℝ) (hS : 0<s) : euclidean F s=atPoint t s := by
    obtain ⟨w,hx,hW⟩ := approximate s
    haveI ht := hs.damped_mass _ hS
    have hh : Integrable (fun p => Real.exp (-s*time p)) μ := by
        have hp : Integrable (fun _ : E4 => (1:ℝ)) (OS.Semigroup.transform timeAxis s μ) := integrable_const _
        have he := (integrable_withDensity_iff_integrable_smul (OS.Semigroup.measurable ..)).1 hp
        apply Integrable.congr he; exact ae_of_all _ fun p=> (by change Real.exp _ * 1=_; rw [mul_one]; rfl)
    rw [heat_value s hS hs]
    refine tendsto_nhds_unique_of_eventuallyEq (f:=fun n => ∫ p,w n p ∂μ) ?_ (reads t s hS w (fun i => (hx i).2) hW)
        (Eventually.of_forall fun n=>h _ (hx n).1)
    exact tendsto_integral_of_dominated_convergence _ (fun i => (w i).continuous.aestronglyMeasurable) hh (fun i=> ae_of_all _ (hx i).2) (ae_of_all _ hW)

lemma euclidean_excludes (ht : EuclideanAsymptotic F A) (hA : 0<A) (t : Collection) :
    ¬ euclidean F =ᶠ[past] atPoint t := by
    intro h; apply hA.ne'
    apply no_powerlog (real_profile t 0)
    have he : Tendsto _ _ (𝓝 (A:ℂ).re) := (Complex.continuous_re.tendsto _).comp ht
    apply he.congr'; filter_upwards [h] with i hi; rw [comp_apply]; rw [hi,Complex.real_smul, mul_re,ofReal_re,ofReal_im]; ring

/-- No polynomial-field vacuum correlations. It suffices to hypothesize
the mass-shell reads (the ordinary contractions with no same-vertex pairing)
on momentum tests that are Fourier transforms of tensor product position
smearings. Even just those seeing compact total momenta suffice. -/
theorem polynomial_excludes (ht : EuclideanAsymptotic F A) (hA : 0<A) (W : Collection) :
    ¬ ∀ f g : Probe E4, HasCompactSupport ⇑(waveTest (productTest f g)) →
       F.A.world.W 2 (pairV F.action.J (pinned F)) (productTest f g)=tests W (waveTest (productTest f g)) := by
    intro h
    obtain ⟨μ,hμ,hM⟩:=traceSpectrum_exists F
    apply euclidean_excludes ht hA W
    apply mostly.mono; intro x hx; apply identifies_euclid hμ W _ _ hx.1
    intro v hv
    obtain ⟨p,hp⟩ := hv.isBounded.subset_closedBall (0:E4)
    obtain ⟨u,hu⟩:= probe_one (Nat.ceil p)
    obtain ⟨w,hw⟩:= testPlus_onto (Probe.sew (testPlus u) v)
    have he : waveTest (productTest u w)=v := by
        ext1 x
        rw [waveTest_product,hw,Probe.sews,← mul_assoc]
        by_cases hx : v x=0
        · rw [hx,mul_zero]
        have ht := hu x ((closedBall_subset_closedBall (Nat.le_ceil p)) (hp (subset_tsupport v hx)))
        have he : ‖testPlus u x‖^2=(1:ℝ) := by exact congr_arg (fun y : ℝ≥0 => (↑y:ℝ)) ht
        rw [mul_comm (star _),Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,he,Complex.ofReal_one,one_mul]
    rw [← he,← hμ.absolute]; exact h u w (he.symm ▸ hv)
end YM.TraceExtension.Wick
