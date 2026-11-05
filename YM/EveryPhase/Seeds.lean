import YM.EveryPhase.Shell

/-!
# Seed the analytic jump by integration on a Euclidean cylinder

For strictly Euclidean exterior times and Euclidean slot for the stress, can
integrate the weighted divergence on positive and negative sides
simultaneously. Endpoint at zero height needn't be a regular value and we
need no direct derivative identity at it. Use continuity of interval
primitive of the *classically integrable shell*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Metric Boundary Next.BOUNDARY Mink Complex Probe Table
open Work.C20
open scoped Topology BigOperators Interval ContDiff LineDeriv
variable {n : ℕ}

def hatChi (c : ContDiffBump (0:ℝ)) (g : Probe Space3) (u : ℝ) (x : E4) := c (YM.time x-u)*(g (spatial x)).re

lemma hat_diff (c : ContDiffBump (0:ℝ)) (g : Probe Space3) (u) : ContDiff ℝ ∞ (hatChi c g u) := by
  unfold hatChi
  exact (c.contDiff.comp (clockL.contDiff.sub contDiff_const)).mul
    ((Complex.reCLM.contDiff.comp (g.smooth ⊤)).comp restL.contDiff)
lemma hat_size (c : ContDiffBump (0:ℝ)) (g : Probe Space3) (hg : HasCompactSupport ⇑g) (u) :
    HasCompactSupport (hatChi c g u) ∧ tsupport (hatChi c g u) ⊆ {x | |YM.time x-u| ≤ c.rOut} := by
  let K : Set E4 := {x | |YM.time x-u| ≤ c.rOut}
  have hp : tsupport (hatChi c g u) ⊆ K := by
    refine closure_minimal (fun x hx => ?_) (isClosed_le (by fun_prop) continuous_const)
    by_contra HH
    change ¬ |YM.time x-u| ≤ c.rOut at HH; apply hx; unfold hatChi
    rw [c.zero_of_le_dist (by simpa [Real.dist_eq] using (lt_of_not_ge HH).le),zero_mul]
  refine ⟨?_,hp⟩
  let k := tsupport g ×ˢ closedBall u c.rOut
  refine HasCompactSupport.intro ((hg.prod (isCompact_closedBall u c.rOut)).image divide.symm.continuous) ?_
  intro x hx; by_contra e
  have he := hp (subset_closure (a:=x) (show x∈support (hatChi c g u) from e))
  have hb : spatial x∈tsupport g := by
    by_contra h; apply e; simp [hatChi,image_eq_zero_of_notMem_tsupport h]
  apply hx; refine ⟨(spatial x,YM.time x),⟨hb,?_⟩,by simp⟩
  simpa [Real.dist_eq] using (show |YM.time x-u| ≤ c.rOut from he)
lemma hat_jets (c : ContDiffBump (0:ℝ)) (g : Probe Space3) (hr : ∀ r, ((g r).re:ℂ)=g r) (u s : ℝ) (y : Space3) :
    (((Analysis.D (basis timeAxis) (hatChi c g u) (position y (u+s)):ℝ):ℂ))=((deriv c s:ℝ):ℂ)*g y ∧
    ∀ i : SpaceAxis, (((Analysis.D (basis i.castSucc) (hatChi c g u) (position y (u+s)):ℝ):ℂ))=
      (c s:ℂ)*drift g i y := by
  let x := position y (u+s)
  let f := fun p : E4 => c (YM.time p - u)
  have hf : DifferentiableAt ℝ f x := ((c.contDiff.differentiable (n:=∞) (by simp)) _).comp x
    ((clockL.differentiableAt).sub (differentiableAt_const _))
  have hv : DifferentiableAt ℝ (fun p : E4 => g (spatial p)) x := (g.differentiableAt).comp x restL.differentiableAt
  have he (a : Axis) : (((Analysis.D (basis a) (hatChi c g u) x:ℝ):ℂ))=
      (c s:ℂ)* fderiv ℝ g y (spatial (basis a)) + g y *((deriv c s*YM.time (basis a):ℝ):ℂ) := by
    have hw := ofRealCLM.hasFDerivAt.comp x (((hat_diff c g u).differentiable (by simp)) x).hasFDerivAt
    have hL : DifferentiableAt ℝ (fun p : E4 => (f p:ℂ)) x := ofRealCLM.differentiableAt.comp x hf
    rw [show ofRealCLM ∘ hatChi c g u=fun p => (f p:ℂ)*g (spatial p) by funext p; simp [hatChi,f,hr] ] at hw
    have ht := DFunLike.congr_fun hw.fderiv (basis a)
    have hF : HasFDerivAt f ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv c s)).comp clockL) x := by
      have hp : YM.time x-u=s := by simp [x]
      have hu := ((clockL.hasFDerivAt (x:=x)).sub_const u)
      rw [← hp]
      exact (((c.contDiff.differentiable (n:=∞) (by simp)) _).hasDerivAt.hasFDerivAt).comp x hu
    rw [fderiv_fun_mul hL hv] at ht
    have hq : fderiv ℝ (fun p => (f p:ℂ)) x (basis a)=((deriv c s:ℝ):ℂ)*(YM.time (basis a):ℂ) := by
      change fderiv ℝ ((⇑ofRealCLM) ∘ f) x (basis a)=_
      rw [(ofRealCLM.hasFDerivAt.comp x hF).fderiv]; simp [mul_comm]
    have hh : fderiv ℝ (fun p => g (spatial p)) x (basis a)=fderiv ℝ g y (spatial (basis a)) := by
      change fderiv ℝ ((⇑g) ∘ (⇑restL)) x (basis a)=_
      rw [fderiv_comp x g.differentiableAt restL.differentiableAt, restL.fderiv]; simp [x]
    change ((f x:ℂ)*fderiv ℝ (fun p => g (spatial p)) x (basis a)+g (spatial x)*fderiv ℝ (fun p => (f p:ℂ)) x (basis a))= _ at ht
    rw [hq,hh,show f x=c s by simp [f,x],show spatial x=y by simp [x],← ofReal_mul] at ht
    exact ht.symm
  constructor
  · rw [he]; simp [mul_comm]
  intro i
  have ht : YM.time (basis i.castSucc)=0 := by simp [YM.time,Ne.symm (show i.castSucc≠timeAxis from Fin.castSucc_ne_last i)]
  have hj : spatial (basis i.castSucc)=needle i := by
    ext l; by_cases h : l=i <;> simp [basis_eq,needle,Ray.fromAxis,spatial,h]
  rw [he]; simp [ht,hj, drift_at]

def pureReady (x : Points (n+1)) (k : Fin (n+1)) (d : ℝ) := 0<d ∧ ∀ s∈Ioc 0 d,
    hole k.succ (pureU x) ((((YM.time (x k)+s):ℝ):ℂ)*I) ∈ strict (n+2) ∧
    hole k.castSucc (pureU x) ((((YM.time (x k)-s):ℝ):ℂ)*I) ∈ strict (n+2)
lemma preparation (x : Points (n+1)) (hx : x∈ordered (n+1)) (k : Fin (n+1)) : ∃ d, pureReady x k d := by
  obtain ⟨d,hd,h⟩ := affords (pure_time hx) k
  refine ⟨d,hd,?_⟩; intro s hs
  have hu := h.self_of_nhds
  change _ ∧ (∀ (z : ℂ) (s : ℝ), _ → _ → _ → _) at hu
  simpa only [ofReal_add,ofReal_sub,add_mul,sub_mul,pureU] using hu.2 (pureU x k) s rfl hs.1 hs.2

lemma hat_window (x : Points (n+1)) (k : Fin (n+1)) {d : ℝ} (h : pureReady x k d)
    (c : ContDiffBump (0:ℝ)) (hc : c.rOut < d)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : g =ᶠ[𝓝 (spatial (x k))] fun _ => (1:ℂ)) :
    Window (Points.rearrange (first k) x) (hatChi c g (YM.time (x k))) := by
  let u := YM.time (x k)
  refine ⟨hat_diff ..,(hat_size c g hg u).1, ?_, ?_⟩
  · rw [Points.rearrange_at,first_coord]
    have he : Tendsto (fun p => YM.time p-u) (𝓝 (x k)) (𝓝 0) := by
      simpa [u] using ((clock_cont.tendsto (x k)).sub_const u)
    filter_upwards [he.eventually c.eventuallyEq_one,(rest_cont.tendsto (x k)).eventually hr] with i hi hI
    change c (_-u)*_=1
    change c (YM.time i-u) = 1 at hi; rw [hi,hI]; simp
  intro i he
  rw [Points.rearrange_at,first_next] at he
  let j := k.succAbove i
  have hp : |YM.time (x j)-u|≤c.rOut := (hat_size c g hg u).2 he
  have hv := h.2 d ⟨h.1,le_rfl⟩
  rcases lt_or_gt_of_ne (show j ≠ k from Fin.succAbove_ne _ _) with hj|hj
  · have he := hv.2 (show k.castSucc.succAbove j< k.castSucc from
      (Fin.succAbove_lt_iff_castSucc_lt ..).2 (Fin.castSucc_lt_castSucc_iff.mpr hj))
    simp only [hole_self,hole_next, pureU, Complex.mul_I_im, ofReal_re] at he
    have he : YM.time (x j)<u-d := he
    linarith [(abs_le.mp hp).1]
  have ht := hv.1 (show k.succ < k.succ.succAbove j from
    (Fin.lt_succAbove_iff_lt_castSucc ..).2 (Fin.succ_lt_succ_iff.mpr hj))
  simp only [hole_self,hole_next,pureU,Complex.mul_I_im,ofReal_re] at ht
  have ht : u+d<YM.time (x j) := ht
  linarith [(abs_le.mp hp).2]

lemma split_space {f : E4 → ℂ} (u : ℝ) (hf : Integrable f) :
    Integrable (fun s : ℝ => ∫ r, f (position r (u+s))) ∧
    (∫ y, f y)=∫ s : ℝ, ∫ r, f (position r (u+s)) := by
  let e := divide.symm.toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e volume volume := MeasurePreserving.symm e.symm volume_divide
  have he : Integrable (f ∘ e) (volume.prod volume) := (hp.integrable_comp_emb e.measurableEmbedding).mpr hf
  let g := fun s : ℝ => ∫ r, f (position r s)
  have hh : Integrable g := he.integral_prod_right
  change Integrable (fun s => g (u+s)) ∧ _
  constructor
  · exact (measurePreserving_add_left volume u).integrable_comp_of_integrable hh
  rw [← hp.integral_comp e.measurableEmbedding]
  change (∫ p, (f ∘ e) p ∂(volume.prod volume))=∫ s, g (u+s)
  rw [integral_prod_symm _ he,integral_add_left_eq_self]; rfl

lemma curtainsFTC (d : ℝ) (hd : 0<d) (f F Y : ℝ → ℂ) (hf : Integrable f) (hg : support f ⊆ Ioo (-d) d)
    (hF : F d=0) (hY : ∀ s∈Ioc 0 d, HasDerivAt F (f s+f (-s)) s)
    (hv : F =ᶠ[𝓝[>] 0] Y) : Tendsto Y (𝓝[>] 0) (𝓝 (-∫ s, f s)) := by
  let w := fun s => f s+f (-s)
  have he : Integrable (fun s : ℝ => f (-s)) := by
    simpa using (integrable_comp_mul_left_iff f (show (-1:ℝ)≠0 by norm_num)).2 hf
  have hw : Integrable w := hf.add he
  have ht : (∫ s in 0..d, w s)=∫ s, f s := by
    unfold w; rw [intervalIntegral.integral_add (hf.intervalIntegrable ..)
      he.intervalIntegrable,
      intervalIntegral.integral_comp_neg, neg_zero, add_comm, intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable ..) (hf.intervalIntegrable ..),
      intervalIntegral.integral_of_le (by linarith)]; exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by_contra fun h => hx (Ioo_subset_Ioc_self (hg h))
  have hu := intervalIntegral.continuous_primitive (fun a b => hw.intervalIntegrable) d
  rw [← ht, intervalIntegral.integral_symm d 0, neg_neg]
  apply Tendsto.congr' _ ((hu.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi 0)))
  refine EventuallyEq.trans ?_ hv
  filter_upwards [(nhdsGT_basis_Ioc 0).mem_of_mem hd] with s hs
  change (∫ s in d..s, w s)=F s
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun i hi => hY i (by
    rw [uIcc_comm,uIcc_of_le hs.2] at hi; exact ⟨hs.1.trans_le hi.1,hi.2⟩)) (hw.intervalIntegrable ..),hF,sub_zero]

end YM.EveryPhase.Stress
