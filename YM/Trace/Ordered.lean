import YM.Trace.AnalyticIntegral
import YM.Trace.Fields
import YM.Trace.ConeValues

/-! Link translation spectral data obtained from fields after phase selection back to exact
strict Euclidean values, using `Region.roots`, `Opens`, and uniqueness at the boundary. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
namespace YM.Trace
open Boundary Function Filter MeasureTheory Measure Set Complex Spectral
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order}
    (Y : Spec.Final C F S)

abbrev VPair := Points 2

def probe2 (f g : Probe E4) := Joint.materialize 2 ![Probe.bar f, g]
lemma probe2_eq (f g : Probe E4) (p : VPair) : probe2 f g p = star (f (p 0)) * g (p 1) := by
  rw [probe2,Joint.material_at]; simp [Fin.prod_univ_two]

def height2 (z : ℂ) (p : VPair) := (![(p 0 timeAxis),(p 1 timeAxis)+z] : Times 2)
@[simp] lemma height_one (z : ℂ) (p : VPair) : height2 z p 0 = (time (p 0)) := rfl
@[simp] lemma height_two (z : ℂ) (p : VPair) : height2 z p 1 = (time (p 1):ℂ)+z := rfl
lemma height_strict (z : upper) (p : VPair) : height2 z p ∈ strict 2 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  change ((p 0 timeAxis :ℂ)).im < _
  change ((p 0 timeAxis :ℂ)).im < ((p 1 timeAxis : ℂ)+ z.val).im
  simpa only [ofReal_im,add_im,zero_add] using
    (show 0<z.val.im from z.prop)
lemma height_cont : Continuous (uncurry height2) := by
  refine continuous_pi fun i => ?_; fin_cases i
  · exact continuous_ofReal.comp (Mink.clock_cont.comp (by fun_prop))
  exact (continuous_ofReal.comp (Mink.clock_cont.comp (by fun_prop : Continuous (fun (p : ℂ×VPair) => p.2.ofLp 1)))).add continuous_fst

def liftTwo (O : S.Tag) (z : ℂ) (x : VPair) := Y.A.waves.F 2
    (height2 z x) (Boundary.trace x) (fun _ => S.pin O.1 O.2)

def testedTwo (O : S.Tag) (u v : Test4) (z : ℂ) := ∫ x : VPair, liftTwo Y O z x * probe2 u v x

lemma lift_two_cont (O : S.Tag) : ContinuousOn (uncurry (liftTwo Y O)) (upper ×ˢ univ) := by
  refine (Y.realization.chosen.heat.together 2 _).comp (f:=fun p : ℂ × VPair => (height2 p.1 p.2,Boundary.trace p.2)) ?_ ?_
  · refine Continuous.continuousOn (Continuous.prodMk ?_ ?_)
    · exact height_cont
    apply Continuous.comp (continuous_pi fun i => Mink.rest_cont.comp (f:=fun x : VPair => WithLp.ofLp x i) (by fun_prop)) continuous_snd
  exact fun ⟨_,p⟩ hz => ⟨height_strict ⟨_,hz.1⟩ p,mem_univ _⟩

omit Y in
lemma compact_tested {u v : Test4} (hu : CC u) (hv : CC v) : CC (probe2 u v) := by
  let t (i : Fin 2) := (![tsupport u,tsupport v] : Fin 2 → Set E4) i
  let k := WithLp.toLp 2 '' {p : Fin 2 → E4| ∀ i,p i∈t i}
  have ht : IsCompact k := IsCompact.image (isCompact_pi_infinite (fun i => by
      fin_cases i
      · exact hu
      exact hv)) (PiLp.continuous_toLp ..)
  refine ht.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun p hp => ⟨WithLp.ofLp p,?_,rfl⟩) ht.isClosed)
  intro i
  fin_cases i
  · exact (by apply subset_tsupport; intro hx; apply hp; rw [probe2_eq,hx,star_zero,zero_mul] : p 0 ∈ tsupport u)
  exact (by apply subset_tsupport; intro hx; apply hp; rw [probe2_eq,hx,mul_zero] : p 1 ∈ tsupport v)

set_option pp.proofs false in
set_option maxRecDepth 10000 in
lemma lift_point_analytic (O : S.Tag) (x : VPair) : DifferentiableOn ℂ (liftTwo Y O · x) upper := by
  apply DifferentiableOn.comp (g:=fun t : Times 2=> Y.A.waves.F 2 t (Boundary.trace x) (fun _ => S.pin O.1 O.2)) (f:=fun z : ℂ=> height2 z x) (s:=upper)
    (t:=strict 2) (Y.realization.chosen.heat.hol 2 _ (Boundary.trace x)) ?_ (fun z h=> height_strict ⟨_,h⟩ x)
  refine differentiable_pi.mpr ?_ |>.differentiableOn
  intro i; fin_cases i
  · exact differentiable_const ((time (x 0)):ℂ)
  exact differentiable_const ((time (x 1)):ℂ) |>.add differentiable_id

lemma lift_two_analytic (O : S.Tag) (u v : Test4) (hu : CC u) (hv : CC v) :
    DifferentiableOn ℂ (testedTwo Y O u v) upper := by
  let k := tsupport (probe2 u v)
  have ht := compact_tested hu hv
  let K (z : ℂ) (x : VPair) := liftTwo Y O z x * probe2 u v x
  change DifferentiableOn ℂ (fun z=>∫ x,K z x) upper
  refine contour_analytic (μ:=volume) (F:=K) (u:=k) upper_open ht (fun z hz x he=> ?_) ?_
      (fun x => (lift_point_analytic Y O x).mul (show DifferentiableOn ℂ (fun z : ℂ=>probe2 u v x) upper from differentiableOn_const _))
  · exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport he)
  exact (lift_two_cont Y O).mul ((probe2 u v).continuous.comp continuous_snd).continuousOn

variable {μ : Measure E4}
def damping (z : ℂ) (p : E4) := cexp ((time p:ℂ)*I*z)
@[simp] lemma heat_size (z) (p) : ‖damping z p‖ = Real.exp (-z.im * time p) := by
  rw [damping,norm_exp]; simp only [mul_re,mul_im,ofReal_re,ofReal_im,I_re,I_im,mul_zero,mul_one,sub_zero,zero_mul,add_zero,zero_sub]; congr 1; ring

set_option linter.unusedVariables false in
def paid (μ : Measure E4) (u v : Test4) (p : E4) := star (plus u p) * plus v p
def heatTest (μ : Measure E4) (u v : Test4) (z : ℂ) := ∫ p,
    paid μ u v p * damping z p ∂μ
def heatPoint (μ : Measure E4) (w : ℂ) (x : VPair) := ∫ p, Probe.plane p (x 1-x 0) * damping w p ∂μ

variable (hm : Tempered μ) (ht : μ (Mink.coneᶜ)=0)
include hm
lemma bound_paid (u v) : ∃ c : ℝ, ∀ x, ‖paid μ u v x‖ ≤ c := by
  refine ⟨Probe.size 0 0 (plus u) * Probe.size 0 0 (plus v),fun x => ?_⟩
  rw [paid,norm_mul,norm_star]; refine mul_le_mul (SchwartzMap.norm_le_seminorm ..) (SchwartzMap.norm_le_seminorm ..) (norm_nonneg _) (apply_nonneg ..)
lemma integrable_paid (u v) : Integrable (paid μ u v) μ := by
  obtain ⟨n,A,h⟩ := hm
  refine h.integrable_prod ENNReal.ofReal_lt_top (plus u) (plus v) _ (by unfold paid; fun_prop) 1
     (fun x => by rw [paid,norm_mul,norm_star,one_mul])

include ht
lemma heatPoint_cont {w : ℂ} (hz : 0<w.im) : Continuous (heatPoint μ w) := by
   refine continuous_iff_continuousAt.mpr fun x =>
      tendsto_integral_filter_of_dominated_convergence
        (fun p:E4 => Real.exp (-w.im * time p)) ?_ ?_ (hm.integrable_exp μ ht hz) ?_
   · exact .of_forall fun r => by unfold damping; exact (by fun_prop : Continuous _).aestronglyMeasurable
   · simp
   filter_upwards with p
   exact ContinuousAt.tendsto (by fun_prop : ContinuousAt (fun n : VPair=> _) x)
lemma heatTest_analytic (u v : Test4) : DifferentiableOn ℂ (heatTest μ u v) upper := by
  intro w hw
  let L := paid μ u v; let D (z : ℂ) (p : E4) := L p * (damping z p * ((time p:ℂ)*I))
  obtain ⟨C,hC⟩:=bound_paid hm u v
  have hc : 0≤C := (norm_nonneg _).trans (hC 0)
  have hE : ∀ᵐ p ∂μ, 0 ≤ time p := (show ∀ᵐ p ∂μ,p∈ Mink.cone from (ae_iff.mpr ht)).mono fun p h => (norm_nonneg (spatial p)).trans h
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀:=w) (F':=D) (F:=fun z p => L p * damping z p) (μ:=μ)
     (s:={p|w.im/2<p.im}) (by refine continuous_im.continuousAt.preimage_mem_nhds ?_; exact lt_mem_nhds ((show w.im/2 <w.im by change 0<w.im at hw; exact half_lt_self hw)))
     (.of_forall fun z => ((by unfold L paid damping; exact (by fun_prop : Continuous _).aestronglyMeasurable)))
     ((integrable_paid hm u v).norm.mono' (by unfold L paid damping; fun_prop)
       (hE.mono (fun p he => by
          change ‖L p * damping w p‖ ≤ _
          rw [norm_mul,heat_size]
          exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by change w.im>0 at hw; nlinarith)))))
     (by unfold D L paid damping; fun_prop)
     (hE.mono (fun p hp z hz => by
        change ‖D z p‖ ≤ _; simp only [D,norm_mul,norm_I,mul_one,norm_real,Real.norm_eq_abs]
        have he : Real.exp (-z.im * time p) ≤ Real.exp (- (w.im/2) * (time p)) := Real.exp_le_exp.mpr (by change w.im/2<z.im at hz; nlinarith)
        rw [heat_size,mul_comm _ (|time p|)]; gcongr <;> first | exact hC p | exact le_add_of_nonneg_left (by norm_num)))
     (hm.integrable_damp μ ht (show 0<w.im/2 by change w.im>0 at hw; linarith) |>.const_mul C)
     (Filter.Eventually.of_forall (fun p => fun z hz =>
       show HasDerivAt _ _ _ from by
         unfold D damping
         convert! (((hasDerivAt_id' z).const_mul ((time p:ℂ)*I)).cexp.const_mul (L p)) using 1
         ring))
  exact this.2.differentiableAt.differentiableWithinAt

private abbrev tick (t : ℝ) := t • basis timeAxis
omit hm ht
lemma plus_ticked (v : Test4) (t : ℝ) (p : E4) : plus (Probe.ahead (tick t) v) p = plus v p * damping t p := by
  simp only [plus_eq,Probe.ahead_at,← integral_mul_const]
  rw [← integral_add_left_eq_self (μ:=volume) (fun x : E4 => Probe.plane x p * v (x-tick t)) (tick t)]
  apply integral_congr_ae; filter_upwards with x
  rw [Probe.plane_dot (tick _ + _),Probe.plane_add, Probe.plane_dot p x, add_sub_cancel_left]
  have he : inner ℝ p (tick t)= time p*t := by
    rw [real_inner_smul_right, Mink.pairing, Mink.roll_space,Mink.roll_clock, inner_zero_right,mul_one,zero_add,mul_comm]
  rw [Probe.plane, he, damping,Complex.ofReal_mul, show ((↑(time p):ℂ)*↑t*I)=↑(time p)*I*↑t by ring,mul_assoc,mul_comm (cexp _)]

private def profileTwo : Heights 2 := ![0,1]
private lemma pair_shift (s : ℝ) (t : ℝ) (p : VPair) :
    Boundary.shift (p+points (fun i=>if i=0 then 0 else tick t)) (s • profileTwo) = height2 ((t:ℂ)+s*I) p ∧
            Boundary.trace (p+points (fun i=>if i=0 then 0 else tick t)) = Boundary.trace p := by
       constructor <;> ext1 i <;> fin_cases i
       · change ((time (p 0+0)):ℂ)+(s*0:ℝ) * I= (p 0 timeAxis)
         simp [time]
       · change (↑(time (p 1+tick t)):ℂ)+(s*1:ℝ)*I= ((time (p 1):ℂ)+((t:ℂ)+s*I))
         simp only [mul_one,Mink.clock_add,Mink.clock_mul, Mink.roll_clock,ofReal_add]
         ring
       · change spatial (p 0+0)=_; simp [Boundary.trace]
       change spatial (p 1+tick t)=_; simp [Boundary.trace]
       -- projection simplification

lemma actual_boundary (u v : Test4) (e t : ℝ) :
    Tendsto (fun s : ℝ => testedTwo Y ⟨4,theta Y e⟩ u v ((t:ℂ)+s*I)) (𝓝[>] 0)
      (𝓝 (inner ℂ (oneWave Y (S.pin 4 (theta Y e)) u)
           (oneWave Y (S.pin 4 (theta Y e)) (Probe.ahead (tick t) v)))) := by
  have he := Y.realization.chosen.emerges.profile 2 (fun _ => S.pin 4 (theta Y e)) profileTwo (by
       intro i j h; fin_cases i <;> fin_cases j <;> simp_all [profileTwo]) (probe2 u (Probe.ahead (tick t) v))
  rw [← exact_pair] -- witness W at RHS
  refine he.congr (fun s => by
      -- test weights shift
      let q : VPair := points (fun i => if i=0 then 0 else tick t)
      unfold Waves.atSlopes testedTwo
      rw [← integral_add_right_eq_self (μ:=volume) (f:=fun x : VPair => Y.A.waves.restricted _ _ x * probe2 u (Probe.ahead (tick t) v) x) q]
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      dsimp only; unfold liftTwo Waves.restricted; rw [(pair_shift s t p).1,(pair_shift s t p).2]
      congr 1
      rw [probe2_eq,probe2_eq]; simp [q,points])

include hm ht in
lemma model_boundary (u v : Test4) (t : ℝ) : Tendsto (fun s : ℝ => heatTest μ u v ((t:ℂ)+s*I)) (𝓝[>] 0) (𝓝 (heatTest μ u v t)) := by
   refine tendsto_integral_filter_of_dominated_convergence (fun p:E4 => ‖paid μ u v p‖)
      (.of_forall fun s => (by unfold paid damping; fun_prop)) ?_ (integrable_paid hm .. |>.norm)
      (.of_forall fun p => ?_)
   swap; · simpa only [ofReal_zero,zero_mul,add_zero] using! (ContinuousAt.tendsto (x:=(0:ℝ)) (by unfold damping; fun_prop : ContinuousAt (fun s : ℝ => paid μ u v p * damping (↑t+↑s*I) p) _)).mono_left nhdsWithin_le_nhds
   filter_upwards [self_mem_nhdsWithin] with s hs
   have he : ∀ᵐ p∂μ, p ∈ Mink.cone := ae_iff.mpr ht
   filter_upwards [he] with p hp
   rw [norm_mul]
   refine mul_le_of_le_one_right (norm_nonneg _) (by
     rw [heat_size]; apply Real.exp_le_one_iff.mpr
     exact mul_nonpos_of_nonpos_of_nonneg (by simp; exact (show s>0 from hs).le) ((norm_nonneg _).trans hp))

include hm ht in
theorem tested_ordered_match (a b : Test4) (ha : CC a) (hb : CC b) (e : ℝ)
    (hμ : ∀ f g : Test4, inner ℂ (oneWave Y (S.pin 4 (theta Y e)) f) (oneWave Y (S.pin 4 (theta Y e)) g)=∫ k,paid μ f g k ∂μ) :
    EqOn (testedTwo Y ⟨4,theta Y e⟩ a b) (heatTest μ a b) upper := by
    intro w hw; apply sub_eq_zero.mp
    apply (vanishes_of_vertical_limit (F:= fun s => testedTwo Y ⟨4,theta Y e⟩ a b s - heatTest μ a b s)
      (lift_two_analytic Y _ _ _ ha hb |>.sub (heatTest_analytic hm ht a b)) ?_ hw)
    intro t
    have H := actual_boundary Y a b e t
    have heq (p : E4) : paid μ a b p * damping t p=paid μ a (Probe.ahead (tick t) b) p := by
        simp [paid,plus_ticked,mul_assoc]
    rw [hμ,← show heatTest ..=_ from (integral_congr_ae (ae_of_all _ heq) : heatTest μ a b t = _)] at H
    simpa only [sub_self] using H.sub (model_boundary hm ht a b t)

omit Y in
lemma product_separates (K : VPair→ℂ) (hc : Continuous K) (h : ∀ (a b : Probe E4), CC a → CC b → (∫ x,K x * probe2 a b x)=0) :
    K=0 := funext (fun p => by
    by_contra! hz
    change K p ≠ 0 at hz
    let r x := ((star (K p)) * K x).re
    have hr : Continuous r := continuous_re.comp (continuous_const.mul hc)
    have hi : 0<r p := by dsimp only [r]; rw [mul_comm, ← starRingEnd_apply, mul_conj,ofReal_re]; exact (normSq_pos).mpr hz
    let l (u : E4×E4) := points (![u.1,u.2])
    let P := (p 0,p 1)
    have hl : Continuous l := by
        apply (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i : Fin 2 => ?_)
        fin_cases i
        · exact continuous_fst
        exact continuous_snd
    have hL (z : VPair) : l (z 0,z 1)=z := PiLp.ext (fun i => by fin_cases i <;> rfl)
    obtain ⟨δ,hδ,hU,Hd⟩ : ∃ δ>0, 0<δ/2 ∧ ∀ q : E4×E4, dist q P < δ → 0<r (l q) := by
       obtain ⟨δ,hδ,Q⟩ := Metric.mem_nhds_iff.mp (((hr.comp hl).tendsto P).eventually (lt_mem_nhds (show 0<(r ∘ l) P by change 0<r (l (p 0,p 1)); rwa [hL p])))
       exact ⟨_,hδ, by linarith,Q⟩
    let A (z : E4) : ContDiffBump z := ⟨δ/4,δ/2,by positivity,by linarith⟩
    let f (z : E4) : Probe E4 := (HasCompactSupport.toSchwartzMap (HasCompactSupport.comp_left (f:=⇑(A z))
       ((A z).hasCompactSupport) Complex.ofReal_zero) (Complex.ofRealCLM.contDiff.comp (A z).contDiff))
    have hF (z x : E4) : f z x=((A z x):ℂ) := rfl
    let g := probe2 (f (p 0)) (f (p 1)); let G (z : VPair) := A (p 0) (z 0) * A (p 1) (z 1)
    have hG (z : VPair) : g z=(G z:ℂ) := by
         dsimp only [g,G]; rw [probe2_eq,hF,hF, ← starRingEnd_apply,Complex.conj_ofReal, ofReal_mul]
    have hx z : CC (f z) := by
      change HasCompactSupport (Complex.ofReal ∘ ↑(A z)); exact HasCompactSupport.comp_left ((A z).hasCompactSupport) Complex.ofReal_zero
    have hg : HasCompactSupport ⇑g := compact_tested (hx _) (hx _)
    have hP : HasCompactSupport G := ?_
    have htG : Continuous G := ?_
    have hpos (z : VPair) : 0 ≤ (G z)*(r z) := by
          by_cases h : dist (z 0,z 1) P ≤ δ/2
          · have hp := Hd _ (h.trans_lt (by linarith)); rw [hL] at hp
            exact mul_nonneg (mul_nonneg ((A _).nonneg) ((A _).nonneg)) hp.le
          suffices G z=0 by rw [this,zero_mul]
          contrapose! h
          -- nonzero ⇒ both components in tsupport ball
          obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp h
          rw [← mem_support,ContDiffBump.support_eq] at h1 h2
          rw [Prod.dist_eq]; exact max_le (Metric.mem_ball.mp h1).le (Metric.mem_ball.mp h2).le
    suffices H : ∫ z, G z*r z = 0 from ?_
    · have he := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hpos)
           ((htG.mul hr).integrable_of_hasCompactSupport (hP.mul_right (f':=r)))).mp H -- precedence
      replace he := (htG.mul hr|>.ae_eq_iff_eq volume continuous_const).mp he
      have hx := mul_eq_zero.mp (congrFun he p)
      have hs (x : E4) : A x x=1 := (A x).one_of_mem_closedBall (Metric.mem_closedBall.mpr (by change dist x x ≤ δ/4; simp; linarith))
      have : G p ≠ 0 := mul_ne_zero (show A _ _ ≠ (0:ℝ) from hs (p 0) ▸ one_ne_zero)
          (show A _ _ ≠ (0:ℝ) from hs (p 1) ▸ one_ne_zero)
      exact hx.elim this hi.ne'
    · let J (z : VPair) := (star (K p)) * (K z * g z)
      suffices H0 : ∫ z, J z=0 by
          have ht : ∫ z,(J z).re = 0 := (show _ from (_root_.integral_re (f:=J)
              (by apply Continuous.integrable_of_hasCompactSupport (by exact (continuous_const.mul (hc.mul g.continuous)))
                  exact HasCompactSupport.mul_left (HasCompactSupport.mul_left hg)))).trans
                     (show RCLike.re (∫ z,J z)=0 by rw [H0]; rfl)
          convert! ht using 2
          ext1 x; dsimp only [r,J]; rw [hG,← mul_assoc,Complex.mul_re]; simp [mul_comm]
      unfold J
      erw [MeasureTheory.integral_const_mul, h _ _ (hx _) (hx _),mul_zero]
    · dsimp only [G]; exact (((A _).continuous.comp (f:=fun q : VPair => q 0) (by fun_prop)).mul ((A _).continuous.comp (f:=fun q : VPair => q 1) (by fun_prop)))
    refine HasCompactSupport.of_support_subset_isCompact (K:=tsupport g) hg.isCompact ?_
    intro x hx; apply subset_tsupport; rw [mem_support,hG,ne_eq,ofReal_eq_zero]; exact hx
)

include hm ht in
lemma adjusted_value (z : upper) (u v : Test4) :
     heatTest μ u v z = ∫ r, heatPoint μ z.val r * probe2 u v r := by
   let w x p := Probe.plane p (x 1-x 0) * damping z.val p * probe2 u v x
   letI := hm.finite_compacts
   have hs := hm.integrable_exp μ ht z.property
   have hw : Integrable (uncurry w) (volume.prod μ) := by
      apply (integrable_prod_iff (by dsimp [w,uncurry,damping]; fun_prop)).2
      have he x p : ‖w x p‖= Real.exp (-z.val.im * time p) * ‖probe2 u v x‖ := by simp [w]
      simp_rw [uncurry_apply_pair]
      refine ⟨.of_forall fun x=> (hs.mul_const _).mono' (by unfold w damping; fun_prop) (.of_forall fun p=> (he x p).le),?_⟩
      simp_rw [he,MeasureTheory.integral_mul_const]
      exact (probe2 u v).integrable.norm.const_mul _

   have hi p : paid μ u v p * damping z p=∫ r,w r p := by
      let F (j : Fin 2) : E4 → ℂ := fun x=> Probe.plane x (![(-p),p] j) * (![Probe.bar u,v] j) x
      have he (r : VPair) : w r p=(∏ i : Fin 2, F i (r i))*damping z p := by
          dsimp only [w,F]; rw [probe2_eq, Fin.prod_univ_two,show r _-r _=r 1+ -(r 0) from rfl, Probe.plane_add,
             Probe.plane_inverse,Probe.plane_dot p]
          simp only [Matrix.cons_val_zero,Matrix.cons_val_one, Probe.bar_at]; rw [Probe.plane_inverse,Probe.plane_dot (r 0)]; ring
      have hv : MeasurePreserving (fun x : VPair=>WithLp.ofLp x) (volume : Measure VPair) volume := Points.volume_product _
      let e := MeasurableEquiv.toLp 2 (Fin 2 → E4)
      rw [(show ∫ r,w r p = (∫ (r : Fin 2 → E4), (∏ i,F i (r i))*damping z p) from by
          rw [integral_congr_ae (ae_of_all _ he),← MeasurePreserving.integral_comp' (f:=e.symm) hv (fun r => (∏ i,F i (r i))*damping z p)]; rfl)]
      change _ = ∫ r:Fin 2→E4, (∏ i,F i (r i))*damping z p
      rw [MeasureTheory.integral_mul_const, integral_fin_nat_prod_volume_eq_prod, Fin.prod_univ_two]
      dsimp [paid]; dsimp only [F]; rw [← plus_eq,← plus_eq]; change _=plus (Probe.bar u) (-p) * plus v p * _; rw [plus_bar]; simp
   unfold heatTest; simp_rw [hi]; rw [← integral_integral_swap hw]; unfold heatPoint; simp_rw [← MeasureTheory.integral_mul_const,w]

include hm ht in
lemma heatPoint_eq (e : ℝ) (hμ : ∀ f g : Test4, inner ℂ (oneWave Y (S.pin 4 (theta Y e)) f) (oneWave Y (S.pin 4 (theta Y e)) g)=∫ k,paid μ f g k ∂μ)
    {z : ℂ} (w : z ∈ upper) (x : VPair) :
    liftTwo Y ⟨4,theta Y e⟩ z x = heatPoint μ z x := by
  apply sub_eq_zero.mp
  let a:=liftTwo Y ⟨4,theta Y e⟩ z; let b := heatPoint μ z; let t := a-b
  suffices H : t=0 from congrFun H x
  apply product_separates
  · have hp : Continuous a := continuousOn_univ.mp ((lift_two_cont Y _).comp (f:=fun p=> (z,p)) (by fun_prop)
        fun p hp=>⟨w,mem_univ _⟩)
    exact hp.sub (heatPoint_cont hm ht w)
  intro u v hu hv
  have hi := compact_tested hu hv
  let J:= probe2 u v
  have hp (f : VPair→ℂ) (he : Continuous f) : Integrable (f * (⇑J)) := (he.mul J.continuous).integrable_of_hasCompactSupport hi.mul_left
  have hca : Continuous a := continuousOn_univ.mp ((lift_two_cont Y _).comp (f:=fun p=> (z,p)) (by fun_prop)
        fun p hp=>⟨w,mem_univ _⟩)
  unfold t; simp_rw [Pi.sub_apply,sub_mul]
  erw [integral_sub (hp _ hca) (hp _ (heatPoint_cont hm ht w)), ← adjusted_value hm ht ⟨z,w⟩ u v,
       ← tested_ordered_match Y hm ht u v hu hv e hμ w]
  change testedTwo Y _ _ _ _ - _ = 0; exact sub_self _

/-- Exact Euclidean ordered two-point function on the selected phase at spatial rest, subtracting
`e` in each slot before passage to the shared field quotient. No unit normalization forced here. -/
def restTrace (e s : ℝ) : ℂ := S.useAt (Y.α.ensemble Y.α.atPoint)
          (points ![0,(s:ℝ) • basis timeAxis]) (fun _ : Fin 2 => ⟨4,theta Y e⟩)

include hm ht in
theorem heat_eq_rest (e : ℝ) (s : ℝ) (hs : 0<s)
    (hμ : ∀ f g : Test4, inner ℂ (oneWave Y (S.pin 4 (theta Y e)) f) (oneWave Y (S.pin 4 (theta Y e)) g)=∫ k,paid μ f g k ∂μ) :
    restTrace Y e s = ((∫ p, Real.exp (-(s:ℝ) * time p) ∂μ):ℂ) := by
   let x := (0 : VPair); let z := s*I
   have hw : z ∈ upper := by simpa only [upper,mem_setOf_eq,z,mul_I_im,ofReal_re]
   have hz := heatPoint_eq Y hm ht e hμ hw x
   unfold liftTwo at hz
   let times : Heights 2 := fun i => (![0,s] : Fin 2→ℝ) i
   let O : S.Tag := ⟨4,theta Y e⟩
   have he := Y.realization.chosen.heat.roots 2 (fun _=> O) (Boundary.trace x) times (by
       intro i j h; fin_cases i <;> fin_cases j <;> try contradiction
       exact hs)
   rw [show (fun i=>(times i:ℂ)*I) = height2 z x from ?_, hz] at he
   swap
   · ext1 i; fin_cases i <;> dsimp [times,height2,x,z] <;> simp
   have hp : place (Boundary.trace x) times=points ![(0:E4),s • basis timeAxis] := PiLp.ext fun j => by
       apply Mink.ext_by <;> fin_cases j <;> simp [place, Boundary.trace, times, points, x]
   rw [hp] at he
   refine he.symm.trans ?_
   unfold heatPoint
   have h1 (p:E4) : Probe.plane p (x 1-x 0) * damping z p = ↑(Real.exp (-(s:ℝ)*time p)) := by
          rw [show x 1-x 0=0 from sub_self _, Probe.plane_zero,one_mul,damping, Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
          exact congr_arg _ (calc (time p:ℂ)*I*(s*I) = (time p:ℂ)*(s*(I*I)) := by ring
                                  _ = _ := by rw [I_mul_I]; ring)
   simp only [h1,integral_complex_ofReal]
end YM.Trace
