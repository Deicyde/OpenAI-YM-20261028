import YM.TraceExtension.Wicket.Holy
set_option autoImplicit false
/-! # small-field transfer. Actual crop gauge across whole radius. Uses true predicate Healthy. Includes equality points. -/
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice RG Wilson Work AnalyticBridge.SectorAffine.Offset Push.Uniform Planned.AtomRegular.Foliage WardBin.Lies Next.Fluctuations Next.SectorChange PhysicalNext.JointLoad Heir
open Finset
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical
variable {X:Type}[NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G:Gauge}{n: Side}{s C:ℝ}{o:Site n}{F:Config G n→ X}{P:BudgetPoint}{k r i:ℕ}{Q:Support n}
private lemma fool {U:Config G n}{g:Site n→ G.El} (T:Collar G P.order)(hp: Canvas P o r U g P.order (Cube.fee T))(ht:Cube.Wire P r T)(V:Slab G n k)(hV:∀ i,P.dirBound o (V i))(hk:k≤ P.order):
   Through P.order ((Cube.moduleBill P r)⁻¹ • launch U o r g V) 0 (Cube.fee T) :=by
    let Y:= launch U o r g V; let s:= Cube.moduleBill P r; let A:=Cube.fee T; have h : 0<s:= mul_pos P.threshold_pos (pow_pos (a:=1+(r:ℝ)) (by positivity) _); have hr:1 ≤ A:=Cube.fee_one T; have hs:s ≤ 1:=ht.2
    have he: ContDiffAt ℝ P.order Y 0:=hp.ready V
    have hv(i) (hi:i≤P.order):‖iteratedFDeriv ℝ i Y 0‖ ≤ A*s:=by
       have hh(x:Site n)(hx:separation o x ≤ r):1+(separation o x:ℝ) ≤ (1+(r:ℝ))^P.power:= by
          apply le_trans (add_le_add_right (show (separation o x:ℝ) ≤ (r:ℝ) from Nat.cast_le.mpr hx) _); exact le_self_pow₀ (by simp) (by have h:=P.power_ge; omega)
       match i with
       | 0=>
         rw [norm_iteratedFDeriv_zero, show Y 0 = _ from launch_zero (V:=U) (g:=g) (o:=o) (r:=r) V]; apply (pi_norm_le_iff_of_nonneg (show 0 ≤ A*s by positivity)).mpr; intro j; by_cases hj:separation o j.1 ≤ r
         · apply (hp.size j hj).trans; unfold s Cube.moduleBill; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hh _ hj) P.threshold_pos.le) (by positivity)
         rw [crop,if_neg hj,norm_zero]; positivity
       | i+1=>
          let k:=i+1; refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v=>?_
          apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (by positivity))).mpr; intro j
          let Z:Directions G n →L[ℝ] G.Color:= ContinuousLinearMap.proj j
          have hw:= hp.derivatives V o hk hV k (by omega) hi j
          have hz : ‖iteratedFDeriv ℝ k (Z ∘ Y) 0‖ ≤ A*s:=by
             let l:= separation o j.1; by_cases hv: l ≤ r
             · rw [if_pos hv] at hw; apply le_trans hw (mul_le_mul_of_nonneg_left _ (by positivity))
               change (P.threshold * (1+(separation j.1 o:ℝ))^P.power)^k ≤ s; rw [separation_comm]; have ht:= P.threshold_pos; exact (pow_le_pow_left₀ (by positivity) (show P.threshold*(1+(l:ℝ))^P.power ≤ s from mul_le_mul_of_nonneg_left (by gcongr) ht.le) k).trans (le_trans (pow_le_pow_of_le_one h.le hs (show 1≤k by omega)) (by simp))
             rw [if_neg hv] at hw; exact hw.trans (by positivity)
          change ‖Z (iteratedFDeriv ℝ k Y 0 v)‖ ≤ _; rw [show Z (iteratedFDeriv ℝ k Y 0 v)=iteratedFDeriv ℝ k (Z ∘ Y) 0 v from (by rw [Z.iteratedFDeriv_comp_left he (Nat.cast_le.mpr hi)];rfl)]
          exact (ContinuousMultilinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_right hz (by positivity))
    have hC : Through P.order (s⁻¹ • Y) 0 (|s⁻¹| *(A*s)):= Through.scale (⟨he,hv⟩:Through _ _ _ _) _
    rw [abs_of_pos (inv_pos.mpr h),mul_comm _ s,inv_mul_cancel_left₀ h.ne'] at hC; exact hC
-- Core quantitative tie. Before Haar, orientation coupling.Use Chart.V small mask.Shin.
section
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels
open scoped BigOperators
variable {G:Gauge}{n:Side}{R:Rep G n}{o:Edge (Site n)}{A K:ℝ}{B:BudgetPoint}{P Q:Support n}{U:Config G n}{F:Mellow G n}
lemma coupon (r:ℕ)(T:Collar G B.order) (ht:Cube.Wire B r T)(hf:Cohort B (tower r) o F)(hQ:tower (r+1) ⊆ Q)(hn: 2*(r+1)< n.val)(hh:∀ (v:G.Color),‖v‖≤1→∀ (x:Directions G n),‖x‖ ≤Cube.fee T→Through B.order (minor (fun U=>F U v) (Cube.moduleBill B r)) x A) : Career B Q F (composeCost B.order A (Cube.fee T)):=by
    let C:= Cube.fee T; intro U hU v hv; have he: Army (increment U) 0:= incrementA _ _; have hy: Healthy B.threshold (tower r) U:= Disjoint.mono_left ((Turret.sprout_mono _ (show r≤r+1 by omega)).trans hQ) hU; let Z:=fun U=>F U v
    have hY: Chart B.order Z U:= hf.earns _ 0 (fun _=>v) he contDiffAt_const (by simpa[Work.G07.at_zero_increment] using hy) hv
    obtain ⟨g,hg⟩:= primed hU (o:=0) (r:=r) hQ hn T (by have h:=B.order_ge; omega) ht; let v':=G.adjoint (g o.1) v; have hv':‖v'‖ ≤ 1:= (G.norm_adjoint ..).le.trans hv
    let F':=fun U=> F U v'; let s:= Cube.moduleBill B r; have hs:0<s:=mul_pos B.threshold_pos (pow_pos (a:=1+(r:ℝ)) (by positivity) _); refine ⟨hY,fun l hl hL=> ?_⟩; let Y:= s⁻¹ • launch U 0 r g l.get; have hx: Through B.order Y 0 C:= fool T hg ht l.get (fun i=> hL _ (List.get_mem ..)) hl
    let J:= journey U l.length l.get; have hz : minor F' s ∘ Y=ᶠ[𝓝 0] Z ∘ J:=by
        filter_upwards [(flowJourney U l.get).eventually hg.seen] with x hx'; unfold minor F' Y Z; dsimp only [Function.comp_apply,Pi.smul_apply]; rw [smul_inv_smul₀ hs.ne',← hf.shift (J x) v g]; refine Eq.symm (hf.sites v' _ _ ?_); intro i hi _; obtain ⟨w,hw,he⟩:=halo_spec.mp (show i.1∈ tower r from hi); exact hx' i (mem_singleton.mp hw ▸ he)
    have hx₀:= ((hh v' hv' (Y 0) (by rw [← norm_iteratedFDeriv_zero (𝕜:=ℝ)]; exact hx.pay 0 (by omega))).comp hx).germ hz
    rw [show leftDerivs (fun U=>F U v) l U= iteratedFDeriv ℝ l.length (Z ∘ J) 0 WardBin.Lies.cart from (by simpa only[List.ofFn_get] using Germ.ordered l.get ((show Germ B.order Z U from hY).prod hl))]; refine le_trans (ContinuousMultilinearMap.le_opNorm ..) ?_; rw [prod_eq_one,mul_one]; exact hx₀.pay l.length hl; intro i _; rw[show WardBin.Lies.cart i=bolt i by ext1 j; simp [bolt, WardBin.Lies.cart, Pi.single_apply]]; exact norm_bolt i
variable {H:Peat G n}{Z:Gal G n}
def rasp(o:Edge (Site n))(Z:Gal G n)(H:Peat G n)(s:ℝ):Mellow G n:=fun U v=> orbC Z H U o v s
lemma calls_c(h: Clouded Z P): Continuous (uncurry (fun U v=> clamor o Z v U)):=by
    have hh: Continuous Z:=WardBin.left_cont _ fun U=> (h.wakes _ (increment U) _ (incrementA U 0)).continuousAt
    let f:=Z ∘ Prod.fst (β:=G.Color); change Continuous fun i:Config G n × G.Color=> (Z i.1) ⬝ᵥ (phB o i.2); simp_rw [← fast_dot]; exact Continuous.clm_apply (dotB.continuous.comp (hh.comp continuous_fst)) ((phB o).continuous.comp continuous_snd)
lemma raspT(s:ℝ)(h:Clouded Z P)(hH:Drift _ H)(hp:GaugeInvariant H)(hx:LocalOn P H): Cohort B P o (rasp o Z H s):=by
    refine ⟨fun w U V hv=>orb_local o w hx h.stout U V hv s,fun U v g=> clam_turn Z H P h hp g U o v s,?_,fun V x t hV he hp he' =>(thunder hH h.wakes V t (fun _=>s) x hV he contDiffAt_const o).of_le le_top⟩
    have hv:Continuous (fun p:Config G n × G.Color=> Tint o p.2 s p.1):= (tint_c o s).comp (f:=fun p:Config G n × G.Color=>(p.2,p.1)) (continuous_snd.prodMk continuous_fst); have he:Continuous H:= WardBin.left_cont _ fun U=> (hH _ (increment U) _ (incrementA U 0)).continuousAt
    exact ((Continuous.comp (calls_c h (o:=o)) (hv.prodMk continuous_snd)).mul (Real.continuous_exp.comp ((he.comp hv).sub (he.comp continuous_fst)))).measurable
open Outer.Nodes
private lemma bandsT(o:Edge (Site n))(v:G.Color)(x:Directions G n)(s a:ℝ)(hp:0<s)(h:Allows k (Orpus o v H Z s) (x,a) C): Allows k (minor (fun U=>rasp o Z H (s*a) U v) s) x C:=by
    let u:= (Orpus o v H Z s); let z(s':Rho G n):= (0,a) + s'; let p(y':Directions G n):= (y',0)+ (0,a); let g:= u ∘ z; let q:Rho G n:=(x,0); have hz:z q= (x,a):=by simp[z,q]
    have he: Allows k g q C:=⟨(hz.symm ▸ h.analytic).comp q (contDiffAt_const.add contDiffAt_id),fun i hi=>?_⟩
    · exact (SectorAffine.allows_first_slice he).germ (Eventually.of_forall fun x=>by unfold minor g z u rasp; simp [Orpus])
    unfold g z; unfold Function.comp; rw[iteratedFDeriv_comp_add_left,show (0,a)+q=(x,a) from hz]; exact h.norm_le i hi
lemma priceT (G:Gauge)(A:ℝ)(hA:1≤A)(k m:ℕ)(hm:1≤ m) : ∃ C Y D:ℝ,0≤C∧ 1 ≤Y∧0≤ D∧∀ (n:Side)(B:BudgetPoint)(T:Collar G B.order)(r:ℕ) (E:ℕ) (Q:Support n) (s h T' w:ℝ) (o:Edge (Site n))(Z:Gal G n)(F:Peat G n), k=B.order→ A=Cube.fee T→ 0≤T'→0≤w→ s=Cube.moduleBill B r→ Cube.Wire B r T → 0<h → kettle m*(h/s)≤ A→ zeff T' A s*(kettle m*(h/s))≤1→ tower (r+1)⊆ Q→ Clouded Z (tower r) → Splendor F (tower r) (k+m+1) T' C→ Drift _ F→ Climate Z (k+m+1) w C→2*(r+1)<n.val →E < m →
    Career B Q (rasp o Z F (loc E*h)) (composeCost k (orbAmt Y w T' A s D (k+m+1)) A):=by
    obtain ⟨C,K,D,hC,hK,hD,H⟩:=brill G A hA k m hm
    refine ⟨C,K,D,hC,hK,hD,fun n B T r E Q s h T' w o Z F hk hh ht hw hv hx hP hp he hp' hY hF hU hZ hn hE=>?_⟩; subst k A s; let c:= Cube.fee T; let s:=Cube.moduleBill B r; have hs:0<s:=mul_pos B.threshold_pos (pow_pos (a:=1+(r:ℝ)) (by positivity) _); let t:ℝ:=loc E*h/s
    have hz:t ≤ kettle m*(h/s):=by unfold t; rw[mul_div_assoc]; exact mul_le_mul_of_nonneg_right (roof m E hE).2 (by positivity)
    apply coupon r T hx (raspT (loc E*h) hY hU hF.symm hF.locale) hp' hn; intro v hv x hx'; refine Through.control ?_
    have ht:= (H n _ F Z _ h _ w o v hv ht hw hs hx.2 hP hp he (by exact hY.rises.2) hZ hF).2 (x,t) hx' (by unfold t; positivity [loc_pos E]) hz
    have he:=bandsT o v x s t hs (ht.order (by omega : B.order ≤ B.order+ m+1)); rw [show s*t=loc E*h from (by unfold t; field_simp)] at he; exact he
end
end YM.Trace.Wicket
