import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Stamen
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Tipping
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Waylay
/-!
# Thresholds just for after-one-plate kernel `Opaque` and its earnings
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Grid
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Packets Display Display.Sew Pot Marker Milk Next.Rank.Tapes
    Local Next.SectorChange.Rows Gaussian Schur Wisps Next.Rank Next.Rank.Perch Next.Rank.Value Next.Rank.Flux Vale Display.Docking Next.Scheduling
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ENNReal
variable {c f : Side} {G : Gauge} {S : StepData c f} {D : Patch} {x W v l t q K r a s γ e ξ β y o c' δ L L' : ℝ}

-- output uniform tests

def garlic (x : ℝ) := x^(-(1/48):ℝ)
lemma berry_keep (D : Patch) (G : Gauge) (e : ℝ) (he : 0≤e): ∀ᶠ x in atTop,∀ {c f : Side} (S : StepData c f),S.patch=D →
    Ac.Hit (spanFoot S x) (radiusB x) (fun _=> x^(-(2:ℝ))*Jewels.attrition D) e (x^(-(1/2):ℝ)):= by
  let K:=Jewels.attrition D
  filter_upwards [poly_hit (gauges D (G:=G)).le (Jewels.attrition_nn D) (show (1/2:ℝ)<2 by norm_num) he 321,
    eventually_gt_atTop (0:ℝ), Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x hx ht hv c f S h
  subst D
  refine hx (Fleck S) (toes S) (spanFoot S x) (fleck_notice S G) (fun i k hk=> ?_) _ (fun i=> ⟨mul_nonneg (Real.rpow_pos_of_pos ht _).le (Jewels.attrition_nn _),(mul_comm ..).le⟩)
  obtain ⟨j,hj,he⟩:=halo_spec.mp hk; exact halo_spec.mpr ⟨_,mem_singleton_self _, (separation_triangle _ j _).trans (by have h:= strides S i _ hj; omega)⟩

lemma audacious (i : Purse): ∀ᶠ s in atTop,∀ x∈Set.Icc (s/2) s,∀ b : BudgetPoint,b.B=walls x → Risible b.B (3*garlic (retime x)) ∧ Line i.era i.goal 0 s * (Real.exp (3*garlic (retime x))-1)≤ tinder i s:=by
  have hQ : (6:ℝ) ≤ i.goal:= by exact_mod_cast i.tolerance
  let k:ℝ:= i.goal-3; let m :ℝ:= (-(2*i.goal:ℝ)-10); let v:= m-k-1
  have hv : v < -1/8:= by unfold v m k; linarith only [hQ]
  obtain ⟨a,hA⟩:= eventually_atTop.mp burst_limit
  filter_upwards [risibleQ, Perch.half.eventually_ge_atTop a,Perch.half.eventually_gt_atTop 0,long_pay (-v) (1/48) (by norm_num), Paint.absorb v (-1/8) hv 12, Paint.absorb (k+v) m (show k+v < m by unfold v; linarith only) 6,(bill_hi (show (-1/8:ℝ)<0 by norm_num)).eventually (ge_mem_nhds zero_lt_one)] with s hp hX ho hf hx hY he x ht b hB
  have hs:= (hA x (hX.trans ht.1)).1; have ht':0 < x:= ho.trans_le ht.1
  let q:= garlic (retime x); let c:=3*q
  have hv : q ≤ bill v s:= (Real.rpow_le_rpow_of_nonpos ht' hs (show -(1/48:ℝ) ≤ 0 by norm_num)).trans (by
    simpa only [neg_neg] using hf x ht)
  have hc:0≤ c:= mul_nonneg (by norm_num) (Real.rpow_pos_of_pos (ht'.trans_le hs) _).le
  obtain ⟨-,hh,-⟩:=hp b x hB ht
  have hm: c ≤ kinetics s/4:= by change _≤ bill (-1/8) s/4; unfold c; linarith only [hv,hx]
  have hE:c ≤1:= by change kinetics _ ≤1 at he; linarith only [hm,he]
  refine ⟨⟨hc,(mul_le_mul_of_nonneg_left hm (by positivity)).trans hh.grain⟩,?_⟩
  have hh: Line i.era i.goal 0 s=bill k s:= by
    unfold Line fareP firstN Perch.bill; rw [mul_zero,zero_add,← Real.exp_sub,max_eq_right]; exact congr_arg Real.exp (by unfold k;ring)
    apply Real.one_le_exp; linarith only [mul_le_mul_of_nonneg_left hQ (boil_pos s),boil_pos s]
  have he : Real.exp c-1≤2*c:= by
    have he := Real.abs_exp_sub_one_le (x:=c) (by rw [abs_of_nonneg hc]; exact hE); rw [abs_of_nonneg hc] at he; exact (le_abs_self _).trans he
  have hu: Real.exp c-1≤ 6*bill v s:= le_trans he (by unfold c; linarith only [hv]); rw [hh]
  apply (mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le).trans; rw [mul_left_comm]; change 6*(bill k s * _) ≤ _; rw [Perch.overlap]; exact hY

-- Branch of holdings: on already-furnished Plate and estimates on the summands.
-- See Gush/Offers for concrete opacity compiler; does not supply history.
lemma yield (i : Purse) (D : Patch) (G : Gauge) (K : ℝ) (hk : 0<K) (ε α : ℝ) (he :0<ε) (ha : 0<α) (hv : 2*i.era.coast.a ≤ α/4) : ∀ᶠ s in atTop,
    ∀ x ∈Set.Icc (s/2) s,∀ {c f : Side} (S : StepData c f), S.patch=D → ∀ (v : Dyed G S) (P : Teller G) (W : ℝ) (M : Plate v (retime x) W) (H : Draft v P (retime x) W),
      let u:=retime x; let y:=betaF G x D.L; let t:=acres i x y; let q:= ε*fiery G u S.patch.L/coupling v.source.beta
      let e:=ucap (load i.era+1)+1
      y/2≤ v.source.beta → v.bp.B=walls x → Pupil v u W q K →
      (∀ p j, Matched p → M.base j p ≤ -(α*hot y^2)*(j:Core S u).val.shares) →
      (∃ f:Glade c→ℝ,(∀ i,0≤f i) ∧ Ac.Hit (fun i: Glade c=> i.val) v.bp.B f (e+1) (garlic u) ∧ ∀ i p, Matched p → |Real.exp ((M:Plate v (retime x) W).aux i p)-1| ≤ f i) →
      ∀ R:Rep G c,∀ hp:R.p=v.bp, Holdings (L:=Vale.foliage H) R (fun j=> shiftZ (Orchard.canopy S) hp.symm (sprouting H M (Orchard.canopy S) j)) v.things t (Line i.era i.goal 0 s) (load i.era+1) (tinder i s):= by
  let e:= ucap (load i.era+1)+1; have hE :0 ≤ e:=by unfold e ucap load; linarith only [i.spend]
  obtain ⟨a,hp⟩:= eventually_atTop.mp ((tall_limit.eventually (berry_keep D G (e+1) (by linarith only [hE]))).and ((tall_limit.eventually (bought_grain D.L (e+1) (by linarith only [hE]))).and ((cornfield G D α ha).and (coast_run G K hk ε he D))))
  obtain ⟨b,hb⟩:= eventually_atTop.mp (tall_limit.eventually_ge_atTop 1)
  filter_upwards [Wax.flint i D.L (G:=G) (show 0<α/4 by positivity) hv, risibleQ,audacious i, Perch.half.eventually_ge_atTop a,Perch.half.eventually_ge_atTop b] with s ht hh hy hf hS x hx c f S hZ v P W M H
  intro u y t q d hβ hs hQ hz hv R he; obtain ⟨N,hn,hM,H'⟩:=hv
  let J(i:Rung S u):=(u^(-(4:ℝ)))^(rips i).val.shares; let Z:= u^(-(2:ℝ)); have hb: 1≤u:= hb _ (hS.trans hx.1)
  have h₀:= hp _ (hf.trans hx.1);dsimp only at h₀
  have hX : coast G q K S.patch (retime x) ≤ Z:= by unfold q; rw [hZ]; exact h₀.2.2.2 v.source.beta hβ
  let O:= Orchard.canopy S
  let p:=sprouting H M O; let a':=u^(-(1/2):ℝ); let L:=Line i.era i.goal 0 s
  let V:= chargeStep S.patch Z J N
  have hB:= (hh v.bp x hs hx).1; have hμ : radiusB u≤ v.bp.B:= by change 25*radiusB u+30≤_ at hB; omega
  have hl := hy x hx v.bp hs
  have hv':a'≤garlic u:= by unfold a' garlic; exact Real.rpow_le_rpow_of_exponent_le hb (by norm_num)
  have hm i:0 ≤ J i:= by unfold J; positivity
  have hj : Ac.Hit scarf v.bp.B V (d+1) (3*garlic u):= by
    have ht₁:= coverPays (h₀.2.1 S (congr_arg Patch.L hZ).symm) hm hμ (by exact add_nonneg hE zero_le_one)
    have h2: Ac.Hit (spanFoot S u) v.bp.B (fun _=> Z*Jewels.attrition S.patch) (e+1) a':= by
      rw [hZ]; exact coverPays (h₀.1 S hZ) (fun _=> by have hz := Jewels.attrition_nn D; change 0≤Z*_; unfold Z; positivity) hμ (by linarith only [hE])
    intro i; exact budget_loosen (unionPay ht₁ (unionPay h2 hM) i) (by change a'+(a'+_)≤_; linarith only [hv'])
  have hA:p= sprouting H M O:=rfl
  have hp : ∀ j (r : Pilot G S u), Matched r→ t *|atomP W v M (Sum.inl j) r|≤ J j:= fun j r hr => h₀.2.2.1 S hZ v W M t (acres_one ..) (by rw [show α*hot y^2/4=α/4*hot y^2 by ring]; exact (le_max_left ..).trans (ht x hx)) H.enrolled.produced.branched r j (hz r _ hr)
  obtain ⟨f',H1,H2⟩:= grants H M O J N hm hn hp (acres_one ..) (show 1≤ L from le_max_left ..) H' hQ hX hj hE hl.1
  constructor
  have hh (P : BudgetPoint) (he:P=v.bp): (∀ i,Zest.Wares (shiftZ _ he.symm (p i)) v.things t L (f' i)) ∧ Hits (fun i=> Zest.zone (shiftZ _ he.symm (p i))) f' P d (tinder i s):= by
    subst P; exact ⟨H1,fun i=> (H2 i).trans hl.2⟩
  exact ⟨_,(hh R.p he).1,(hh R.p he).2⟩
end YM.PhysicalNext.InteractingRank.Pump.Grid
