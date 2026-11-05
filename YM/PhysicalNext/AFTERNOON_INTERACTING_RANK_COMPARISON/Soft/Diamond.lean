import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Nuance
import YM.Progress.CLASSICAL_KIN_RECURSION.Delta
/-!
# Actual Holdings on the Aux plate

Escalated: adapt Stocks.yield to a run-length-dependent investment
in the extra Perturbed Plate on this P. No claim of full Lawful.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Packets Display Display.Sew Pump Pump.Grid Pot Marker Milk Next.Rank.Tapes
    Local Next.SectorChange.Rows Gaussian Schur Wisps Next.Rank Next.Rank.Perch Next.Rank.Value Next.Rank.Flux Vale Display.Docking Next.Scheduling
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ENNReal
variable {c f : Side} {G : Gauge} {S : StepData c f} {D : Patch} {x W v l t q K r a s γ e ξ β y o c' δ L L' : ℝ}

lemma weathered (i : Purse) (D : Patch) (G : Gauge) (K : ℝ) (hk : 0<K) (ε α : ℝ) (he :0<ε) (ha : 0<α) (hv : 2*i.era.coast.a ≤ α/4) : ∀ᶠ s in atTop,
     Escalates i D.L s → ∀ n ≤ stretch D.L.val i.band s,∀ x ∈Set.Icc (s/2) s,∀ {c f : Side} (S : StepData c f), S.patch=D → ∀ (v : Dyed G S) (P : Teller G) (W : ℝ) (M : Plate v (retime x) W) (H : Draft v P (retime x) W),
      let u:=retime x; let y:=betaF G x D.L; let t:=acres i x y; let q:= ε*fiery G u S.patch.L/coupling v.source.beta
      let e:=ucap (load i.era+1)+1
      y/2≤ v.source.beta → v.bp.B=walls x → Pupil v u W q K →
      (∀ p j, Matched p → M.base j p ≤ -(α*hot y^2)*(j:Core S u).val.shares) →
      (∃ f:Glade c→ℝ,(∀ i,0≤f i) ∧ Ac.Hit (fun i: Glade c=> i.val) v.bp.B f (e+1) (6*weather s n) ∧ ∀ i p, Matched p → |Real.exp ((M:Plate v (retime x) W).aux i p)-1| ≤ f i) →
      ∀ R:Rep G c,∀ hp:R.p=v.bp, Holdings (L:=Vale.foliage H) R (fun j=> shiftZ (Orchard.canopy S) hp.symm (sprouting H M (Orchard.canopy S) j)) v.things t (Line i.era i.goal 0 s) (load i.era+1) (sailboat s n):= by
  let e:= ucap (load i.era+1)+1; have hE :0 ≤ e:=by unfold e ucap load; linarith only [i.spend]
  obtain ⟨a,hp⟩:= eventually_atTop.mp ((tall_limit.eventually (berry_keep D G (e+1) (by linarith only [hE]))).and ((tall_limit.eventually (bought_grain D.L (e+1) (by linarith only [hE]))).and ((cornfield G D α ha).and (coast_run G K hk ε he D))))
  obtain ⟨b,hb⟩:= eventually_atTop.mp (tall_limit.eventually_ge_atTop 1)
  filter_upwards [Wax.flint i D.L (G:=G) (show 0<α/4 by positivity) hv, risibleQ, Perch.half.eventually_ge_atTop a,Perch.half.eventually_ge_atTop b] with s ht hh hf hS hy n hN x hx c f S hZ v P W M H
  intro u y t q d hβ hs hQ hz hv R he; obtain ⟨N,hn,hM,H'⟩:=hv
  let J(i:Rung S u):=(u^(-(4:ℝ)))^(rips i).val.shares; let Z:= u^(-(2:ℝ)); have hb: 1≤u:= hb _ (hS.trans hx.1)
  have h₀:= hp _ (hf.trans hx.1);dsimp only at h₀
  have hX : coast G q K S.patch (retime x) ≤ Z:= by unfold q; rw [hZ]; exact h₀.2.2.2 v.source.beta hβ
  let O:= Orchard.canopy S
  let p:=sprouting H M O; let a':=u^(-(1/2):ℝ); let L:=Line i.era i.goal 0 s
  let V:= chargeStep S.patch Z J N
  have hB:= (hh v.bp x hs hx).1; have hμ : radiusB u≤ v.bp.B:= by change 25*radiusB u+30≤_ at hB; omega
  obtain ⟨hκ,h₀T,hl,hX1⟩ := hy.reserves n x v.bp hN hx hs
  have hv':a'≤garlic u:= by unfold a' garlic; exact Real.rpow_le_rpow_of_exponent_le hb (by norm_num)
  have hm i:0 ≤ J i:= by unfold J; positivity
  have hj : Ac.Hit scarf v.bp.B V (d+1) (8*weather s n):= by
    have ht₁:= coverPays (h₀.2.1 S (congr_arg Patch.L hZ).symm) hm hμ (by exact add_nonneg hE zero_le_one)
    have h2: Ac.Hit (spanFoot S u) v.bp.B (fun _=> Z*Jewels.attrition S.patch) (e+1) a':= by
      rw [hZ]; exact coverPays (h₀.1 S hZ) (fun _=> by have hz := Jewels.attrition_nn D; change 0≤Z*_; unfold Z; positivity) hμ (by linarith only [hE])
    intro i; exact budget_loosen (unionPay ht₁ (unionPay h2 hM) i) (by change a'+(a'+_)≤_; linarith only [hv',show garlic u≤ weather s n from hκ])
  have hA:p= sprouting H M O:=rfl
  have hp : ∀ j (r : Pilot G S u), Matched r→ t *|atomP W v M (Sum.inl j) r|≤ J j:= fun j r hr => h₀.2.2.1 S hZ v W M t (acres_one ..) (by rw [show α*hot y^2/4=α/4*hot y^2 by ring]; exact (le_max_left ..).trans (ht x hx)) H.enrolled.produced.branched r j (hz r _ hr)
  obtain ⟨f',H1,H2⟩:= grants H M O J N hm hn hp (acres_one ..) (show 1≤ L from le_max_left ..) H' hQ hX hj hE hl
  constructor
  have hh (P : BudgetPoint) (he:P=v.bp): (∀ i,Zest.Wares (shiftZ _ he.symm (p i)) v.things t L (f' i)) ∧ Hits (fun i=> Zest.zone (shiftZ _ he.symm (p i))) f' P d (sailboat s n):= by
    subst P; exact ⟨H1,fun i=> (H2 i).trans hX1⟩
  exact ⟨_,(hh R.p he).1,(hh R.p he).2⟩
end YM.PhysicalNext.InteractingRank.Soft
