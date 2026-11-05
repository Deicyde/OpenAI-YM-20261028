import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Armada
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymSeason
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Solvent
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Hood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Trees March  Itinerary
variable (L) (Q)

def pledgeA (μ x : ℝ)(B : ℝ)(i j : ℕ):= (1+2^(i+2)*B)*(Q.overture L μ x j+2*((swing Q L μ 1 x 0).ceiling 0 j 0 0)) -- v.Tech

def pledgeX (μ x : ℝ)(n: ℕ):= Q.overture L μ x n+2*(swing Q L μ 1 x 0).ceiling 0 0 0 0
-- plus root geometric cost.Rate.T for μ; y dependent analytic probe.Assemble with +2 at post

def pledgeQ (μ x B : ℝ)(i j : ℕ):=10*(pledgeA L Q μ x B i j+pledgeX L Q μ x j)

def tailCost (μ x B e : ℝ)(b j i : ℕ):= (B*collars G e x b i*((swing Q L μ 1 x 0).ceiling 1 j 0 0)+collars G e x b i*(pledgeA L Q μ x B b j*sailUp Q L x*(1-sailUp Q L x)⁻¹))/Q.goal L x

def poster (Q : YM.ConnectedActivityE6.Target G P)(L:Side)(x:ℝ):= betaF G x L ^ (Q.rate/4)
section
variable (hm:0<μ)
include hm
lemma strides (k : ℕ) : Rate G L Q.rate (fun x=> (swing Q L μ 1 x 0).ceiling 0 k 0 0)∧ Rate G L (Q.rate+Q.rate/2) (fun x=> (swing Q L μ 1 x 0).ceiling 1 k 0 0)∧ Rate G L 0 (fun x=> (1-sailUp Q L x)⁻¹):=by
  let V x:= sailUp Q L x; have hg : Q.rate/2 < 0:= by linarith [Q.stop]
  have hh: Rate G L (Q.rate/2) V:=Rate.power
  have hp: Rate G L Q.rate (fun x=> (swing Q L μ 1 x 0).rootHit):=(Q.rate_root (C:=0) (β:=1) L hm).add (Rate.power.mul_right _)
  have ht:Rate G L 0 (fun x=> (1-V x)⁻¹):=by
    refine (Rate.const 2).compare ?_
    filter_upwards [hh.below hg _ (by norm_num: (0:ℝ) < 1/2)] with x hx
    have he: 1/2 ≤ 1-V x:=by linarith [le_abs_self (V x)]
    rw [abs_of_nonneg (inv_nonneg.mpr (le_trans (by norm_num) he)), abs_of_nonneg (by norm_num: (0:ℝ) ≤ 2)]
    exact (inv_anti₀ (by norm_num : (0:ℝ)<1/2) he).trans_eq (by norm_num)
  unfold Mixed.Costs.ceiling; simp only [Reserves.treeYield,Nat.cast_zero,mul_zero,pow_zero,pow_one,mul_one]
  exact ⟨by simpa only [add_zero,swing] using! ((hp.mul ht).mul_left (Reserves.extract Q.ε k 0 0)),by simpa only [add_zero,swing] using! (((hp.mul hh).mul ht).mul_left (Reserves.extract Q.ε k 0 0)),ht⟩
lemma scaleHome (b j : ℕ){B:ℝ→ℝ}(hb:Rate G L 0 B) : Rate G L Q.rate (fun x=>pledgeA L Q μ x (B x) b j)∧ Rate G L Q.rate (fun x=> pledgeQ L Q μ x (B x) b j):=by
  have h:=Q.rate_none L hm 0 j 0
  have hp:Rate G L Q.rate (fun x=>pledgeA L Q μ x (B x) b j):=by
    simpa only [zero_add] using! (((Rate.const 1).add (hb.mul_left (2^(b+2):ℝ))).mul
      (h.add ((strides L Q hm j).1.mul_left 2)))
  exact ⟨hp,(hp.add (h.add ((strides L Q hm 0).1.mul_left 2))).mul_left 10⟩
lemma burden (b j i : ℕ) (e : ℝ) {B : ℝ→ℝ} (hb : Rate G L 0 B) : Rate G L (Q.rate/2) (fun x=> tailCost L Q μ x (B x) e b j i):=by
  obtain ⟨hK,ht,hv⟩:=strides L Q hm j
  have he : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
  have hp : Rate G L 0 (fun x=>collars G e x b i):=by simpa only [zero_mul] using! ((he.pow (i*b)).mul_right (Reserves.polyPrice e (i*b)))
  have hz : Rate G L (-Q.rate) (fun x=>(Q.goal L x)⁻¹):=by
    apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx; rw [Real.rpow_neg hx.le]; rfl
  have hM := (scaleHome L Q hm b j hb).1; unfold tailCost; simp_rw [div_eq_mul_inv];
  have ha := (((hb.mul hp).mul ht)).congr (EventuallyEq.rfl); simp only [zero_add] at ha
  have hy:= hp.mul ((hM.mul (show Rate G L (Q.rate/2) _ from (Rate.power (G:=G) (L:=L) (a:=Q.rate/2)))).mul hv); rw [zero_add,add_zero] at hy
  convert! (ha.add hy).mul hz using 1; ring

-- `Plating`; price coupling schedule.
structure Bikes (Q : YM.ConnectedActivityE6.Target G P)(L : Side)(μ x v e B: ℝ)(j k:ℕ) : Prop where
  rev : ∀ (β C:ℝ), (Q.costs L μ β x C).Buy L Q.halo (radiusB x)→ (swing Q L μ β x C).Buy L Q.halo (radiusB x)
  covers : radiusB (betaF G x L) ≤ 2*(radiusB x)
  win : v+e+e ≤ Q.exp
  push : degreePrice (radiusB x) (pledgeA L Q μ x B j k) e ≤ sailUp Q L x
  heat : degreePrice (radiusB x) (pledgeQ L Q μ x B j k) e ≤ 1/2
  within : sailUp Q L x ≤ 1/2
  posts : 0 ≤ v
  allow : 0 < e
  paid : 0 < betaF G x L
  gains : pledgeQ L Q μ x B j k≤ 1/2
lemma stables {v e:ℝ}(B:ℝ→ℝ)(he:0<e)(hr:v+e+e ≤ Q.exp)(hv:0 ≤ v)(hp:Rate G L 0 B)(j i n : ℕ) : ∀ᶠ x in atTop,Bikes Q L μ x v e (B x) j i∧ tailCost L Q μ x (B x) e j i n ≤ poster Q L x:=by
  have ht R (h : Rate G L Q.rate R):Rate G L Q.rate (fun x=>degreePrice (radiusB x) (R x) e):=by
    unfold degreePrice Trees.stretch; simp_rw [div_eq_mul_inv]; have he:= Census.width_rate G L 1 0; simp only [one_mul, add_zero] at he; simpa only [zero_add] using! (((he.mul h).mul_right e⁻¹).mul_left 4)
  obtain ⟨hA,hB⟩:= scaleHome L Q hm j i hp
  have h:=Q.stop; have hh:= Q.grants
  have hN:= AbsoluteSums.Fees.horizons G L 0 (ε:=Q.ε) Q.usable (le_refl 0) (show 2*Q.ε < P.top.supportExponent from by linarith [hh.1,Q.usable])
  filter_upwards [sailsW (L:=L) Q hm, hN, (ht _ hA) (Q.rate/2) (by linarith), (ht _ hB).below h _ (by norm_num: (0:ℝ)<1/2),Delay.shift_pos G L,
    Rate.power.below (G:=G) (L:=L) (show Q.rate/2<0 by linarith) _ (by norm_num: (0:ℝ)<1/2), hB.below h _ (by norm_num:(0:ℝ)<1/2),burden L Q hm j i n e hp (Q.rate/4) (by linarith)] with x hM hz hA hB hx hp hr hu
  exact ⟨⟨hM,hz.2.1, (show v+e+e ≤ Q.exp from by assumption),(le_abs_self _).trans hA,(le_abs_self _).trans hB,(le_abs_self _).trans hp,(by assumption),he,hx,(le_abs_self _).trans hr⟩,(le_abs_self _).trans hu⟩
end
end YM.PhysicalNext.Repeat.Daisy
