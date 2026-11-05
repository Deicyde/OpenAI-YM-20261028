import YM.Extension.UV.StartAnalytic
import YM.Extension.UV.CouplingScales
import YM.Extension.UV.Holo
/-! Budget comparisons along a fixed successful parameter segment using pot/kettle. Anchored
supremum cost, not uniform uncharged per-address assertions. These are on the *actual* startup
formula. Does not yet require or prove that an arbitrary chosen successful Wilson family retained
this deterministic top choice, nor prove compatibility with all later labels. -/
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Startup
open Set Filter Function Lattice Wilson RG RG.Supply Precision Input Tree Ovens Ovens.Pipes
open WilsonStartup Progress.DirectedRecipe Progress.DirectedRecipe.Rack Planned
open scoped Topology BigOperators
variable {G:Gauge} {a:Levels G}{H:Horizon a} {O:ChartRatio G} (k:Kin H O) (N p:ℕ) (x y B : ℝ)
local notation "b" => a.budget N
-- `b` here hard-mask budget scaled with hatted parameters, same through band segment.
local notation "u" => a.clock.hatBeta N

/-- Full input comparison in the narrower interval. -/
abbrev strictBand (a:Levels G) (N:ℕ):= Icc ((5:ℝ)/8*a.clock.hatBeta N) ((11:ℝ)/8*a.clock.hatBeta N)
lemma strict_is (a:Levels G) (N:ℕ): strictBand a N ⊆ RG.Shoot.band a N := fun y hy=> by
 have h:=a.fits.delayed N
 change y∈Icc _ _ at hy; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
lemma pays_min : u/2∈RG.Shoot.band a N:= by have h:=a.fits.delayed N; exact ⟨le_rfl,by linarith⟩

private lemma budget_scale {g:ℕ→ℝ} {v:ℝ} (h:SumBudget g v) {c:ℝ} (hc:0≤c):
    SumBudget (fun i=>c*g i) (c*v):= ⟨fun i=> mul_nonneg hc (h.1 i),h.2.1.mul_left _,by rw [tsum_mul_left]; gcongr; exact h.2.2⟩
variable (hX: Port.AtTop k) (he:Start.Allows a N) (hx:x∈strictBand a N) (hy:y∈strictBand a N)
include hX he
lemma start_E_budget: ∃ v:ℕ→ℝ,
    (∀ i, BudgetPoint.supBounds (a.budget N) (((canonical k N p x).activities.reg i).site) ((canonical k N p x).activities.reg i).support (((canonical k N p x).activities.E i) - ((canonical k N p y).activities.E i)) (v i)) ∧
     ∀ x' : Site _, SumBudget (fun i => if ((canonical k N p x).activities.reg i).site=x' then BudgetPoint.mass (a.budget N) ((canonical k N p x).activities.reg i).support (v i) else 0) (|x-y|/(u/2)*(a.clock.allowance N)) := by
   let B:=u/2; let c:= (x-y)/B
   have hB := genuine_valid k N p hX he B (pays_min (a:=a) N)
   obtain ⟨g,hg,hB⟩:= hB.boundE
   have ht : 0<u:=zero_lt_one.trans (a.fits.delayed _)
   have hc := contour_bound a N
   refine ⟨fun i=> ‖c‖*(g i),fun i=>?_,fun x₁=>?_⟩
   · rw [E_diff_real k _ _ _ _ B (by positivity)]
     exact Start.times_bound c (hg i)
   · have heq i : (if ((canonical k N p x).activities.reg i).site=x₁ then BudgetPoint.mass (a.budget N) ((canonical k N p x).activities.reg i).support (‖c‖ * g i) else 0) = ‖c‖ * (if ((canonical k N p B).activities.reg i).site=x₁ then BudgetPoint.mass (a.budget N) ((canonical k N p B).activities.reg i).support (g i) else 0) := by
         change (if ((canonical k N p B).activities.reg i).site=x₁ then BudgetPoint.mass _ ((canonical k N p B).activities.reg i).support _ else _) = _
         split_ifs <;> simp [BudgetPoint.mass]; ring -- adjust shadowing x param
     simp_rw [heq]
     have hl := budget_scale (hB x₁) (norm_nonneg c)
     rw [Real.norm_eq_abs,show |c| = |x-y|/(u/2) from by dsimp [c,B]; rw [abs_div,abs_of_pos (by positivity : 0<u/2)]] at hl ⊢; exact hl

omit hX in
lemma individual_disc {z : ℝ} (hz : z∈strictBand a N) i U q (hq:q ∈ Metric.ball (z:ℂ) (u/8)): ‖embodiedK a N p q i U‖ ≤ |(canonical k N p (u/2)).activities.K i U| := by
  have hd := (Complex.abs_re_le_norm _).trans_lt (show ‖q-(z:ℂ)‖ < u/8 by rw [← dist_eq_norm]; exact ((Metric.mem_ball).1 hq))
  have hh := K_norm_compare k N p (u/2) q i U he.clip
  apply hh
  rw [Complex.sub_re,Complex.ofReal_re] at hd; linarith [(abs_lt.mp hd).1,hz.1]
include hx hy
lemma start_K_budget : ∃ v:ℕ→ℝ,
    (∀ i U', ‖embodiedK a N p (x:ℂ) i U'-embodiedK a N p (y:ℂ) i U'‖ ≤ v i) ∧
    ∀ x':Site _, SumBudget (fun i=>if x'∈((canonical k N p x).activities.forced i).support then BudgetPoint.mass (a.budget N) ((canonical k N p x).activities.forced i).support (v i) else 0) ((|x-y|/(u/8))*a.clock.forcedAllowance N):= by
  let B := u/2
  have hB:= genuine_valid k N p hX he B (pays_min (a:=a) N)
  let c:= |x-y|/(u/8)
  obtain ⟨g,hg,hB⟩:=hB.boundK
  have ht : 0<u:=zero_lt_one.trans (a.fits.delayed _)
  refine ⟨fun i=>c*g i,fun i U=>?_,fun x'=>?_⟩
  · let f(z:ℂ):=embodiedK a N p z i U
    let X := Complex.ofReal '' strictBand a N
    have hConv : Convex ℝ X:= (convex_Icc ..).linear_image (Complex.ofRealCLM:ℝ→L[ℝ]ℂ).toLinearMap
    have hf := K_entire_piece (G:=G) (a:=a) N p i U
    apply (diam_lipschitz (f:=f) (r:=u/8) (M:=g i) hConv _ _ _ (by positivity) _ ?_ _ ?_).trans_eq ?_ -- adjust implicit δ
    all_goals try exact fun _ _=> hf.differentiableOn
    all_goals try exact fun z hz=> hf.differentiableAt
    · rintro _ ⟨z,hz,rfl⟩ q hq
      exact (individual_disc k N p he hz i U q hq).trans ((Real.norm_eq_abs ..).symm▸ ((hg i).2 U))
    · exact mem_image_of_mem _ hx
    · exact mem_image_of_mem _ hy
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]; unfold c; ring
  · simp_rw [k_addresses k N p x B]
    have hbudget := budget_scale (hB x') (show 0≤c by positivity)
    convert hbudget using 2
    rename_i i
    rw [BudgetPoint.mass, mul_ite,mul_zero]
    split_ifs <;> (unfold BudgetPoint.mass at *; try ring)
end YM.Extension.UV.Startup
