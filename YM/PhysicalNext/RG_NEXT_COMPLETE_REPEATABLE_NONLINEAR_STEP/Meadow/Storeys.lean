import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Highway
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Equip
/-!
 # Extra-income in PURE IK and auxiliary flags. Hero appointments paid.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo Height
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {P:Teller G} (L:Side) {Q : ConnectedActivityE6.Target G P} {σ u : ℝ}
lemma extraHeight (X : ConnectedActivityE6.Target.Expense Q) (μ:ℝ) (_hp : 0 < μ) (j n:ℕ) (he : X.wanting≤ -(7/16:ℝ)) : ∀ᶠ x : ℝ in atTop,
    ∀ A i k, Armada Q L μ X.earn x i A j k → 0 ≤ A→
        collars G i x j n*(salary Q L μ A x j k*(1-1/2)⁻¹) ≤ betaF G x L^X.wanting →
          let D:= grow G L x; let y:= asset X
          (D^3)⁻¹*collars G y x j n*(D*salary Q L μ A x j k*(1-1/2)⁻¹) ≤ betaF G x L ^ (-(23/20):ℝ):= by
  let v:=grow G L; have hi:=asset_pos X
  have he' : Rate G L (-(9/8)) (fun x=> (v x^3)⁻¹) := by
    apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx
    unfold v grow; rw [show (9/8:ℝ)=3/8*3 by norm_num,Real.rpow_neg hx.le, Real.rpow_mul hx.le]; norm_num
  let Y:=asset X
  filter_upwards [((he'.mul_right (Real.exp Y)).mul ((Rate.power (G:=G) (L:=L) (a:=3/8)).mul (Rate.power (a:=X.wanting)))) (-(23/20):ℝ) (by linarith only [he]), Delay.shift_pos G L] with x hx hk A i k H ha hp D y
  apply le_trans _ ((le_abs_self _).trans hx)
  let p:=i⁻¹^(n*j) *((n*j).factorial:ℝ)
  have hi' := H.delta
  have ht:p≥0:=by unfold p; positivity
  have hh : 0 < salary Q L μ A x j k:= by unfold salary; have he:= H.earned; positivity
  have hv : 0 < v x:= Real.rpow_pos_of_pos hk _
  have hx : 0 < D:=hv
  have hG : collars G Y x j n ≤ Real.exp Y * collars G i x j n:= by
    unfold collars Reserves.polyPrice; rw [mul_left_comm (Real.exp Y)]
    apply mul_le_mul_of_nonneg_left
    · rw [mul_comm (Y⁻¹^(n*j)*↑(n*j).factorial)]
      refine mul_le_mul_of_nonneg_left ((le_trans (b:=p) ?_ (le_mul_of_one_le_right ht (Real.one_le_exp hi'.le)))) (Real.exp_nonneg _)
      unfold p; have he':i≤Y:=by unfold Y asset; linarith only [H.little]
      gcongr
    unfold shiftG; positivity
  let s:=salary Q L μ A x j k
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ (D^3)⁻¹)) (by unfold s; positivity : 0 ≤ D*s*(1-1/2)⁻¹)).trans
  calc _ = (D^3)⁻¹*Real.exp Y*(D*(collars G i x j n*(s*(1-1/2)⁻¹))) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hx.le) (by positivity)
lemma flights (G:Gauge) (L:Side) (X : Stage) (W : ℝ) (hw : 0 < W): ∀ᶠ t in atTop,∀ p:BudgetPoint,p.threshold ≤ 2*Pressure.fiery G t L→p.power=X.power→p.order=X.order→p.supportExponent=X.supportExponent→p.B= radiusB t→∀ β b Λ,|β| ≤ 2*betaF G t L→|b| ≤ W→ 0≤ Λ→ Λ ≤ ConnectedActivityE6.loopBill G L t →
    let u:=Song.octaveNeed G p X.clip X.width X.paths Λ β b
    u ≤ betaF G t L ^ (-(7/16):ℝ) ∧ Real.exp (-(X.width/4)*p.B)*u ≤ betaF G t L ^ (-(23/20):ℝ) ∧ preExponent p/p.B≤ X.width/4:= by
  obtain ⟨q,hq,h⟩:= spur G L X W hw
  have he : Rate G L (-2) (fun x=> Real.exp (-(X.width/4)*radiusB x)) := by
    refine (Rate.cutoff (G:=G) (L:=L) (a:=-2) (show 0<X.width/4 from div_pos X.width_pos (by norm_num))).compare (Eventually.of_forall fun x=>?_)
    rw [abs_of_nonneg (Real.exp_nonneg _),abs_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonpos_left (show (Pressure.Stores.till x:ℝ)≤radiusB x by exact_mod_cast Nat.div_le_self ..) (by have he:=X.width_pos; linarith)
  filter_upwards [h,(he.mul hq) (- (23/20)) (by norm_num), hq (-(7/16)) (by norm_num), (((tendsto_const_nhds (x:=X.supportExponent+3)).div_atTop (tendsto_natCast_atTop_atTop.comp YM.Work.E01.radiusB_tendsto)).eventually (gt_mem_nhds (show 0<X.width/4 from by have he:=X.width_pos; linarith)))] with x h ht hz hy p hV hp hx hX hB β b Λ ha hw hS hh u
  have hf : u≤ q x:= h p hp hx hX hV β b Λ ha hw hS hh -- implicit
  refine ⟨hf.trans ((le_abs_self _).trans hz),?_,?_⟩
  · rw [hB]; exact (mul_le_mul_of_nonneg_left hf (Real.exp_nonneg _)).trans ((le_abs_self _).trans ht)
  unfold preExponent; rw [hX,hB]; exact le_of_lt hy
end YM.PhysicalNext.Repeat.Meadow
