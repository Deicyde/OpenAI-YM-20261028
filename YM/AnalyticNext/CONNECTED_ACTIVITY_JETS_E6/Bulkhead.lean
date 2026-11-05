import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Powder

/-! # Uniform supremum costs for reinstated D occurrences.
Every multiplicity shares Y and labels *before* taking the amount's norm.
K-style weight on actual support. Includes coarse outgoing test. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees Multiple Letter OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C δ e : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {j b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W α μ L Q o C T R) (X : Coat T F) (hk : X.x=α) (he : X.width=o.K)

lemma regains (r : H.Chainbook) (ht : Ac.Spark H.bookFoot r.1) (hp : H.Fresh r) : OmitClusters.restores r := by
  obtain ⟨j,hj⟩:= ht.1; rcases j with j|j
  · exact ⟨j,hj⟩
  obtain ⟨o,ho,h⟩ := not_disjoint_iff.mp (hp.2.2 j (mem_toRight.mpr hj)); obtain ⟨v,hv,hb⟩ := mem_biUnion.mp ho
  exact ⟨v,mem_toLeft.mp hv⟩

def excels (j : ℕ) (p : H.Chainbook) := if H.Fresh p ∧ Ac.Spark H.bookFoot p.1 then manyW (grade H.seam (H.thinPay j) (H.broadPay j)) p else 0
lemma thick_pos (j : ℕ) (u : H.Chapter) : 0≤grade H.seam (H.thinPay j) (H.broadPay j) u := by
  rcases u with i | i
  · exact H.ours_pos ..
  exact clusters_nonneg _ (fun _=> H.ours_pos ..) _
lemma excels_nn (j : ℕ) (p : H.Chainbook) : 0≤ H.excels j p := by
  unfold excels; split
  next ht => apply Finset.prod_nonneg; intro i _; exact div_nonneg (pow_nonneg (H.thick_pos j _) _) (by positivity)
  exact le_rfl

include he hk

omit he hk
def armK (Q : YM.ConnectedActivityE6.Target G P) (L : Side) (μ x : ℝ) (m j : ℕ) := ((( (2:ℝ)^m)⁻¹*
      Real.exp (-Q.mark L μ x))*(Q.mergeScale L μ x j*(1-1/2)⁻¹))
variable (p : Renewed j a δ e H)
include p
lemma stocks (x : Site c) (m : ℕ) : SumBudget (fun r : H.Chainbook=> if OmitClusters.restores r ∧ m ≤ Multiple.card r then
      Trees.currency (radiusB α) a (H.library r)*Multiple.connected H.bookFoot x (grade H.seam (H.thinPay j) (H.broadPay j)) r else 0)
    (armK Q L μ α m j) := by
  let t:= Q.mark L μ α; let v:= Q.mergeScale L μ α j; let c₀:= Q.overture L μ α j; let d:= Q.quantum L μ α 0 j 1 0
  have hv : 0<c₀ := p.shift.1
  have hk' : d= c₀*Real.exp (-t) := by
    let h:= Q.quantum_form L μ α 0 j 1 0
    unfold d c₀ t; simpa only [Nat.cast_one,mul_one] using! h
  have hZ : Real.exp t*d = c₀ := by rw [hk',mul_left_comm,← Real.exp_add]; simp
  have ht : 0 < v := by unfold v Target.mergeScale; exact mul_pos (by norm_num) hv
  refine OmitClusters.restore H.seam H.smallAt H.largeAt _ _ (radiusB α) (fun _=> H.ours_pos _ _ _ _ _) (fun _=> H.ours_pos _ _ _ _ _)
    (fun i=> i.2.1) (fun i=> i.2.1) (by norm_num : (1:ℝ)≤2) (σ:=1/2) (by norm_num) (by norm_num)
    H.laws.acquired.marked p.full p.post H.testS p.shift p.marks ?_ ht p.paid p.tree (show (1:ℝ)/2<1 by norm_num) x m
  norm_num
  change _ + _ * (c₀ * _) ≤ 20*c₀
  change (2:ℝ)*Real.exp t*_ *d+_ *_ ≤ _; linarith
lemma bulkhead (m : ℕ) : Ac.Hit H.library (radiusB α) (fun p=> if m ≤ Multiple.card p then H.excels j p else 0) a (armK Q L μ α m j) := by
  intro x; refine budget_mono (H.stocks p x m) (fun i=> ?_) fun i=> ?_
  · split
    next => apply mul_nonneg _ (Real.exp_pos _).le; dsimp only; split <;> first | exact H.excels_nn .. | exact le_rfl
    exact le_rfl
  split
  next hi =>
    dsimp only; split
    next hz =>
      unfold excels; split
      next hv => rw [if_pos ⟨H.regains i hv.2 hv.1,hz⟩,Multiple.connected, if_pos ⟨hv.2,hi⟩]; exact (mul_comm ..).le
      rw [zero_mul]; exact (H.stocks p x m).1 _
    rw [zero_mul]; exact (H.stocks p x m).1 _
  exact (H.stocks p x m).1 _
omit p

-- Push mark buys ANY fixed pay of actual outgoing forced threshold at this x.
lemma dictionary_fit (Q : YM.ConnectedActivityE6.Target G P) (L : Side) (j m : ℕ) {μ A : ℝ} (hμ : 0 < μ) (hp : 0≤A) {δ : ℝ}
    (hd : 0≤δ) (he : δ<2) : ∀ᶠ x : ℝ in atTop, armK Q L μ x m j ≤ Real.exp (-A * (Vac.Numbers.P x)^δ) := by
  let B:= G.slopeConstant * Real.log L.val
  have hm (x : ℝ) (h : 1 ≤ Real.log (Real.log x)) (hz : 1<x) : Vac.Numbers.P x ≤ Delay.fineMonitor G L x := by
    unfold Delay.fineMonitor Vac.Numbers.P
    have hk : 0 < Real.log x := by
      exact Real.log_pos hz
    apply Real.exp_monotone; apply pow_le_pow_left₀ (zero_le_one.trans h); apply Real.log_le_log hk
    apply Real.log_le_log (zero_lt_one.trans hz) (le_add_of_nonneg_right (Work.E04.shift_nonneg G L))
  have hf := Delay.wins G L (half_pos hμ) (show (0:ℝ)<1/2 by norm_num) hp he 0
  have hz : Rate G L Q.rate (fun x=> ((2:ℝ)^m)⁻¹*(Q.mergeScale L μ x j*(1-1/2)⁻¹)) :=
    ((Q.tempo L hμ j).mul_right _).mul_left _
  filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.comp Real.tendsto_log_atTop|>.eventually_ge_atTop 1,
    hf,hz.below Q.stop 1 zero_lt_one] with x hx h ht ha
  have hg:= (le_abs_self _).trans ha
  have hv := Real.rpow_le_rpow (show 0≤Vac.Numbers.P x from (Real.exp_pos _).le) (hm x h hx) hd
  rw [pow_zero,mul_one] at ht; let M:= Q.mark L μ x
  change A*_ ≤ M / 16 at ht; have hh: 0 < M:= Delay.win_pos G L x (half_pos hμ) (show (0:ℝ)<1/2 by norm_num)
  unfold armK; rw [mul_comm ((2:ℝ)^m)⁻¹,mul_assoc]
  apply (mul_le_of_le_one_right (Real.exp_pos _).le hg).trans; apply Real.exp_monotone
  change - M ≤ - A*_; linarith [mul_le_mul_of_nonneg_left hv hp]
end YM.ConnectedActivityE6.Cash
