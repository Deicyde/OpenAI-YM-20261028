import YM.Work.F05.Graphs
import YM.Work.F05.Jacobian



/-!
# F05 answer

Cancel additive Hessian change with change of the product of
relative chart ratios (probability Haar scales already agree). All
comparisons real germs for the given step data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F05
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

private lemma cancellation (L A B d j k : ℝ)
    (h : A = d^2*B) (hb : 0<B) (hg : j = |d| * k) (hj : 0 < j) (hk : 0 < k) :
    L + (1/2) * Real.log A - Real.log j = L + (1/2)*Real.log B - Real.log k := by
  have hd : |d| ≠ 0 := by intro he; rw [hg, he, zero_mul] at hj; exact lt_irrefl _ hj
  rw [h, ← sq_abs, Real.log_mul (pow_ne_zero _ hd) hb.ne', hg, Real.log_mul hd hk.ne',
    pow_two, Real.log_mul hd hd]
  ring

section
variable {c f : Side} {G : Gauge} {S : StepData c f}
    {B T : Forest S.ratio} {p : Clip} {W : PathData G}
    {ρ : Bid.Dir G c → AxisChart G B} {u : Bid.Dir G c → AxisChart G T}
    {σ C Λ a b : ℝ} {P : ChartRatio G}

private lemma crit_toll (h : Critical B p W ρ) (hf : LocalRatio P) :
    ∀ᶠ x in 𝓝 0, 0 < toll B P (ρ x) := by
  have hi := h.2.1.continuousAt.tendsto
  rw [h.1] at hi
  filter_upwards [hi.eventually (parcel_zero B hf)] with y hy
  exact toll_pos B hf hy

/-- Use both actual graphs; no adjustment of measure scale required in
these interfaces. -/
lemma same_thermal (hs : S.patch.Branches S.kernel G) (h : W.Bounds p σ C Λ)
    (hB : Critical B p W ρ) (hT : Critical T p W u)
    (hb : 0<b) (hQ : PriceGap T p W b) (hf : LocalRatio P) (r : S.Choices) :
    thermal B r p W ρ P =ᶠ[𝓝 0] thermal T r p W u P := by
  let e := freeEquiv B T
  have hx := graph_switch hs h hB hT hb hQ r
  filter_upwards [hx,hessian_ratio hs h hB hT e hx r,hessian_pos hb hQ hT r,
    (crit_home hB).eventually (loop_switch B T h), (crit_home hB).eventually (toll_switch e hf),
    crit_toll hB hf,crit_toll hT hf] with x hh hk hd hl ht hv hw
  change switch B T x (ρ x)=u x at hh
  change Precision.loop W _ = Precision.loop W (lifting T (represent x) (switch B T x (ρ x))) at hl
  change toll B P (ρ x) = |(fderiv ℝ (move e x) (ρ x)).det| * toll T P (switch B T x (ρ x)) at ht
  rw [hh] at hl ht
  unfold thermal
  rw [← hl]
  exact cancellation _ _ _ _ _ _ hk hd ht hv hw
end

theorem answer : YM.Bid.F05 := by
  intro G c f S hS H T p W σ C Λ a b ρ u hp hH hT _ hb _ hQ P hP k
  refine ⟨?_, 0, ?_⟩
  · filter_upwards [graph_switch hS.1 hp hH hT hb hQ k,
      (crit_home hH).eventually (tested_switch H T hS.1 hp k)] with x he hw
    change switch H T x (ρ x) = u x at he
    exact hw.trans (congr_arg _ he)
  simpa only [add_zero] using! same_thermal hS.1 hp hH hT hb hQ hP k
end YM.Work.F05
