import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Agreements
import YM.Extra.ITERATION_NO_LOSS.Mechanism
import YM.Extra.MULTISOURCE_TRAJECTORIES.Service
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Growth
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Symbol
import YM.Further.FREE_COVARIANCE_KP.KP.Gem
import YM.Next.MAXWELL.Studio
import YM.Next.RANK.Flux.Chronicle
import YM.Next.RANK.Prepaid
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Arc.Audit
import YM.Push.GRID_APPROXIMATION.Roll
import YM.Push.LOCAL_SPLITTING.Direct
import YM.Push.PRICE_COMPILER.Builders
import YM.UVNext.PRICED_KERNELS.Crews


/-! # Tag with the actual `Light` family, before displays. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph Marker Value Flux
      MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
     
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {V ι κ : Type} [Fintype V] [DecidableEq V] [Fintype ι] [Fintype κ] {θ : V→Site f}
section Dust
variable (R : Rep G f) (H : ι → SourceAt G θ) (K : κ → Lifted G θ R.p.threshold) {σ C Λ δ w : ℝ}
lemma dust_gauge (hp : R.Lawful σ C Λ δ w) : GaugeInvariant (Value.dust R H K) := by
  intro t U
  have he : GaugeInvariant R.exponent := YM.Push.Local.Kernel.exp_invariant hp
  have hh (i : ι) : (H i).amount R.p.threshold (gauge t U)=(H i).amount R.p.threshold U:= congr_arg (Poly.send (H i).fires)
    (YM.Push.Local.Kernel.mask_gauge _ _ (H i).inv t U)
  have hy (i : Finset κ): Lifted.pack K i (gauge t U)=Lifted.pack K i U:= by
    unfold Lifted.pack Lifted.gather Lifted.amount
    simp only [fun i=>(K i).inv t U,gauge_flags]; congr!
  simp_rw [Value.dust,he t U,hh, hy]
lemma send_continuous (y : modes V) : Continuous (Poly.send y) := by
  change Continuous (fun p : ℂ => (Poly.send y p).part); apply continuous_pi; intro i
  simp_rw [Poly.part_send]; split <;> first |exact continuous_id|exact continuous_const
lemma dust_measible (hp : R.Lawful σ C Λ δ w) : Measurable (Value.dust R H K) := by
  have he := (R.exponentEnv hp).meas
  have hh (i : ι) : Measurable ((H i).amount R.p.threshold):= (send_continuous _).measurable.comp (masked_measurable _ _ _ (H i).meas)
  have hv (i : Finset κ) : Measurable (Lifted.pack K i) := by
    have hf j : Measurable ((K j).amount) := (send_continuous _).measurable.comp (K j).meas
    have hz := Finset.measurable_fun_prod i (f:= fun j=> (K j).amount) fun j _=>hf j
    unfold Lifted.pack
    refine Measurable.ite ?_ hz measurable_const
    unfold Lifted.gather
    by_cases e : (i:Set κ).PairwiseDisjoint fun i => (K i).extent
    · simp only [e,true_and]
      simp_rw [eq_comm]; exact flags_measurable_eq ..
    simp [e]
  apply ((Complex.continuous_ofReal.measurable).comp (Real.continuous_exp.measurable.comp he)).smul
    ((Poly.pass_cont.measurable.comp (Finset.measurable_fun_sum _ (fun i _=>hh i))).mul (Finset.measurable_fun_sum _ (fun i _=>hv i)))

/-- K compatibility on *every* U, nonzero or not. Integrable on actual
finite torus, including sums over all H alternatives at this period. -/
lemma dust_env {r : V → ℝ} {e l L} (hr : ∀ i, 0<r i) (he : 0≤e) (hp : R.Lawful σ C Λ δ w)
    (hH : Light R H K r e l L) (hK : Background R K) : Envelope (Value.dust R H K) := by
  have hm : Notice R θ (Value.dust R H K) r e l L:= ⟨ι,κ,inferInstance,inferInstance,H,K,rfl,hK,hH⟩
  obtain ⟨k,hk,h⟩ := Poly.equivalent_norm (R:=Stock.census V) hr
  obtain ⟨s,hs⟩ := (R.exponentEnv hp).cost
  refine ⟨dust_measible R H K hp,Real.exp (s+Fintype.card (Site f)*L+Fintype.card V*l)*k,fun U=>?_⟩
  exact (h _).trans ((mul_le_mul_of_nonneg_right ((hm.price hr he U).trans
      (Real.exp_monotone (add_le_add_left (add_le_add_left ((le_abs_self _).trans (hs U)) _) _))) hk))

end Dust
end YM.PhysicalNext.InteractingRank
