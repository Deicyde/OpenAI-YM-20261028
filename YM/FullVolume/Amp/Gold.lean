import YM.FullVolume.Amp.Sieve
import Mathlib.Analysis.Normed.Module.DoubleDual
/-! Standard complexification envelope, strong. Any real linear probe into complex payload.Vital analytic.At. UV after later. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp
open Filter Function Ray Set
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable (X Y : Type*) [NormedAddCommGroup X][NormedSpace ℝ X]
variable [NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y] [NormedSpace ℂ Y] [IsScalarTower ℝ ℂ Y]
-- Store complex values in real bidual envelope, isometric norm.Compare.Output actually has series with coefficients in X. Complex analytic notion thereby not weakening to weak testing.
abbrev hullB := (X →L[ℝ] ℝ) →L[ℝ] ℂ
-- isometry
def golden : X →L[ℝ] hullB X := (ContinuousLinearMap.compL ℝ (StrongDual ℝ X) ℝ ℂ Complex.ofRealCLM).comp (NormedSpace.inclusionInDoubleDual ℝ X)
lemma measureN (x:X): ‖golden X x‖= ‖x‖:=by
  let f:= NormedSpace.inclusionInDoubleDualLi ℝ (E:=X)
  let g:= golden X x; have hx u: ‖g u‖= ‖f x u‖:= Complex.norm_real _
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro u; exact (hx u).trans_le (((f x).le_opNorm _).trans_eq (by rw [LinearIsometry.norm_map]))
  rw [← f.norm_map x]; exact ContinuousLinearMap.opNorm_le_bound (f x) (norm_nonneg g) fun u=> (hx u).symm.trans_le (g.le_opNorm u)
variable {X Y}
section lift
variable (f:X→L[ℝ] Y)(x: Beam X)
def shine (z:ℂ): Y:=∑' i:ℕ,z^i • f (x i)
def diagram (i:ℕ): ℂ [×i]→L[ℂ] Y:= ContinuousMultilinearMap.piFieldEquiv ℂ (Fin i) Y (f (x i))
lemma diaN (i): ‖diagram f x i‖ = ‖f (x i)‖ := LinearIsometryEquiv.norm_map _ _
lemma diaY (i)(z:ℂ): diagram f x i (fun _=>z)= z^i • f (x i):=by change (∏ i:Fin i,z) • f (x i) =_; simp
variable [CompleteSpace X]
include f x
lemma opening (s:sun): shine f x s.val=f (Beam.read X s x):= by
  have ht:= f.hasSum (x.spar (abs_le.mpr s.2)); apply Eq.trans _ ht.tsum_eq; unfold shine; apply tsum_congr; intro i; rw [map_smul,←Complex.ofReal_pow]; exact IsScalarTower.algebraMap_smul ℂ (s.val^i) (f (x i))
lemma hol (z:ℂ)(hz:‖z‖<1): AnalyticAt ℂ (shine f x) z:=by
   let P:FormalMultilinearSeries ℂ ℂ Y:=diagram f x
   rw [show shine f x=P.sum from (by unfold P FormalMultilinearSeries.sum shine; simp_rw [diaY])]; have hv:Summable (fun i=> ‖P i‖):=by simp_rw [P,diaN]; exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>f.le_opNorm (x i)) ((paid x).summable.mul_left ‖f‖)
   have hb:=P.le_radius_of_summable_norm (r:=(1:ℝ≥0)) (by simpa using hv); simp only [ENNReal.coe_one] at hb
   apply (P.hasFPowerSeriesOnBall (zero_lt_one.trans_le hb)).analyticOnNhd _
   apply mem_eball_zero_iff.mpr; refine lt_of_lt_of_le ?_ hb; exact ENNReal.coe_lt_coe.mpr (show ‖z‖₊ < 1 from NNReal.coe_lt_coe.mp hz)
end lift
end YM.FullVolume.Amp
