import YM.UVExtension.Yard.Allowance
import Mathlib.Analysis.PSeries
import YM.UVExtension.Oriel.Gate

/-! # Normalized kinetic cylinder. The extra initial-bar or delay request
    (includes *every* subsequent StepStages horizon, no late truncation dependence).
    We can work around the path-only predicted center; this both handles the
    boundary shooting and keeps all centers a fixed prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Camp
open Function Set Filter RG Lattice Wilson Precision
open Lamppost AnalyticBridge VerifiedReset Collection
open Oriel
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}

-- max in roll, paths on real.
abbrev rad : ℝ:= Oriel.rim/4
abbrev soft : ℝ:= Oriel.rim/8
def worth (T:Levels G)(m:ℕ):= Yard.rake (T.clock.hatBeta m)
def pulse (T:Levels G)(m:ℕ):= stretchB (T.clock.hatBeta m)
def budget (T:Levels G)(m:ℕ):= worth T m / pulse T m

def Fees (T:Levels G) : Prop:= SumBudget (fun i:ℕ=> budget T (i+1)) (soft/4)
lemma pulse_pos (T:Levels G)(m:ℕ): 0 < pulse T m:= Real.rpow_pos_of_pos (zero_lt_one.trans (T.fits.delayed _)) _
lemma worth_pos (T:Levels G)(m:ℕ):0 < worth T m:= Real.rpow_pos_of_pos (zero_lt_one.trans (T.fits.delayed _)) _
lemma pulse_falls (T:Levels G)(m:ℕ): pulse T m ≤ T.clock.hatBeta m:= by unfold pulse stretchB; exact (Real.rpow_le_rpow_of_exponent_le (T.fits.delayed m).le (by norm_num : 98/100 ≤ (1:ℝ))).trans_eq (Real.rpow_one _)
lemma ready (_T:Levels G):0 ≤ rad∧ 0< soft∧ (soft/2<rad∧rad<Oriel.rim):=by norm_num [rad,soft,Oriel.rim]
-- slope, stone
private lemma stone (T:Levels G) (i:ℕ) : (Real.log 3) ≤ Real.log (T.S.block i).val:= Real.log_le_log (by norm_num) (by exact_mod_cast (T.S.block_large i))
lemma logs_pos (T:Levels G)(i:ℕ): 0< Real.log (T.S.block i).val:= (Real.log_pos (by norm_num : (1:ℝ)<3)).trans_le (stone T i)
lemma pulse_mono (T:Levels G)(h:G.Simple): Monotone (pulse T) := monotone_nat_of_le_succ (fun i=> by
  apply Real.rpow_le_rpow (zero_lt_one.trans (T.fits.delayed _)|>.le) _ (by norm_num: 0≤(98/100:ℝ)); unfold Calendar.hatBeta; rw [Schedule.scale_succ,mul_add,← add_assoc]; exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos h).le (logs_pos T i).le))
private def expense (w v:ℝ)(i:ℕ):= (v+w*((i+1:ℕ):ℝ)) ^ (-(106/100):ℝ)
lemma delayed (G: Gauge)(hg:G.Simple):∀ᶠ v in atTop,∀ T:Levels G, v ≤ T.clock.bar → Fees T:=by
  let w:= G.slopeConstant * Real.log 3; have hw:0<w:= mul_pos (Gauge.slopeConstant_pos hg) (Real.log_pos (by norm_num))
  let f := expense w 0; let ζ:ℝ:= 106/100; have hz:0< ζ:=by norm_num [ζ]
  have hx: Summable f:= by
    have h: Summable (fun i:ℕ=> ((i:ℕ):ℝ)^ (-ζ)):= Real.summable_nat_rpow.mpr (by norm_num [ζ])
    apply (((summable_nat_add_iff 1).2 h).mul_left (w ^ (-ζ))).congr
    intro i; dsimp only [f,expense]; rw [zero_add,Real.mul_rpow hw.le (by positivity)]
  have hf: Tendsto (fun v=> ∑' i:ℕ, expense w v i) atTop (𝓝 0):= by
    have h := tendsto_tsum_of_dominated_convergence (g:=fun _ :ℕ=> (0:ℝ)) (f:=fun v:ℝ=> expense w v) hx (fun i=> (tendsto_rpow_neg_atTop hz).comp (tendsto_id.atTop_add (tendsto_const_nhds (x:=w*((i+1:ℕ):ℝ))))) (show ∀ᶠ v:ℝ in atTop,∀ i, ‖expense w v i‖≤ f i from ?_)
    · simpa only [tsum_zero] using h
    filter_upwards [eventually_ge_atTop (0:ℝ)] with v hv i; have hi:0<w*((i+1:ℕ):ℝ):= by positivity
    unfold expense; rw [Real.norm_of_nonneg (Real.rpow_nonneg (add_nonneg hv hi.le) _)]; apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hz.le)
    linarith
  filter_upwards [hf.eventually (gt_mem_nhds (by norm_num [soft,Oriel.rim]: (0:ℝ)< soft/4)),eventually_ge_atTop (0:ℝ)] with v hv hp T hQ
  have hS(i:ℕ): v+w*(i:ℝ) ≤ T.clock.hatBeta i:= by
    induction i with
    | zero=> simpa [Calendar.hatBeta] using hQ
    | succ i ih=>
       have hx := stone T i; calc
         _=v+w*(i:ℝ)+w:= by push_cast; ring
         _ ≤ T.clock.hatBeta i+G.slopeConstant*Real.log (T.S.block i).val:= add_le_add ih (mul_le_mul_of_nonneg_left hx (Gauge.slopeConstant_pos hg).le)
         _ = _:= by unfold Calendar.hatBeta; rw [Schedule.scale_succ, mul_add, add_assoc]
  have he i: budget T (i+1) ≤ expense w v i:= by
     have hx:= zero_lt_one.trans (T.fits.delayed (i+1)); unfold budget worth pulse stretchB Yard.rake
     rw [← Real.rpow_sub hx,show (-(8/100)-98/100:ℝ)= -ζ by norm_num [ζ]]; exact Real.rpow_le_rpow_of_nonpos (by positivity) (hS (i+1)) (neg_nonpos.mpr hz.le)
  have hp' i:0≤ expense w v i:=by unfold expense; positivity
  have hs : Summable (expense w v):= by refine Summable.of_nonneg_of_le hp' ?_ hx; intro i; exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (neg_nonpos.mpr hz.le)
  have hV i: 0≤ budget T (i+1):= div_nonneg (worth_pos ..|>.le) (pulse_pos ..|>.le); have hY:=Summable.of_nonneg_of_le hV he hs
  exact ⟨hV,hY,(hY.tsum_le_tsum he hs).trans hv.le⟩
end YM.UVExtension.Camp
