import YM.UVExtension.Crown.Train
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Camp
open Function Set Filter RG Lattice Wilson Precision
open Lamppost AnalyticBridge VerifiedReset Collection
open Oriel Oriel.Charted Push Push.AbsoluteSums Metric RG.Shoot Complex Finset
open scoped Topology ContDiff Matrix.Norms.Frobenius NNReal Classical
variable {G : Gauge} (h:G.Simple)(T:Levels G) (N:ℕ)(X:ℕ→Type)[∀ i,NormedAddCommGroup (X i)][∀ i,NormedSpace ℂ (X i)]
namespace Cart
variable (V:Cart T N X)(r:ℕ)(hr:r ≤ N)
set_option quotPrecheck false
local notation "c'"=> tally T N X V
local notation "Λp"=> fun i=>pulse T i
def paidF (T:Levels G)(i:ℕ):=(T.clock.hatBeta i) ^ (95/100:ℝ)
local notation "B"=> T.clock.hatBeta
include h
lemma strokeB (i:ℕ): 0 < B i ∧ B i + G.slopeConstant*Real.log 3 ≤ B (i+1) := by
    refine ⟨zero_lt_one.trans (T.fits.delayed i),?_⟩; have hv := Real.log_le_log (by norm_num : (0:ℝ)<3) (show (3:ℝ) ≤ (T.S.block i).val from (by exact_mod_cast T.S.block_large i)); unfold Calendar.hatBeta; rw [Schedule.scale_succ,mul_add,← add_assoc]; exact add_le_add_right (mul_le_mul_of_nonneg_left hv (Gauge.slopeConstant_pos h).le) _
lemma paid_pos i: 0<paidF T i:= Real.rpow_pos_of_pos (strokeB h T i).1 _
lemma paid_mono : Monotone (paidF T):= by
   refine monotone_nat_of_le_succ fun i=> Real.rpow_le_rpow (strokeB h T i|>.1.le) ?_ (by norm_num : 0≤ (95/100:ℝ)); exact (le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos h).le (Real.log_nonneg (by norm_num)))).trans (strokeB h T i|>.2)
lemma delayedB : ∃ m,0 < m ∧ ∀ i, m*((i+1:ℕ):ℝ) ≤ B (i+1):=by
   let m:= G.slopeConstant *Real.log 3; have hp:0< m:=mul_pos (Gauge.slopeConstant_pos h) (Real.log_pos (by norm_num)); refine ⟨m,hp,fun i=>?_⟩
   induction i with
   | zero=> simpa only [Nat.zero_add,Nat.cast_one,mul_one] using (show m ≤ _ from (le_add_of_nonneg_left (strokeB h T 0).1.le).trans (strokeB h T 0).2)
   | succ i ih=> apply le_trans _ ((strokeB h T (i+1)).2); push_cast at ih ⊢; change _ ≤ B _ + m; nlinarith only [ih]
lemma skiesC : Filter.Tendsto (T.clock.hatBeta) atTop atTop:=by
    obtain ⟨m,hm,hf⟩:= delayedB h T; rw [← tendsto_add_atTop_iff_nat 1]; exact tendsto_atTop_mono hf ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tendsto_add_atTop_nat 1)|>.const_mul_atTop hm)
lemma penny : ∃ Y:ℝ,0≤ Y∧∀ i:ℕ, ∑ j∈Finset.range i,worth T (j+1) ≤ Y*paidF T i:=by
    obtain ⟨m,hm,hM⟩:=delayedB h T
    let f(j:ℕ):= Camp.worth T (j+1)/paidF T (j+1); have hp j :0≤ f j:= div_nonneg (worth_pos T _|>.le) (paid_pos h T _|>.le)
    let r:ℝ:=-(103/100); have hV:Summable f:=by
       have hF: Summable (fun i:ℕ=>((i:ℕ):ℝ)^r):= Real.summable_nat_rpow.mpr (by norm_num [r]); apply Summable.of_nonneg_of_le hp _ (((summable_nat_add_iff 1).2 hF).mul_left (m^r))
       intro i; unfold f Camp.worth paidF Yard.rake; rw [←Real.rpow_sub (strokeB h T (i+1)|>.1), ← Real.mul_rpow hm.le (Nat.cast_nonneg _), show -(8/100:ℝ)-95/100 = r by unfold r; ring]; exact Real.rpow_le_rpow_of_nonpos (by positivity) (hM i) (by norm_num [r])
    refine ⟨∑' i,f i,tsum_nonneg hp,fun i=>?_⟩; let g j:= f j*paidF T i
    calc
      _ ≤ ∑ j∈Finset.range i,g j:= by
        refine Finset.sum_le_sum fun j hj=> ?_; have he:j+1≤ i:= Finset.mem_range.mp hj; apply le_trans _ (mul_le_mul_of_nonneg_left (paid_mono h T he) (hp j))
        unfold f; rw [div_mul_cancel₀ _ (paid_pos h T _|>.ne')]
      _ ≤ (∑' i,f i)*paidF T i:= by unfold g; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hV.sum_le_tsum _ (fun i _=> hp _)) (paid_pos h T i|>.le)
-- incur horizon-specific expenses. Gives global shrink cutoff s. Excludes small m handled with analytic neighborhood (imag).
lemma framed : ∀ᶠ i:ℕ in atTop, ∀ (N:ℕ), ∀ hi:i≤N, ∀ (X:ℕ→Type)[∀ j,NormedAddCommGroup (X j)][∀ j,NormedSpace ℂ (X j)] (V:Cart T N X) (hf:Fees T) (b:ℂ), b∈Broad T → ‖node N (picked h T N X V hf (b:=b)) i hi‖ ≤ (T.clock.hatBeta i) ^ (-(1/50:ℝ)) := by
   obtain ⟨A,hA,hV⟩:= penny h T; let K:= flatTime T; have he:∀ᶠ i:ℕ in atTop,K+A ≤ T.clock.hatBeta i ^ (1/100:ℝ) := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).comp (skiesC h T)).eventually_ge_atTop _
   filter_upwards [he] with i he N hi X _ _ V hf b hx
   let v:=picked h T N X V hf (b:=b); have hy:=laced h T N X V hf hx; let t:=(⟨i,Nat.lt_succ_of_le hi⟩:Fin (N+1)); let z:= v t
   have hp:z=(pulse T i:ℂ)⁻¹*(b-∑ j∈range i,V.tally T N X v j):=congr_fun hy.2.symm t
   change ‖z‖ ≤_; rw [hp,norm_mul, norm_inv,Complex.norm_real,Real.norm_of_nonneg (pulse_pos ..|>.le)]; apply (inv_mul_le_iff₀ (pulse_pos ..)).mpr; apply (norm_sub_le ..).trans
   have hK:‖b‖≤K*paidF T i:= (mem_ball_zero_iff.mp hx|>.le).trans (le_mul_of_one_le_right (flat_pos T|>.le) (Real.one_le_rpow (T.fits.delayed i|>.le) (by norm_num : 0≤ (95/100:ℝ))))
   refine (add_le_add hK ((norm_sum_le ..).trans ((sum_le_sum (fun j hj=> V.rates T N X hy.1 _ (lt_of_lt_of_le (Finset.mem_range.mp hj) hi))).trans (hV i)))).trans ((le_of_eq (add_mul ..).symm).trans ((mul_le_mul_of_nonneg_right he (paid_pos h T i|>.le)).trans_eq ?_))
   unfold paidF pulse stretchB; rw [← Real.rpow_add (strokeB h T i|>.1),←Real.rpow_add (strokeB h T i|>.1)]; ring_nf -- confirm
end Cart
end YM.UVExtension.Camp
