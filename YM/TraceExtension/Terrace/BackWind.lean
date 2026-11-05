import YM.TraceExtension.Terrace.Mortal
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price MergeProof.East Further.CorrectedLift Climb Analysis Work Weir
open Further.PhysicalPeriodLimitF933 Shunt PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells Pressure
open Relay Shepherd
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}(A:Levels G)(h:G.Simple)(θ:PostT A)(K:Stock.Tabs A)
def bountyW (P:Levels G)(j t:ℕ):= let k:=summit P j;Tau P j 1000000* (P.clock.hatBeta k)^(2*(t-j))
lemma stipend (A:Levels G)(j k:ℕ):1 ≤ bountyW A j k:= by
    unfold bountyW; exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (mul_nonneg (by norm_num) (gate_le _ (A.fits.delayed _)|>.le))) (one_le_pow₀ (le_of_lt (A.fits.delayed _)))
include h θ K
lemma rateD : ∀ᶠ j:ℕ in atTop, let k:=summit A j;let m:=basin A K j
    bountyW A j k ≤ Real.exp ((prism (A.clock.hatBeta k):ℝ)/32) ∧
    (∀ i:ℕ,j ≤ i→ i<k→ bountyW A j i ≤ renal A i * bountyW A j (i+1)) ∧ Real.exp ((A.S.a j/A.S.a m)^4 * Vac.treasury A m+4)/(bountyW A j m)^2 ≤ Tau A j (-1900000):=by
    filter_upwards [back_gate A h θ,( (Sstar A).eventually ((lrate A h).eventually_ge_atTop 1)), ( (hrate A h).comp (Sstar A)).eventually (hugeW 1000 (by norm_num)), (lrate A h).eventually_ge_atTop 4, liability A h θ K] with j hj ht hv hG hL k m
    let x:=A.clock.hatBeta j; let y:=A.clock.hatBeta k; have hx:= A.fits.delayed j; have hy:1≤y:=(le_of_lt (A.fits.delayed k)); have hy':0 < y:=zero_lt_one.trans_le hy; let a:= Lyra A j; let b:= Lyra A k
    have hb:1 ≤ b:=ht; have hu: a ≤ b:= lypos A h (stellar ..|>.le); have Ha:a≥ 4:=hG; let G0:= Gate x;let G1:= Gate y
    have hf:G0 ≤ G1:= pow_le_pow_left₀ (lira ..|>.le) hu _; have hQ : 1 ≤ G0:=one_le_pow₀ (le_trans (by norm_num : (1:ℝ)≤4) Ha)
    have hk :(↑(k-j):ℝ) ≤ 2*G0:= (bound_gap A (stellar ..|>.le)).trans hj
    have hφ: 1000* G1 * b ≤ (prism y :ℝ)/32:=hv
    have hZ: Tau A j 1000000 ≤ bountyW A j m:=by unfold bountyW; exact le_mul_of_one_le_right (Tau_pos ..|>.le) (one_le_pow₀ hy)
    constructor
    · change Real.exp _ * y^ (2*(k-j)) ≤ _; rw [show y^ (2*(k-j))= Real.exp ((↑(2*(k-j)):ℝ)*b) from (by rw [Real.exp_nat_mul]; unfold b Lyra; rw [Real.exp_log (show 0<A.clock.hatBeta k from hy')]),← Real.exp_add]; apply Real.exp_monotone
      push_cast; norm_num [Dust]; have hh:=mul_le_mul_of_nonneg_left hb (show 0≤ G0 from zero_le_one.trans hQ); have hx:=mul_le_mul_of_nonneg_left hf (show 0 ≤ b from zero_le_one.trans hb); change 100*G0+2* (↑(k-j):ℝ) * b ≤ (prism y:ℝ)/32; linarith only [hf,hQ,hb,hφ,hh,hx, mul_le_mul_of_nonneg_right hk (lira A k|>.le)]
    constructor
    · intro i hi he; have hp: renal A i=(A.clock.hatBeta (i+1))^ (-(2:ℝ)):=rfl; rw[hp,Real.rpow_neg (bell ..|>.le),Real.rpow_two]; unfold bountyW; dsimp only
      rw [show 2*((i+1)-j)=2*(i-j)+2 from by omega, pow_add]; let C:= Tau A j 1000000; let Iv:= A.clock.hatBeta (i+1); have hI:0<Iv:=bell ..; change C*y^(2*(i-j)) ≤ (Iv^ (2:ℕ))⁻¹*(C*(y^(2*(i-j))*y^ (2:ℕ)))
      have he':0<C:=Tau_pos ..; field_simp; exact pow_le_pow_left₀ hI.le (show Iv ≤ y from monoBeta _ h he) 2
    have hm:=le_trans (one_le_pow₀ (le_trans (by norm_num : (1:ℝ)≤4) Ha) (n:=1)) (pow_le_pow_right₀ (le_trans (by norm_num : (1:ℝ)≤4) Ha) (show 1≤27 by decide)); have hs : a^27 ≤ G0:= pow_le_pow_right₀ (le_trans (by norm_num : (1:ℝ) ≤ 4) Ha) (by decide)
    have hz: 1 ≤ bountyW A j m:= stipend ..; apply (div_le_iff₀ (by positivity)).2
    apply le_trans _ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Tau_pos ..|>.le) hZ _) (Tau_pos ..|>.le)); rw [sq,Tau,watch,Tau,watch,← Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; norm_num; linarith only[hL,hQ,hs]
end YM.Trace.Terrace
