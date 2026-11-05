import YM.TraceExtension.Prom.Port.Stagecraft
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.SectorChange SectorNext.Vacuum Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Push.SectorMeasure
     YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory Bid Display Display.Docking Filter AnalyticBridge.LocalGaussianLaws Local RG.Supply Next.Rank.Station Tree
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} (B : Binding C) {N i k p : ℕ}
    {g : Course C N p k} (J : ChartRatio G) (ξ : Purse)


local notation "St" => C.path.levels.clock.op i p
local notation "xℓ" => C.path.levels.clock.factor (C.path.levels.clock.J (i+1))

set_option quotPrecheck false

-- call assembler
section
variable (c : Course C N p k) (V : (i : ℕ)→ Rep G (C.side i p)) (l d : ℝ)

-- no Purchase; knows next
end

section volume
-- not requiring a modified scale supposition in lower, purchases eventually for every paid schedule independently
open Asymptotics
lemma vault_sizeSky (A : Levels G) (hs : G.Simple) : ∀ᶠ k in atTop,∀ (p : Purse), CorridorSky A p.band p k → WaxroomSky A p k:= by
  let b:= A.clock.hatBeta; let B:=A.clock.bar
  let d:= G.slopeConstant
  have ht := hat_rate A hs; have hu:= brims
  have hQ (x) : 0 ≤ d * Real.log ((A.S.block x).val):= Work.E04.shift_nonneg G _
  have hZ : Monotone b:= monotone_nat_of_le_succ (fun i=>by unfold b Calendar.hatBeta; rw [Schedule.scale_succ,mul_add]; linarith only [hQ i])
  have hv:∀ᶠ i in atTop, ∀ j,100*(1+radiusB (retime (b i)))≤(A.S.side i j).val:= by
    let w := fun t:ℝ=> (100*(1+4*(B+d*t)))*Real.exp (-t)
    have he : Tendsto w atTop (𝓝 0):= by
      have hp:Tendsto (fun pA:ℝ=> pA * Real.exp (-pA)) atTop (𝓝 0):= by simpa only [pow_one,one_mul,Real.exp_neg, div_eq_mul_inv] using! (isLittleO_pow_exp_pos_mul_atTop 1 zero_lt_one).tendsto_div_nhds_zero
      have hv:Tendsto (fun pA:ℝ=> Real.exp (-pA)) atTop (𝓝 0):=Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr tendsto_id)
      have hx:=(hp.const_mul (400*d)).add (hv.const_mul (100*(1+4*B))); rw [mul_zero,mul_zero,add_zero] at hx
      exact hx.congr fun a=>show _= w a from (by unfold w; ring)
    filter_upwards [he.comp A.S.divergent |>.eventually (ge_mem_nhds zero_lt_one), ht.eventually ((Work.E09.radiusB_small 1 zero_lt_one 1).def zero_lt_one), ht.eventually hu] with i hi hf hv p
    let pA:= A.S.denominator i
    have h':0<b i:=zero_lt_one.trans (A.fits.delayed i)
    have h0 : (radiusB (b i):ℝ) ≤ b i:= by change 0<A.clock.hatBeta i at h'; unfold b; simpa only [Real.rpow_one,pow_one,one_mul,Real.norm_of_nonneg h'.le,Real.norm_of_nonneg (Nat.cast_nonneg _)] using! hf
    have hp:(100:ℝ)*(1+4*b i) ≤ (pA.val:ℝ):= by
      let w:= A.S.scale i
      change 100*(1+4*b i)*Real.exp (-w)≤ 1 at hi
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _),one_mul] at hi
      have hh : Real.exp w=(pA.val:ℝ):= by
        unfold w Schedule.scale; rw [Real.exp_log (inv_pos.mpr (A.S.a_pos _)),Schedule.a,inv_inv]
      rw [← hh]; exact hi
    have hx : (radiusB (retime (b i)):ℝ) ≤ 4 * b i:= le_trans (show _ ≤ (4:ℝ)*(radiusB (b i):ℝ) by exact_mod_cast hv.2) (mul_le_mul_of_nonneg_left h0 (by norm_num))
    refine le_trans (b:=pA.val) ?_ (Nat.le_mul_of_pos_left _ (A.S.period p).property)
    exact_mod_cast (show (100:ℝ)*(1+radiusB (retime (b i))) ≤ pA.val from by linarith only [hx,hp])
  obtain ⟨j,hj⟩:= eventually_atTop.mp hv
  filter_upwards [ht.eventually (eventually_gt_atTop (2*b j))] with k hk p hp i hi hi' pA
  refine hj i ?_ pA; by_contra! h; have hh:b i ≤ b j:= hZ h.le
  have hf:b k/2 ≤ b i:= hp.court i hi hi'.le |>.1; change _<b k at hk; linarith only [hh,hf,hk]
end volume

end YM.PhysicalNext.InteractingRank
