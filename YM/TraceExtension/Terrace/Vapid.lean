import YM.TraceExtension.Terrace.Tolls
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price MergeProof.East Further.CorrectedLift Climb Analysis Work Weir
open Further.PhysicalPeriodLimitF933 Shunt PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells Pressure
open Relay Shepherd
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}
lemma priest (G:Gauge)(S:Stage)(l:ℕ):∀ᶠ x:ℝ in atTop,∀ (w:ℝ),1 ≤ w → w ≤ Real.exp ((prism x:ℝ)/32) →∀ (n:Side)(R:Rep G n)(Λ:ℝ), Age S x Λ R→∀ z:ℝ, Shepherd.tariff R (wingC R z S.width S.paths Λ) (2*hue x) ≤ 1 → ExpenseH S.paths Λ (Weir.smoke x) (Weir.hue x) 1 S.width x z w R l (wheelQ x) (prism x):=by
    let c:= Real.exp ((S.supportExponent-4+1)*l); let e(x:ℝ):= Real.exp (-(prism x:ℝ)/8)
    have he : Tendsto e atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (by simpa only[neg_div] using! tendsto_neg_atTop_atBot.comp ((tendsto_natCast_atTop_atTop.comp growthP).atTop_div_const (by norm_num:(0:ℝ)<8)))
    have hx':Tendsto (fun x=> Real.exp (3*e x)-1) atTop (𝓝 0):=by
       have hu:= Real.continuous_exp.continuousAt.tendsto.comp (he.const_mul 3); simpa using! hu.sub_const 1
    let f(x:ℝ):=((radiusB x+radiusB x+1:ℕ):ℝ)^4;
    have hf:Weir.Lim 0 f:=by unfold f; push_cast; exact ferry ((((upperB.gather upperB).gather (mass zero_le_one))).crop 4)
    filter_upwards [bsize_c,Dsmall,mires G S,gardenP (c*Real.exp 2) 1,gardenP (4*c) 0,gardenP 8 3,gardenP 3 1,hx'.eventually (ge_mem_nhds zero_lt_one),hf 1 (by norm_num), eventually_gt_atTop (1:ℝ)] with x hv ht hm hC hk hA hα hE hr hx w hW hz n R v hQ z hr'
    specialize hm n R v hQ; let m:=wheelQ x; let k:=prism x; have hK:(4*(k:ℝ)) ≤ (m:ℝ):=by exact_mod_cast hv
    let c':=Real.exp ((k:ℝ)/2); have hc:1 ≤ c':=Real.one_le_exp (by positivity); set u:=Real.exp (-(m:ℝ))*Shepherd.tariff R (leaseC R S.width S.paths v) (hue x) with hu;
    have hp: 2*4*Real.exp k*u ≤ e x:=by
       unfold u; have hs:= mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*4*Real.exp k*Real.exp (-(m:ℝ)) by positivity); have hδ:= mul_le_mul_of_nonneg_left hA (show 0 ≤ Real.exp k*Real.exp (-(m:ℝ)) by positivity); linarith only [hs,hδ, show Real.exp k *Real.exp (-(m:ℝ))*Real.exp ((k:ℝ)/32) ≤ e x from by rw[← Real.exp_add,←Real.exp_add]; exact Real.exp_monotone (by change _ ≤ -(k:ℝ)/8; linarith only[hK,Nat.cast_nonneg (α:=ℝ) k])]
    have he0:e x≤1:=Real.exp_le_one_iff.mpr (by change -(prism x:ℝ)/8 ≤ 0; linarith only [Nat.cast_nonneg (α:=ℝ) (prism x)])
    refine ⟨hW,hr',?_, c', e x, hc, ?_ , (Real.exp_pos _).le, ?_ ,?_ ⟩
    · change 4*u≤1; by_cases hs:0 ≤ u; swap; · linarith only [le_of_not_ge hs]
      refine le_trans ?_ (hp.trans he0); linarith only [hs,mul_le_mul_of_nonneg_left (Real.one_le_exp (Nat.cast_nonneg k)) hs]
    · rw [hQ.depth]; change 4*c'*c ≤ _; rw [pow_zero,mul_one] at hk
      apply le_trans _ ((Real.exp_monotone (a:= (k:ℝ)/2+k/32) ?_) : _ ≤ Real.exp k); swap; · linarith only [Nat.cast_nonneg (α:=ℝ) k];
      rw [Real.exp_add]; linarith only [mul_le_mul_of_nonneg_left (le_trans (b:=Real.exp ((k:ℝ)/32)) hk le_rfl) (zero_le_one.trans hc)]
    · rw[hQ.depth]; change x*c* Real.exp 2*(w^2/c') ≤ _; have hp':x*c*Real.exp 2 ≤ Real.exp ((k:ℝ)/32):=by rw [pow_one] at hC; linarith only [hC]
      let y:=(k:ℝ)/32; apply (mul_le_mul hp' (div_le_div_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hW) hz 2) (zero_le_one.trans hc)) (show 0 ≤ w^2/c' by positivity) (Real.exp_pos _).le).trans
      change Real.exp y*(Real.exp y^2/c')≤_; rw[sq,← Real.exp_add, show c'= _ from rfl, ← Real.exp_sub (y+y) _,← Real.exp_add]; exact Real.exp_monotone (by unfold y; change _ ≤ -(k:ℝ)/8; linarith only[Nat.cast_nonneg (α:=ℝ) k])
    intro t; have hT:t ≤ 3*e x:=by change e x + (2*4*Real.exp k*u+2*Real.exp k*_) ≤ _;linarith only[hp,ht]
    constructor
    · have hu:(R.p.B+R.p.B+1:ℝ)^ (4:ℕ)=f x:= by rw [hQ.hM.2.1]; unfold f; push_cast; rfl
      simp only[Nat.cast_add,Nat.cast_pow,Nat.cast_one]; rw[hu]; refine le_trans (mul_le_mul_of_nonneg_left hT (by unfold f; positivity : 0 ≤ f x)) ?_
      apply le_trans (mul_le_mul_of_nonneg_right (hr.2.trans (Real.rpow_one _).le) (show 0≤3*e x by unfold e; positivity));
      have he:(3*x)≤ Real.exp ((k:ℝ)/32):=by rw[pow_one] at hα; exact hα
      apply le_trans _ (c:=1) (b:= Real.exp ((k:ℝ)/32)*e x); swap; · exact ((by ring : x*(3*e x) = 3*x*e x) ▸ mul_le_mul_of_nonneg_right he (show 0 ≤ e x from (Real.exp_pos _).le))
      unfold e; rw[← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by change _+( -(k:ℝ)/8) ≤0;linarith only[Nat.cast_nonneg (α:=ℝ) k])
    exact le_trans (sub_le_sub_right (Real.exp_monotone hT) _ ) hE
end YM.Trace.Terrace
