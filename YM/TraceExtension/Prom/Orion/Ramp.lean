import YM.TraceExtension.Prom.Orion.Medal
import YM.TraceExtension.Prom.Order.Graph
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d:ℕ}
lemma tide_mode (A:Levels G)(h:G.Simple) : ∀ᶠ k:ℕ in atTop, A.clock.monitor k ≤ A.clock.monitor (k+1):=by
   filter_upwards [(hat_rate A h).eventually_ge_atTop (Real.exp 1)] with k hk
   have he: clim A k ≤ clim A (k+1) := add_le_add_right (mul_le_mul_of_nonneg_left (PhysicalNext.InteractingRank.Soft.scaleSky (Nat.le_succ k)) (Gauge.slopeConstant_pos h).le) _
   have ht:= Real.log_le_log (zero_lt_one.trans (A.fits.delayed k)) he; have hf : 1 ≤ Real.log (clim A k):= by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hk
   exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (Real.log_nonneg hf) (Real.log_le_log (zero_lt_one.trans_le hf) ht) _)
lemma near_skies (A:Levels G)(h:G.Simple) (he:∀ᶠ k in atTop,topL A k ≤ A.clock.monitor k) {b:ℝ}(hb:0≤b) : ∀ᶠ k in atTop, Station.gap A b k ≤ Station.gap A (b+1) (k+1):=by
   filter_upwards [(tendsto_add_atTop_nat 1).eventually he,tide_mode A h] with k h₀ ht
   have hx : mag A b k ≤ mag A b (k+1):= Real.rpow_le_rpow (Real.exp_pos _).le ht hb
   have hh : ((A.S.block k).val:ℝ) ≤ A.clock.monitor (k+1):= by rw [← A.fits.sameFactor]; exact le_trans (show wheel A (k+1) ≤ topL A (k+1) from le_max_left ..) h₀
   have hp : A.S.a k=A.S.a (k+1)*((A.S.block k).val:ℝ):= by rw[A.S.a_step]; exact (div_mul_cancel₀ _ (by exact_mod_cast (A.S.block k).property.ne')).symm
   have hz : mag A (b+1) (k+1)=A.clock.monitor (k+1)*mag A b (k+1):=by rw[Atlas.mag_bill,show b+1=1+b by ring,← overlap, fire_bill,mag_bill]
   unfold Station.gap; rw [hp,mul_assoc,hz]; gcongr
   all_goals first| exact (mag_pos ..).le|exact (A.S.a_pos _).le|exact (Real.exp_pos _).le
lemma gap_curve (A:Levels G)(b:ℝ)(k:ℕ)(x:ℝ)(hx:Station.gap A b k ≤ x)(hp:x ≤ Station.gap A (b+1) k): ∃ d:ℝ, d∈ Icc 0 1 ∧ x=Station.gap A (b+d) k:=by
    let f (i:ℝ):= Station.gap A (b+i) k;have he: Continuous f:= by
       unfold f Station.gap Station.mag; apply continuous_const.mul; apply Continuous.rpow (by fun_prop) (by fun_prop); exact fun _=> Or.inl (Real.exp_pos _).ne'
    have hX : f 0 ≤ x:= by unfold f; simpa only [add_zero] using! (by rw [add_zero]; exact hx : Station.gap A (b+0) k≤x)
    obtain ⟨t,ht,H⟩:= intermediate_value_Icc (zero_le_one' ℝ) he.continuousOn (show x∈Icc (f 0) (f 1) from ⟨hX,hp⟩); exact ⟨t,ht,H.symm⟩
lemma gap_account (A:Levels G)(h:G.Simple)(b:ℝ)(hb:0≤b)(he:∀ᶠ k in atTop,topL A k ≤ A.clock.monitor k) (J : ℕ): ∃ r:ℝ,0<r ∧ ∀ s,0<s → s≤r → ∃ k≥J,∃ c:ℝ, c∈ Icc 0 1 ∧ s=Station.gap A (b+c) k:=by
    obtain ⟨t,ht⟩:= eventually_atTop.mp (near_skies A h he hb)
    let i:= max t J; let a:= Station.gap A b; let r:= a i
    refine ⟨r,Station.gap_pos ..,fun s hS hy=>?_⟩
    have hχ: ∃ k, i < k ∧ a k ≤ s := ((eventually_gt_atTop i).and ((Station.gap_rate A h b).eventually (ge_mem_nhds hS))).exists
    let k:=Nat.find hχ; obtain ⟨hd,hE⟩:= Nat.find_spec hχ; change i < k at hd
    refine ⟨k,(show J ≤ i from le_max_right ..).trans hd.le, gap_curve A b k s hE ?_⟩
    obtain ⟨n,hn⟩:= Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hd))
    change k=n+1 at hn; have hx:i ≤ n:=by omega
    rw [hn]; apply le_trans _ (ht n (le_trans (show t ≤ i from le_max_left ..) hx));
    rcases eq_or_lt_of_le hx with h|h; exact h ▸ (show s ≤ Station.gap A b i from hy)
    exact le_of_lt (lt_of_not_ge fun H=> Nat.not_lt_of_le (show k ≤ n from Nat.find_min' _ ⟨h,H⟩) (show n<k by omega))
-- repeated per seq can always pass subseq and measured k distinct for arbitrary τ definitions
lemma gap_orders (A:Levels G)(h:G.Simple)(b:ℝ)(hb:0≤b)(he:∀ᶠ k in atTop,topL A k ≤ A.clock.monitor k) (s:ℕ→ℝ) (hh: Tendsto s atTop (𝓝 0))(hp:∀ j,0<s j) (J:ℕ): ∃ K P : ℕ→ℕ, StrictMono K ∧ StrictMono P ∧ ∀ j, J ≤ P j ∧ ∃ c:ℝ,c∈ Icc 0 1 ∧ s (K j)=Station.gap A (b+c) (P j):=by
   let F i k:= J ≤ k ∧ ∃ c:ℝ,c∈ Icc 0 1 ∧ s i=Station.gap A (b+c) k
   have hv(i k):∃ p q:ℕ,i<p∧k<q∧F p q:=by
      obtain ⟨r,hr,hT⟩:= gap_account A h b hb he (max J k+1)
      obtain ⟨p,hq,hX⟩:= ((eventually_gt_atTop i).and (hh.eventually (ge_mem_nhds hr))).exists
      obtain ⟨q,hQ,hc⟩:= hT _ (hp p) hX; exact ⟨p,q,hq,by omega,by omega,hc⟩
   choose K P hK hP H using hv
   let J':ℕ → ℕ × ℕ:= Nat.rec (0,0) (fun n i=> (K i.1 i.2,P i.1 i.2))
   refine ⟨fun i=>(J' (i+1)).1,fun i=> (J' (i+1)).2,strictMono_nat_of_lt_succ (fun i=> hK _ _),strictMono_nat_of_lt_succ (fun i=> hP _ _),fun i=> H _ _⟩
end YM.MergeProof.East
