import YM.TraceExtension.Shepherd.Triton
import YM.TraceExtension.Terrace.Vapid
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price MergeProof.East Further.CorrectedLift Climb Analysis Work Weir
open Further.PhysicalPeriodLimitF933 Shunt PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells Pressure
open Relay Shepherd
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge} {C:Family G} (H:C.Makes) (θ:PostT C.path.levels) (h:G.Simple)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "P"=> C.S
include H θ h
lemma funeral : ∀ᶠ i:ℕ in atTop,∀ p N:ℕ,i+1≤N → Real.exp (brinkP C i p (i+1) N ((A|>.clock.threshold (i+1))/16)) ≤ Real.exp (-(2:ℝ)*(prism ((A).clock.hatBeta (i+1)) :ℝ)):=by
   let a:= (A); let t(i):=a.clock.monitor i; let x(i):=a.clock.hatBeta i; let y(i):= Lyra a i; let K(i):= (prism (x i) :ℝ)
   let Z(i):=(a.clock.threshold i)/16; let B(i):=(a.params i).clip.linear
   have ht(i):0 < Z i:=div_pos (a.budget i|>.threshold_pos) (by positivity); have hB(i): 0<B i:= (a.params i).clip.tail_pos
   let L:ℝ:=10*16^ (2:ℕ)
   have hQ : ∀ᶠ i:ℕ in atTop,L*y i*(y i^6+2*K i) ≤ t i^2:=by
      filter_upwards[(hrate a h).eventually ((((logC.times L (by unfold L; positivity)).cop ((logC.crop 6).gather ((bankH 40).times 2 (by positivity)))) 2 (by norm_num)))] with i hp; apply le_trans hp.2; change Wave 2 (x i) ≤ a.clock.monitor i ^2; rw[oracle,sq,walt]; norm_num [x]
   have h(k): (P).a k/(P).a (k+1)= ((P).block k).val:=by rw[C.S.a_step,div_div_eq_mul_div,mul_div_cancel_left₀];exact C.S.a_pos _ |>.ne'
   filter_upwards [(tendsto_add_atTop_nat 1).eventually hQ, (tendsto_add_atTop_nat 1).eventually (Vac.treasury_stage (A) ‹G.Simple›)] with i hi hv p N hN
   let j:=i+1; let c:= y j; let q:=K j; have ht': x j*(Z j*16)^2=t j^2:=by
      unfold Z; rw [div_mul_cancel₀ _ (by norm_num)]; change x j*((Real.sqrt (x j))⁻¹*t j)^ (2:ℕ)=_; rw [mul_pow,inv_pow,Real.sq_sqrt (bell ..|>.le),← mul_assoc,mul_inv_cancel₀ (bell ..|>.ne'),one_mul]
   let s:= ((P|>.block i).val:ℝ); have hc:0 < c:=lira ..; have hS:s ≤ c:= (θ.bloom i).trans (lypos a ‹G.Simple› i.le_succ)
   let R:=C.path.rep N p (i+1); have hR:R.clip= (a.params (i+1)).clip:= (H.wilson.represents N p _ hN).clip
   apply Real.exp_monotone; unfold brinkP
   change (C.S.a i/C.S.a j)^4* _ - R.beta*(R.clip.linear/5*(Z j)^2)≤ _ ; rw [h,hR]
   have hx0: s^4 * Vac.treasury a j ≤ c^6:= (mul_le_mul_of_nonneg_left (hv.trans (θ.purse j)) (pow_nonneg (Nat.cast_nonneg _) (4:ℕ))).trans ((mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hS _) (sq_nonneg c)).trans_eq (by change c^4*c^ (2:ℕ)=_;ring))
   have hp: (x j/2) * (B j/5*(Z j)^2) ≤ R.beta*(B j/5*(Z j)^2):= mul_le_mul_of_nonneg_right (H.wilson.represents _ _ _ hN|>.band.1) (mul_nonneg (div_nonneg (hB ..|>.le) (by positivity)) (sq_nonneg _))
   have h1: c^6+2*q ≤ (x j/2)*(B j/5*(Z j)^ (2:ℕ)):=by
       have hh:= θ.jig j; rw [← ht'] at hi
       unfold L at hi; change c*B j ≥ 1 at hh; change 10*16^ (2:ℕ)*c * (c^6+2*q)≤_ at hi; linarith only [mul_le_mul_of_nonneg_right hi (hB j|>.le),mul_le_mul_of_nonneg_right hh (show 0 ≤ c^6+2*q from by unfold q K;positivity)]
   change s^ (4:ℕ)* _ - R.beta*(B j/5* _) ≤ -2*q; linarith only[hp,h1,hx0]
lemma expire :∀ᶠ i:ℕ in atTop,∀ p N:ℕ,0 < i→∀ hi:i ≤ N,∀ (P':Support (C.side i p))(f:Config G (C.side i p)→ℂ)(U V:ℝ),Envelope f→0≤U→(∀ x, ‖f x‖≤V) → (∀ x, Healthy ((A|>.clock.threshold i)/16) P' x → ‖f x‖ ≤ U) → ‖Wilson.moment (C.beta N p) (backTo C.path N p hi f)‖ ≤ U + V*P'.card*Real.exp (-(2:ℝ)* (prism ((A).clock.hatBeta i):ℝ)):=by
    obtain ⟨k,hk⟩:= eventually_atTop.mp (funeral H θ h); filter_upwards [eventually_gt_atTop k] with i hi p N hI hN Q f U V hF ht hv hp
    cases i with
    | zero=>omega
    | succ i=>
       let x:= (A).clock.hatBeta (i+1); let b:= ((A).budget (i+1)).threshold; have hB: (C.path.rep N p (i+1)).p=(A).budget (i+1):=(H.wilson.represents _ _ _ hN).vac; have hv' : 0≤ V:= (norm_nonneg _).trans (hv 1);
       have hθ:0<b:= ((A).budget _).threshold_pos; have hT:= soils H hN (Nat.le_succ i) (show 0 < b/16 by positivity) (by rw[hB];change 2*(b/16) ≤ b;linarith only[hθ]) (point_room _ θ i) Q f hF U V hv' hv hp ht; apply hT.trans; exact add_le_add_right (mul_le_mul_of_nonneg_left (hk i (by omega) p N hN) (mul_nonneg hv' (Nat.cast_nonneg _))) _
end YM.Trace.Terrace
