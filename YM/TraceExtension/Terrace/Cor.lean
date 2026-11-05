import YM.TraceExtension.Terrace.Grid
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Trace.Terrace.Glade
open Function Filter Finset Lattice RG Wilson Labels Source Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price MergeProof.East Further.CorrectedLift Ward Climb Analysis Work Weir StressFlux
open Further.PhysicalPeriodLimitF933 Shunt PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells Pressure
open Motion AnalyticBridge VerifiedReset Relay ProofPorts.GridRealModelsEstimates20261012
open Wicket
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
lemma seatsafe (S:Signed){n:Side}(k:ℕ)(b:ℝ)(U:Config G n)(h:Healthy b (tower k) U): Healthy b (tower k) (pull S 0 U):=by
    let s:Seat n:= (S,0); refine (Seat.healthy s b _ U).mp (Disjoint.mono_left ?_ h)
    intro x hx; obtain ⟨y,hy,rfl⟩:= mem_image.mp hx; let x:=affine (R:=Per n) S 0 y; have he: separation (0:Site n) y ≤ k:= by simpa [tower,halo_spec] using hy
    have hf : Push.Local.turnSites S (0:Site n) 0=0:=by change affine (R:=Per n) S 0 0=0; simp [affine]
    have ht : separation (0:Site n) x=separation 0 y:=by nth_rw 1[← hf]; exact Push.Local.turn_sep ..
    exact halo_spec.mpr ⟨0,mem_singleton_self _,ht.le.trans he⟩
lemma costReed {n:Side}(i:Axis)(v:Axis→ Film G n)(U:Config G n)(t:ℝ) (hV:∀ a:Axis, ∀ s:Signed, ‖v a (pull s 0 U)‖ ≤ t): ‖Reed (present n) v i U‖ ≤ t:=by rw[reedEq,Finset.sum_apply]; apply le_trans (norm_sum_le ..); rw [← rent_collect t]; refine sum_le_sum (fun k _=>?_); change ‖muC i k • present n k _ U‖≤_; rw [norm_smul,mu_norm]; exact mul_le_mul_of_nonneg_left ((mirrorP ..).le.trans (hV _ k.1)) rent_pos.le
variable (H:C.Makes)(θ:PostT C.path.levels)(h:G.Simple)
set_option quotPrecheck false
local notation "A"=>C.path.levels
local notation "S!"=>C.S
include h θ
lemma focus_scale :∀ᶠ i:ℕ in atTop,(C.S.a i/C.S.a (summit (A) i))^5 ≤ Tau (A) i 100000:=by
    filter_upwards[back_gate (A) h θ] with i hi; rw [z_scale]; refine (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_monotone hi) _).trans_eq ?_; unfold Tau watch; rw[← Real.exp_nat_mul]; congr 1; norm_num; ring
omit θ in
lemma potent (c:ℝ)(hx:0 ≤ c):∀ᶠ i:ℕ in atTop, let b:= (prism ((A).clock.hatBeta (summit (A) i)):ℝ); Real.exp (-b) ≤ Tau (A) i (-c) :=by
   let P:= A; let Y:= summit P
   filter_upwards [(hrate _ h|>.comp (Sstar P)).eventually (hugeW c hx), (lrate P h).eventually_ge_atTop 1] with i hi hv k
   let y:=P.clock.hatBeta (Y i); let x:= Gate (P.clock.hatBeta i); let t:= Gate y; let z:= Lyra P (Y i); have hZ: Lyra P i ≤ z:=lypos P h (stellar ..|>.le);
   have H: 1 ≤ z:=hv.trans hZ
   have hX: x ≤ t:=pow_le_pow_left₀ (zero_le_one.trans hv) hZ _; have hp:0 ≤ t:= zero_le_one.trans (one_le_pow₀ H); have ht:c*t*z ≤ k/32:=hi; apply Real.exp_monotone; change -k≤ -c*(1/10000)* x; linarith only [ht, mul_le_mul_of_nonneg_left H (mul_nonneg hx hp),mul_le_mul_of_nonneg_left hX hx,show 0 ≤ k from Nat.cast_nonneg _,show 0 ≤ c*x from mul_nonneg hx ((gate_le _ ((A).fits.delayed i)).le)]
include H
lemma canopy (m:ℕ) : ∀ᶠ i in atTop, let k:= summit C.path.levels i;let t:=(A).clock.hatBeta k;let u:= Tau (A) i; let q:=(C.S.a i/C.S.a k)^5
    ∀ N p (hn:k≤N),let B:= tilesAt C.S p ((stellar A i).le.trans hn); let β:= C.beta N p; let P:= (A).clock.threshold k;∀ (l j:ℕ),room (A) i k l → ∀ (X Y: Axis→ Film G (C.side k p)) (v:Axis→ℂ), (∀ i:Axis,Interior (Push.GridApprox.window 0 l) (X i)∧ Interior (Push.GridApprox.window 0 l) (Y i))→
      (∀ i:Axis, B.rootTest β (backTo C.path N p hn (Y i)) ≤ u (-1800000))→ ( ((Wicket.tower j (n:=C.side k p)).card:ℝ) ≤ t^m)→
      (∀ i U, Healthy (P/16) (tower j) U → ‖X i U -Y i U+v i‖ ≤ Real.exp (-(prism t:ℝ))) → (∀ i U,‖X i U-Y i U‖ ≤ t^m)→∀ d:Axis, Crown C i N p hn (Reed (present _) (q • X) d):=by
    let V:= A
    filter_upwards [toll_small (x:=1000) (by norm_num) ((stickK V h θ).pows h m),potent h (show ℝ from 600000) (by norm_num),focus_scale θ h] with i hi hx hy k t u q N p hn B β P l j hL X Y v hV hP hr hQ h X'
    let n:= C.side k p; let G':= Reed (present n) (q • X) X'; let H':= Reed (present n) (q • Y) X'
    have hq:0 ≤ q:= pow_nonneg (div_pos (C.S.a_pos _) (C.S.a_pos _) |>.le) _; have hp(d): Interior (Push.GridApprox.window 0 l) ((q • Y) d):= conn _ (hV d|>.2) q
    refine ⟨H',tower j, l, reedRoad _ _ X' l (fun i=>conn _ (hV i|>.1) q), reedRoad _ (q • Y) X' l hp, hL,hr.trans hi,fun U=>?_, fun U h₀=>?_,?_⟩
    · rw [show H'= Reed (present n) (q • Y) X' from rfl];
      have hz: ((q • X) - (q • Y))= q • (X-Y):= (smul_sub ..).symm
      change ‖_ - Reed (present n) (q • Y) X' U‖ ≤ u 500000; rw [show _- Reed _ (q • Y) X' U= Reed (present n) (q • (X-Y)) X' U from (by rw [← hz,map_sub]; rfl: Reed _ (q • X) X' U-Reed _ (q • Y) X' U=_)];
      apply costReed; intro a s; change ‖q • (X a _-Y a _)‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg hq];
      exact (mul_le_mul_of_nonneg_left (h a _ |>.trans hi) hq).trans ((mul_le_mul_of_nonneg_right hy (Tau_pos ..|>.le)).trans ((Tau_add _ i 100000 1000).symm.le.trans (tau_mono _ _ (by norm_num))))
    · let z₀:Axis→ Film G n:= fun i U=> v i
      have hy': Reed (present n) (q • ((X-Y)+z₀))= Reed (present n) (q • X) - Reed (present n) (q • Y):=by rw[smul_add,smul_sub,map_add,map_smul,show Reed (present n) z₀=0 from const_zero v,smul_zero,add_zero,map_sub]
      change ‖G' U-H' U‖ ≤ _; rw[show G' U-H' U= _ from congr_fun (congr_fun hy'.symm X') U]; apply costReed; intro a s
      change ‖q • ((X a _-Y a _)+ v a)‖ ≤ _; rw[norm_smul,Real.norm_of_nonneg hq];
      refine (mul_le_mul_of_nonneg_left ((hQ a _ (seatsafe s j _ U h₀)).trans hx) hq).trans ((mul_le_mul_of_nonneg_right hy (Tau_pos ..|>.le)).trans ((Tau_add _ i 100000 (-600000)).symm.le.trans ?_)); exact tau_mono _ _ (by norm_num)
    rw [show backTo _ _ _ hn H'= _ from readUp i k N p (stellar (A) i|>.le) hn (q • Y) X' l hp]
    let W(d):=backTo C.path N p hn ((q • Y) d); have hz(d): Interior (B.chamber 0) (W d):= Broom i k N p (stellar (A) i|>.le) hn _ _ (hp d) hL
    refine (teamW C.S (u:=W) β _ X' (seamless H N p) hz _ ?_).2; intro d; rw[show W d=q • backTo C.path N p hn (Y d) from linC hn q (Y d),fade,Real.norm_of_nonneg hq];
    exact (mul_le_mul_of_nonneg_left (hP d) hq).trans ((mul_le_mul_of_nonneg_right hy (Tau_pos ..|>.le)).trans ((Tau_add _ i 100000 (-1800000)).symm.le.trans (tau_mono _ _ (by norm_num))))
end YM.Trace.Terrace.Glade
