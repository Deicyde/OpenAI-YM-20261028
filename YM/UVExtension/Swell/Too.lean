import YM.UVExtension.Pier.Ships
import YM.MergeProof.North.GraceN
/-! # Subexp/poly accounting per-stage -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Swell
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet Extra.Histories MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {P:Type*}(S : Schedule)
-- all polynomials priced eventually. no slope condition to conceal arithmetic.
def expS (S:Schedule) (C:ℝ) (i:ℕ) := Real.exp (C*S.scale i)
def PolyB (S:Schedule)(F:ℕ→ℝ):= ∃ C:ℝ,0<C ∧∀ᶠ i in atTop, ‖F i‖ ≤ expS S C i
namespace PolyB
variable {S}{a b:ℕ→ℝ}
lemma fromNote {c:ℝ}(h:Note S a c): PolyB S a:= by
   let v:= 1+max 0 c; have he : c < v:= (le_max_right _ _).trans_lt (lt_add_of_pos_left _ zero_lt_one)
   refine ⟨v,by unfold v; positivity,(h.outweigh (Note.bell_exp S v) he).mono fun i hi=>?_⟩; rw [Real.norm_of_nonneg (h.pos i|>.le)]; exact hi
lemma mono (h:PolyB S b)(he:∀ᶠ i in atTop,‖a i‖≤‖b i‖): PolyB S a:=by obtain ⟨c,hc,hX⟩:=h; exact ⟨c,hc,(he.and hX).mono fun i hi=> hi.1.trans hi.2⟩
lemma mul (h:PolyB S a)(hf:PolyB S b): PolyB S (fun i=>a i*b i):=by
   obtain ⟨c,hc,h⟩:=h; obtain ⟨d,hd,hQ⟩:= hf; refine ⟨c+d, add_pos hc hd,?_⟩; filter_upwards [h,hQ] with i hi hx
   apply (norm_mul ..).trans_le ((mul_le_mul hi hx (norm_nonneg _) (Real.exp_pos _).le).trans_eq ?_); unfold expS; rw [add_mul,Real.exp_add]
lemma add (h:PolyB S a)(hf:PolyB S b):PolyB S (fun i=>a i+b i) :=by
   obtain ⟨c,hc,h⟩:=h; obtain ⟨d,hd,hF⟩:=hf; let v:=max c d
   apply (fromNote ((Note.bell_exp S v).extra (Note.bell_exp S v))).mono
   filter_upwards [h,hF,S.divergent.eventually_gt_atTop 0] with i hi hx hA; refine (norm_add_le ..).trans ((add_le_add (hi.trans (Real.exp_monotone (mul_le_mul_of_nonneg_right (le_max_left c d) hA.le))) (hx.trans (Real.exp_monotone (mul_le_mul_of_nonneg_right (le_max_right c d) hA.le)))).trans ?_); exact le_abs_self _
lemma const (S:Schedule)(w:ℝ):PolyB S (fun _=>w):= by
    let v:=max 1 ‖w‖; have hp: 0<v:= lt_of_lt_of_le zero_lt_one (le_max_left ..)
    exact (fromNote (Note.notes S v hp)).mono (Eventually.of_forall fun i=> (show ‖w‖ ≤ v from le_max_right ..).trans (le_abs_self _))
lemma pow (h:PolyB S a)(n:ℕ): PolyB S (fun i=> a i^n):=by induction n with|zero=>simp only [pow_zero]; exact const S 1| succ i ih=>simpa only [pow_succ] using ih.mul h
lemma waves (s:Finset P) (a:ℕ→P→ℝ)(ha:∀ i∈s,PolyB S (fun j=> a j i)): PolyB S (fun j=> ∏ i∈s,a j i):=by
   induction s using Finset.induction_on with
   | empty=> simp only [Finset.prod_empty]; exact const ..
   | insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact (ha i (Finset.mem_insert_self ..)).mul (ih fun j hj=>ha j (Finset.mem_insert_of_mem hj))
lemma sum (s:Finset P)(a:ℕ→P→ℝ)(ha:∀ i∈s,PolyB S (fun j=> a j i)): PolyB S (fun j=>∑ i∈s,a j i):=by
   induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact const ..
   | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (ha i (Finset.mem_insert_self ..)).add (ih fun j hj=>ha j (Finset.mem_insert_of_mem hj))
lemma inverse (S:Schedule): PolyB S (fun i=> (S.a i)⁻¹):=by simpa [one_div] using fromNote ((Note.notes S 1 zero_lt_one).splits (Note.note_a S))
lemma stretch (S:Schedule): PolyB S S.scale:=by
   refine ⟨1,zero_lt_one,?_⟩; filter_upwards [S.divergent.eventually_gt_atTop 0] with i hi; unfold expS; rw [one_mul,Real.norm_of_nonneg hi.le]; exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
lemma payment (h:S.Gentle):PolyB S (fun i=> ((S.block i).val:ℝ)):=by
    refine fromNote (c:=0) ?_; refine ⟨fun i=>by positivity,h⟩
end PolyB

open ConnectedActivityE6
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A) {C:ℕ→ℝ}(h: Cloud.Leases C R.shape A.delay)
set_option quotPrecheck false
local notation "T"=> A.B.a.S
local notation "Θ"=> A.B.a
include h in
lemma taxes : PolyB A.B.a.S (fun i=> Real.exp ((A.B.a.budget i).supportExponent)):= by
    refine (PolyB.payment (Θ).fits.mesh).mono (Eventually.of_forall fun i=>?_)
    let j:=(Θ).clock.J (i+1); let t:=(Θ).clock.J i; let Q:=R.target j t
    have hp: (Θ|>.budget i).supportExponent+2 ≤ (R.expense j t).earn:=by
       rw [Rain.jersey (A:=A) (m:=i)|>.2.2.1]; have h:= R.pledging.agenda j t (step_paid A.B.a i)|>.1; linarith
    have ht : (Θ|>.budget i).supportExponent ≤ Q.relative := by
       let X:= R.expense j t; have hC: X.earn+X.two+X.one ≤ Q.exp:=X.worth; have he: Q.exp ≤ Q.relative:= by unfold Target.relative; linarith [Q.usable,Q.pos]
       linarith only [hp,X.first,X.second,hC,he]
    have he : 24*coined Q 0≤((T|>.block i).val:ℝ):= PriceCompiler.block_eq A.B.valid i|>.symm ▸ h.hearty j t (step_paid A.B.a i) 0 (Nat.zero_le _)
    rw [Real.norm_of_nonneg (Real.exp_pos _|>.le)]; apply (le_trans _ he).trans (le_abs_self _); refine le_trans ?_ (le_mul_of_one_le_left (Real.exp_pos _|>.le) (by norm_num)); unfold coined; apply Real.exp_monotone; push_cast; apply le_trans ht; rw [zero_add,mul_one]
    apply le_mul_of_one_le_right ((A.B.a.budget i).exponent_pos.le.trans ht); unfold Push.AbsoluteSums.Footprint.preCost Animals.ballCost; norm_cast; exact Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma theta (Q:Levels G): PolyB Q.S (fun i=> Q.clock.threshold i|>Inv.inv):=by
    have hb:PolyB Q.S (fun i=> Q.clock.hatBeta i):= (PolyB.const Q.S Q.clock.bar).add ((PolyB.const ..).mul (PolyB.stretch Q.S))
    refine hb.mono (Eventually.of_forall fun i=>?_); let x:= Q.clock.hatBeta i; have he:1<x:= Q.fits.delayed i; have hv : 1 ≤ Real.sqrt x:= by nth_rw 1 [← Real.sqrt_one]; exact Real.sqrt_le_sqrt he.le
    have hT: 1 ≤ Q.clock.monitor i:= Real.one_le_exp (sq_nonneg _); have hl : (Real.sqrt x)⁻¹ ≤ Q.clock.threshold i:= le_mul_of_one_le_right (by positivity) hT
    change ‖(Q.clock.threshold i)⁻¹‖≤‖x‖; rw [Real.norm_of_nonneg (inv_nonneg.mpr ( (show 0≤ (Real.sqrt x)⁻¹ by positivity).trans hl)),Real.norm_of_nonneg (zero_le_one.trans he.le)]; refine (inv_anti₀ (inv_pos.mpr (zero_lt_one.trans_le hv)) hl).trans ?_; rw [inv_inv]; have ht:= Real.sq_sqrt (zero_le_one.trans he.le); nlinarith only [ht,hv]
end YM.UVExtension.Swell
