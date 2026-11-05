import YM.UVExtension.Tide.Falls
/-! # Real chessboard rapid rates, fine and layout stop. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Tide
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open Source Labels Gale Mast MergeProof Cells GridApprox Accent Extra.Histories
open Swell Stock Harvest
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {Q:Factor A} {S: Uses Q hG} {C:ℕ→ℝ}{w:Bid.Worth}{R: Bandage Q C w} {t:ℕ→ℕ}(L:Cellar S t R)
    (N n m k d:ℕ) {a:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a)
open Cellar Gale.Circuit
local notation "T"=> A.B.a.S
local notation "φ"=> A.B.a
local notation "P"=> A.B.a.budget m
local notation "R0"=> desk a ha
local notation "ℍ"=> Row a
set_option quotPrecheck false
local notation "V0"=> Cellar.yard (roseA S) L
variable (I:ℕ→ℕ)(H':Harvest.Barn S R I L)(hK:Mix.paidL (Cellar.yard (roseA S) L))

private lemma bits {α:Type}(s:Finset α){x:α→ℝ}{p M:ℝ}(hp:0≤ p)(hf:0≤M)(hv:1 ≤ M)(h:∀ i,0≤ x i)(ht:∀ i∈s,p+x i ≤ M): (∏ i∈s,(p+x i))-(∏ i∈s,x i)≤ (s.card:ℝ)*p*M^s.card:=by
   induction s using Finset.induction with
   | empty => simp
   | insert i s hi ih=>
      let A:=∏ j∈s,(p+x j); let B:=∏j∈s,x j; have he:A≤ M^s.card:=by simpa using! Finset.prod_le_prod (f:=fun i=>p+x i) (g:=fun _=>M) (fun i _=>add_nonneg hp (h i)) (fun i hh=>ht _ (Finset.mem_insert_of_mem hh))
      have hf₁:=mul_le_mul_of_nonneg_left he hp; have hx₀:A-B ≤ (s.card:ℝ)*p * M^s.card:= ih (fun i hh=> ht i (Finset.mem_insert_of_mem hh))
      have hz: x i ≤ M:= (le_add_of_nonneg_left hp).trans (ht i (Finset.mem_insert_self ..))
      rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.card_insert_of_notMem hi,pow_succ]; push_cast; change (p+x i)*A-x i*B≤ _
      have hh:= mul_le_mul_of_nonneg_left hx₀ (h i); have hX:=mul_le_mul_of_nonneg_right hz (show 0 ≤ (s.card:ℝ)*p * M^s.card by positivity); nlinarith only [hh,hX,hf₁,mul_le_mul_of_nonneg_left hv (show 0 ≤ p*M^s.card by positivity)]

private lemma bump (x:ℝ)(s:ℕ)(y: Fin s→ ℝ) (P':Schedule)(ha:0≤x)(hv:∀ i,y i ≤ x): ∃ b:ℝ,4≤ b ∧ ∀ᶠ j in atTop,∀ k≥j, b*P'.scale j ≤ P'.scale k→
    let t i:= expS P' (y i) j; let p:= expS P' (-1/16) k; (∏ i,(p+t i))-(∏ i,t i)≤ expS P' (-(1/32)) k:=by
    let r:=x+1; have hr:0 ≤ r:=by unfold r; linarith only [ha]
    let B:=4 + 64*r*s; have hB:4 ≤ B:= by unfold B; exact le_add_of_nonneg_right (by positivity)
    have he := (Note.notes P' 2 two_pos).mills (Note.bell_exp P' x); obtain ⟨N,hN⟩:= eventually_atTop.mp (he.outweigh (Note.bell_exp P' r) (by unfold r; linarith))
    have hs:Tendsto (expS P' (1/64)) atTop atTop:= Real.tendsto_exp_atTop.comp (P'.divergent.const_mul_atTop (by norm_num : (0:ℝ)<1/64)); obtain ⟨t,ht⟩:= eventually_atTop.mp (hs.eventually_ge_atTop (s:ℝ))
    refine ⟨B,hB,?_⟩; filter_upwards [eventually_ge_atTop N,P'.divergent.eventually_gt_atTop 0,eventually_ge_atTop t] with j hj hp h k hk hX; intro f p
    let M:= expS P' r j; have hm:1 ≤ M:= Real.one_le_exp (mul_nonneg hr hp.le); have hP: p ≤ expS P' x j:= by refine Real.exp_monotone ?_; exact le_trans (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hp.trans_le ((bob _).monotone hk)|>.le)) (mul_nonneg ha hp.le)
    have hQ i:p+f i ≤ M:=(add_le_add hP (Real.exp_monotone (mul_le_mul_of_nonneg_right (hv i) hp.le))).trans ((two_mul _|>.symm).trans_le (hN j hj))
    have hx: (∏ i,(p+f i))-(∏ i,f i) ≤ (s:ℝ)*p*M^s:=by simpa only [Finset.card_univ,Fintype.card_fin] using! bits Finset.univ (Real.exp_pos _|>.le) (Real.exp_pos _|>.le) hm (fun i=> (Real.exp_pos _|>.le : 0 ≤ f i)) (fun i _=> hQ i)
    apply hx.trans; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (ht k (h.trans hk)) (show 0≤p from Real.exp_pos _|>.le)) (show 0≤ M^s from pow_nonneg (zero_le_one.trans hm) _)).trans; dsimp only [p,M]; unfold expS; rw [← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone; unfold B at *; linarith only [hp,hX]

open Relay
section
variable (u: Fin k→ (roster L).Token)(W:(i:Fin k)→ Circuit S (u i).1 N n R L a)(v:Keys S)(J:ℕ) (hJ:J≤ m)(hu:∀ i,t (u i).1 ≤ m)
local notation "r"=> fun (i:Fin k)=> len G (u i).1
local notation "F"=> yard v L
local notation "ζ"=> fun i=> expS (A.B.a.S) (↑(u i|>.1)+1) J -- precheck
include R
private lemma crewAt (h:m≤N)(i:Fin k): crew L N n m k u W hu (v N n|>.val) i= science (yard v L) m N n (u i).1 (fetch S (u i).1 N n R L (W i) (u i).2 m (hu i) ((v N n).val:ℂ)):=by
    let ξ:= fetch S (u i).1 N n R L (W i) (u i).2 m (hu i) ((v N n).val:ℂ); exact (parser L m n m (u i).1 le_rfl (fun _ _=> rose0 S) ξ).trans ((parser L N n m _ h v ξ).symm)

private lemma walls (q:Fin k→Site (A.B.a.S.side J n))(hq:Injective q)(p:ℝ)(t':Fin k→ℝ)(hN:m≤N)
    (l:ℕ)(hK: GridApprox.room A.B.a J m l) (f:Fin k→ Config G (A.B.a.S.side m n) →ℂ) (ht:let T':= GridApprox.tilesAt A.B.a.S n (hJ.trans hN); ∀ i, Interior (T'.chamber 0) ((yard v L).O N n (d:=(u i).1) (u i).2 0) ∧ Interior (GridApprox.window (0:Site (A.B.a.S.side m n)) l) (f i) ∧ T'.rootTest ((yard v L).beta N n) ((F).O N n (d:=(u i).1) (u i).2 0) ≤ t' i∧ T'.rootTest ((yard v L).beta N n) (GridApprox.backTo (F).path N n hN (f i)-(F).O N n (u i).2 0) ≤ p):
     ‖tasting ((yard v L|>.path).rep N n m) (cargo k (anchor A.B.a.S n hJ ∘ q) f)- (yard v L).numeric N n u (anchor A.B.a.S n (hJ.trans hN) ∘ q)‖ ≤ (∏ i,(p+t' i))-(∏ i,t' i):=by
    let P':= F; let X:= F; let g(i:Fin k):= backTo P'.path N n hN (f i); let b(i:Fin k):= P'.seen (u i) (0:Site (P'.side N n)); let v':= P'.beta N n; let A':= anchor (T) n (hJ.trans hN); let y(i):= A' (q i)
    let t:= C -- retire
    have he: tasting ((yard v L|>.path).rep N n m) (cargo k (anchor (T) n hJ ∘ q) f)= Wilson.moment v' (lifting A.B.a.S n (hJ.trans hN) q g):=by
        have Hf(i):= ht i|>.2.1; have hA: Envelope (lifting P'.S n hJ q f):= lifts_env P'.S n hJ q f (fun i=> cylinder_env (Hf i))
        exact (scaledK _ (selected S v) m N n hN hA).symm.trans (congr_arg (moment v' ·) (aggregation (F).path hN hJ _ q hq _ Hf hK))
    let s:= tilesAt A.B.a.S n (hJ.trans hN)
    have hz:= GridApprox.tariff (T) (hJ.trans hN) (P'.beta N n) (Vintage.YM.Cells.seamless (intakeV v L) N n) q hq b g t' (fun _=> p) (fun i=> (ht i).1) (fun i=> whereBack P'.path hN hJ _ (ht i|>.2.1) hK) (fun i=> ht i|>.2.2.1) (fun i=> ht i|>.2.2.2)
    have hB : moment (P'.beta N n) (fun U=>∏ i,b i (translate (y i) U))= P'.numeric N n u (A' ∘ q):=by
        apply congr_arg (moment _); refine funext fun U=>?_ ; apply Finset.prod_congr rfl; intro i _; exact ((F).translation (d:=(u i).1) (N:=N) (p:=n) 0 (A' (q i)) (u i).snd U).trans (congr_arg (fun x=>P'.seen (u i) x U) (zero_add _))
    change ‖moment (P'.beta N n) (lifting P'.S n (hJ.trans hN) q g) - moment (P'.beta N n) (fun U=>∏ i,b i (translate (y i) U))‖ ≤_ at hz; rw [he]; rw [hB] at hz; exact hz
include hK H'
lemma streams : ∃ b:ℝ,4 ≤ b∧ ∀ᶠ j in atTop,∀ m,∀ h:j ≤ m,b*A.B.a.S.scale j ≤ A.B.a.S.scale m→ ∃ hu:∀ i,t (u i).1 ≤ m,∀ q:Fin k→ Site (A.B.a.S.side j n),Injective q → ∀ N (hN:m<N) (W:(i:Fin k)→ Circuit S (u i).1 N n R L a)(v:Keys S), ((v N n).val:ℂ)∈ ball 0 a→
    ‖fancy L N n m k u W hu (anchor (T) n h ∘ q) (v N n).val - (yard v L).numeric N n u (anchor (T) n (show j≤N from h.trans hN.le) ∘ q)‖ ≤ expS A.B.a.S (-(1/32)) m:=by
    let f(i:Fin k):= (u i).fst; let g i:ℝ:=f i+ (1:ℝ); have hg i:0≤g i:= add_nonneg (Nat.cast_nonneg _) zero_le_one
    let U:= ∑ i,g i; obtain ⟨b,hb,hF⟩:= bump U k g (T) (Finset.sum_nonneg (fun i _=>hg i)) (fun i=> Finset.single_le_sum (fun i _=> hg i) (Finset.mem_univ i))
    choose x hx h using (fun i=> slips (a:=a) L n I H' hK (f i) ((u i).2)); let b':= b+∑ i,x i; have he: b ≤ b':= le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=> (by norm_num : (0:ℝ) ≤ 4).trans (hx i)))
    let R':= Finset.univ.sup r; refine ⟨b',hb.trans he,?_⟩; filter_upwards [eventually_all.mpr h,hF,A.B.a.S.divergent.eventually_gt_atTop 0,ocean A.B.a R'] with j h ht hz hv m hm hj
    have he': b*A.B.a.S.scale j ≤ A.B.a.S.scale m:= (mul_le_mul_of_nonneg_right he hz.le).trans hj; have hX := hv _ hm ((mul_le_mul_of_nonneg_right hb hz.le).trans he')
    have hE(i): x i ≤ b':=(Finset.single_le_sum (fun i _=>(by norm_num : (0:ℝ)≤4).trans (hx i)) (Finset.mem_univ i)).trans (le_add_of_nonneg_left (by linarith only [hb]))
    let t' (i):= h i m hm ((mul_le_mul_of_nonneg_right (hE i) hz.le).trans hj); let hu(i):= (t' i).choose; refine ⟨hu,fun q hq N hN W v hx=>?_⟩; let K:=crew L N n m k u W hu (v N n).val; let T'(i):= expS A.B.a.S (g i) j
    apply le_trans _ (ht m hm he'); refine walls L N n m k u v j hm q hq (expS (T) (-1/16) m) T' hN.le R' hX K ?_
    intro _ i
    obtain ⟨h₁,h₂,h₃,h₄⟩:= ((t' i).choose_spec).2 N hN (W i) v hx
    have ht : K i = _:= crewAt L N n m k u W v hu hN.le i
    rw [ht]; exact ⟨h₁,h₂.enlarges (window_large (Finset.le_sup (s:=Finset.univ) (f:=fun i:Fin k=>len G ((u i).1)) (Finset.mem_univ _))),h₃,h₄⟩
end
end YM.UVExtension.Tide
