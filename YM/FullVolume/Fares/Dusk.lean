import YM.FullVolume.Fares.Oz
/- Acquire tariff & eventual canopy budgets.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} {T:Campaign R}
set_option quotPrecheck false
local notation "P"=> R.alloy.B.a
local notation "A"=> R.alloy
local notation "X"=> R.kit
local notation "D"=> R.rolls
local notation "Φ"=> R.alloy.B.a.clock
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I]
open Face Face.Economics
namespace Sky
variable {Θ:Luna.Tableau T.width 300}{v:ℕ→ℕ→ℝ}(hk:Sky R T Θ v)
local notation "x"=> timeEntry R
local notation "t"=> T.width
local notation "d!"=> intervalClock R
local notation "j"=> R.alloy.B.a.clock.J
include hk
lemma presents (m:ℕ): Snowy t (X).shape R.y Θ v (j (m+1)) (j m) (x m):= hk.earned _ (timeEntry R m) ((A).B.valid.pays m) _ (step_paid _ _)
lemma receives (m N n:ℕ) (hm:m<N) :∃ a,Fund (T.L.prim N m n hm) Θ a (creditP (timeEntry R (m+1))) T.pay T.pay:=by
    let p:= hk.presents m; let i:=j m; let l:=j (m+1); let L:= R.rolls.L l; let q:= x m; let r:= x (m+1); let z:=creditP r; let D0:=station r
    have hr:r=Pressure.betaF G q L:= by have h:=Extra.Iteration.block_beta (a:=P) m; rw [Extra.Iteration.block_eq (A).B.valid] at h; exact h -- rw via change
    have hQ:4 ≤ i:= (Φ).adm m
    have hp:0+3 ≤ i:=(show (0:ℕ)+3≤ 4 by omega).trans hQ
    have he:Release.accepts ((X).span l i) (R.metals.p.profile l).supportExponent ((R.metals.p.profile i).supportExponent+2) L:= (R.b.tunes _ _ _ (Graces.feet hp R.b.clock) _ ((D).large _).need).1
    have hv:0<r:=zero_lt_one.trans ((P).fits.delayed _)
    have hi := p.up; have hZ:= p.has
    have hU:z=Mallow.probe (Pressure.betaF G q L):=by unfold z creditP Mallow.probe; rw [← hr, Real.rpow_neg hv.le,Real.rpow_ofNat,inv_pow]
    have hx:0<z:=hU.symm ▸ hi.probeT; have hy : D0=station (Pressure.betaF G q L):= hr ▸ rfl
    refine ⟨D0,⟨he,hk.fee _ _ (step_paid _ _), R.b.r, hk.supports m,hk.supports (m+1), ?_,p.rate,T.gains.Shears,T.gains.Saved,hk.paid,hk.spire⟩,?_,hx,?_,T.gains.largeG.scale _,T.gains.voices⟩
    · rw [hy]; exact hZ.shipping
    · let g:=radiusTab (Pressure.radiusB (Pressure.betaF G q L)) 1 (Mallow.probe (Pressure.betaF G q L)); change z+Real.exp z*z≤D0; rw [hy]; refine le_trans (b:=g+Real.exp g*g) ?_ hi.buy -- defeq
      have hh:z≤g:=by
         unfold g radiusTab;rw [← hU]; exact le_trans (by linarith only [hx] : z≤4*z) (le_add_of_nonneg_left (mul_nonneg (mul_nonneg (by positivity) (by unfold Extra.Multi.siteFactor; positivity)) hx.le))
      exact add_le_add hh (mul_le_mul (Real.exp_monotone hh) hh hx.le (Real.exp_pos _).le)
    rw [hy]; exact hi.shipping
lemma launches : Tendsto (timeEntry R) atTop atTop:= by
    have hv := Gauge.slopeConstant_pos T.gains.SimpleR
    exact tendsto_const_nhds.add_atTop (((P).S.divergent).const_mul_atTop hv) -- name
lemma slow (m:ℕ): timeEntry R m ≤ timeEntry R (m+1):= by
    have hv:= (Gauge.slopeConstant_pos T.gains.SimpleR).le; unfold timeEntry Calendar.hatBeta; rw [Schedule.scale_succ]; apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ hv
    have ht:0 ≤ Real.log (minutes R m):= Real.log_nonneg (one_minute ..)
    exact le_add_of_nonneg_right ht
lemma canopy (n:ℕ): ∀ᶠ m:ℕ in atTop,(changeA R n m)^4 ≤ mintOut R m:=by
    filter_upwards [hk.launches.eventually (polestar 1 zero_le_one (n*4) 0)] with m hm; rw [add_zero,one_mul] at hm
    have hp: minutes R m≤ timeEntry R m:=by unfold minutes; rw [Extra.Iteration.block_eq (A).B.valid]; exact (hk.presents m).much
    refine le_trans ?_ (show (timeEntry R m)^(n*4)≤ mintOut R m from hm)
    unfold changeA; rw [pow_mul]; exact pow_le_pow_left₀ (zero_le_one.trans (one_change ..)) (pow_le_pow_left₀ (zero_le_one.trans (one_minute ..)) hp _) _
lemma deploy {n:ℕ} :∀ᶠ u₀:ℕ in atTop,∀ m:ℕ,∀ t₁:ℝ,0<t₁→civic n * tariffLog T Θ m n t₁ ≤ changeA R u₀ m*t₁ ∧ civic n*(2*tariffLog T Θ m n t₁+2*tariffGas T m n t₁)≤changeA R u₀ m*t₁:=by
    let χ := Jams.billboardC n (t/2)
    have hθ: t≥0:=zero_le_one.trans Θ.wide
    have hc : 0 ≤ χ := mul_nonneg (Ray.bounty_nn _) (pow_nonneg (by positivity) _)
    have hr:0≤Θ.price:=Finset.sum_nonneg (fun i _=> Θ.hp i)
    let p:= 2*(Θ.price*2+1)
    let V:= civic n*(8*χ*p+8*χ)
    obtain ⟨M,hM⟩:= ((tendsto_pow_atTop_atTop_of_one_lt (show 1 < (3:ℝ) by norm_num)).eventually_ge_atTop V).exists
    filter_upwards [eventually_ge_atTop (M+1)] with u hu m t₁ ht
    let g:= minutes R m; let C:=changeA R u m
    have hg: (3:ℝ) ≤ g:= by unfold g minutes; exact_mod_cast (P).S.block_large m
    have hp: 1 ≤ g:= by linarith only [hg]
    have h_:0≤g:=zero_le_one.trans hp
    have hh : V*g ≤ C:= calc
       _ ≤ g^M*g:= mul_le_mul_of_nonneg_right (hM.trans (pow_le_pow_left₀ (by norm_num) hg M)) h_
       _ ≤ C:= pow_succ g M ▸ (pow_le_pow_right₀ hp hu)
    have hs :Luna.Frets.tempo Θ (R.rolls.L (j (m+1))) ≤ p*g:=by
         unfold g minutes Luna.Frets.tempo p; rw [Extra.Iteration.block_eq (A).B.valid]
         unfold g minutes at hp; rw [Extra.Iteration.block_eq (A).B.valid] at hp; nlinarith only [hp,mul_le_mul_of_nonneg_left hp hr]
    have hs0 : 0 ≤ Luna.Frets.tempo Θ (R.rolls.L (j (m+1))):=by unfold Luna.Frets.tempo; positivity
    have hvE:0≤ tariffLog T Θ m n t₁:= mul_nonneg (by norm_num) (mul_nonneg hc (mul_nonneg hs0 ht.le))
    have hvK : Real.sqrt ((P).clock.forcedAllowance m)≤ g:= by apply le_trans _ hp; exact (Real.sqrt_le_one).2 (Doors.stain_le _)
    have hE : tariffLog T Θ m n t₁ ≤ 4*(χ*(p*g*t₁)):= by unfold tariffLog singleBillE; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs ht.le) hc) (by norm_num)
    have hK : tariffGas T m n t₁ ≤4*(χ*(g*t₁)):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvK ht.le) hc) (by norm_num)
    have hn:0≤ tariffGas T m n t₁:=mul_nonneg (by norm_num) (mul_nonneg hc (mul_nonneg (Real.sqrt_nonneg _) ht.le))
    have hv : civic n*(2*tariffLog T Θ m n t₁+2*tariffGas T m n t₁)≤changeA R u m *t₁ :=by
       apply le_trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hE zero_le_two) (mul_le_mul_of_nonneg_left hK zero_le_two)) (civic_pos n|>.le)); apply le_trans (b:=V*g*t₁) _ (mul_le_mul_of_nonneg_right hh ht.le); apply le_of_eq; unfold V; ring
    exact ⟨le_trans (mul_le_mul_of_nonneg_left (by linarith only [hvE,hn]) (civic_pos _|>.le)) hv,hv⟩
end Sky
end YM.PhysicalNext.Repeat.Legato.Campaign
