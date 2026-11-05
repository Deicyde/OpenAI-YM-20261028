import YM.TraceExtension.Quince.Pride
import YM.TraceExtension.Quince.Unum
import YM.TraceExtension.Quince.Surrey
import YM.TraceExtension.Quince.Soil
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source Pressure
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Legato Malachite
open Mallow Lotus Planned.PrimaryIntegral295 PPX
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Bid Labels Extra.Iteration.Scales
-- requires Stage fixed beta large for ratios
variable {G:Gauge}
def cameo (A:Levels G)(m:ℕ):ℝ:=Real.sqrt (A.clock.monitor m)
lemma cameo_pos (A:Levels G)(m:ℕ): 0<cameo A m:= Real.sqrt_pos.mpr (Real.exp_pos _)
def Ordeal (T: Levels G) :Prop:= ∀ i,cameo T (i+1) ≤ 2*cameo T i
variable {M:Metals G}{D:Rolls M.p}{A:Alloy M D}{X:Factor A}{C:ℕ→ℝ}{K:Worth}(b:Bandage X C K)(Z:Bolt A) (n i:ℕ)
-- one ratio.G.Transfer.match.PP grant
lemma cameo_next : cameo A.B.a (i+1)= coinP G (D.L (A.B.a.clock.J (i+1))) (A.B.a.clock.hatBeta i):=by
    have h:=Push.PriceCompiler.beta_eq A.B.valid i; unfold cameo coinP bankP Push.AbsoluteSums.Delay.fineMonitor Calendar.monitor; rw[h]; rfl
section buy
variable {K:MapPrices}{s:Sheet G}{D:Rolls s}{Θ: Protection D}
def book_rise (V:Delays Θ):Prop:=∀ j x,V.betaEntry j≤x → coinP G (D.L j) x ≤ 2*Real.sqrt (meter x)
lemma rise_B (V:Delays Θ):∃ W:Delays Θ,DelayLe V W ∧ ∀ U:Delays Θ,DelayLe W U→book_rise U:=by
    have hp(j): ∀ᶠ x:ℝ in atTop, coinP G (D.L j) x ≤ 2 * Real.sqrt (meter x) := by
       filter_upwards [(loop_ratio (G.slopeConstant *Real.log ((D.L j).val:ℝ)) ((1:ℝ)/2)).eventually (ge_mem_nhds (show (1:ℝ)<2 by linarith))] with x hx
       have he:0 < meter x^((1:ℝ)/2):=Real.rpow_pos_of_pos (meter_pos _) _
       unfold coinP; simp only [Real.sqrt_eq_rpow]; exact (div_le_iff₀ he).1 hx
    obtain ⟨x,-,hx,H⟩:= collect_upper V.betaEntry _ hp
    exact ⟨{V with betaEntry:=x}, ⟨hx,le_rfl,le_rfl,le_rfl⟩,fun T ht j x hX=>H _ _ ((ht.beta j).trans hX)⟩
end buy
lemma ordered (hp: book_rise A.delay): Ordeal A.B.a:=fun i=> (cameo_next (A:=A) i).trans_le (hp _ _ (A.B.valid.pays i))
def bear (K:Worth)(j i:ℕ):= (10*K.K j)⁻¹
lemma bear_pos (K:Worth)(j i:ℕ):0<bear K j i:=by have h:=K.prices j; unfold bear; positivity
include b Z
variable {d m:ℕ}
local notation "T"=> A.B.a
local notation "L"=> A.B.a.S.block m
local notation "J"=> A.B.a.clock.J
set_option quotPrecheck false
local notation "α"=> Issue.trail Z
local notation "F"=> ((Labels.frames G).level d)
lemma tillP (hp:d+3 ≤ J m): 1≤ C (J (m+1)) ∧ 4*C (J (m+1))≤ puffs L:=by
   obtain ⟨hv,hε,hx,hK⟩:= (b.clock.fits α rfl m d ((Nat.le_add_right ..).trans hp))
   let X:= C (J (m+1)); let W:= K.K (J (m+1)); let Y:= K.K (J (m+1)+1); let ζ:=(A.B.a.params (m+1)).columns
   have hz:= (A.B.a.params (m+1)).columns_ge
   have h : X ≤ W:= le_trans (le_add_of_nonneg_right (mul_nonneg hε (zero_le_one.trans hz))) ((le_mul_of_one_le_right (le_trans hv (le_add_of_nonneg_right (mul_nonneg hε (zero_le_one.trans hz)))|>.trans' zero_le_one) (Motion.orbitCost_one_le _)).trans hK)
   have hf:W ≤ Y:=K.growth (Nat.le_succ _)
   have hg:X ≤ Y^6:=by have he:1≤Y:= hv.trans (h.trans hf); simpa using ((h.trans hf).trans (show Y ≤ Y^6 from by simpa using pow_le_pow_right₀ he (show 1≤6 by norm_num)))
   refine ⟨hv,(?_ :4*X≤100000*Y^6*(1+ζ)^2).trans (b.clock.bank m)⟩
   apply le_trans (mul_le_mul_of_nonneg_left hg (by norm_num)); have h':0≤Y^6:= zero_le_one.trans (hv.trans hg); nlinarith only [h', mul_le_mul_of_nonneg_right (one_le_pow₀ (show (1:ℝ)≤1+ζ from le_add_of_nonneg_right (zero_le_one.trans hz)) (n:=2)) h']
lemma till_gain (hp:d+3 ≤ J m) (hx:(0:ℝ) ≤ 1) : 2*C (J (m+1))*bear K (J (m+1)) (J m) ≤ 1/3:=by
   obtain ⟨hv,hε,hk,hK⟩:= b.clock.fits α rfl m d ((Nat.le_add_right ..).trans hp)
   let X:= C (J (m+1)); let W:= K.K (J (m+1)); let ζ:= (A.B.a.params (m+1)).columns; have hz:= (A.B.a.params (m+1)).columns_ge
   have h:X ≤ W:= le_trans (le_add_of_nonneg_right (mul_nonneg hε (zero_le_one.trans hz))) ((le_mul_of_one_le_right (le_trans hv (le_add_of_nonneg_right (mul_nonneg hε (zero_le_one.trans hz)))|>.trans' zero_le_one) (Motion.orbitCost_one_le _)).trans hK)
   have hq:0<W:=zero_lt_one.trans_le (hv.trans h); change 2* X * (10*W)⁻¹ ≤ 1/3; field_simp; nlinarith only [h,hq]
lemma spends (hp:d+3 ≤ J m)(V: Next.Free.Flight (J (m+1)) (J m))(h₀:4 ≤ J m) (hm:d≤ J (m+1)) {x y:ℝ} (h:Blend 2 x y)(v:(F).Coeff):
    let U:=Seal.donne (localSection G d) (sound G d) M.p.kernel.penalty_pos h₀ (Next.Foundations.valuation G d) V hm h
    (F).coeffSize v ≤ C (J (m+1)) * (F).coeffSize (U.leads (D.L (J (m+1))) v):=by
    intro U; let V':= V.legal
    have hf := Seal.cap_lead (localSection G d) (sound G d) M.p.kernel.penalty_pos h₀ (Next.Foundations.valuation G d) V hm h; let Y:= vowel F (D.L (J (m+1))) v
    have hQ := (b.shape _ _ (step_paid A.B.a m) (first_le A.B.valid m) _ hp).2 V.legal h₀ hm
    exact ((Work.G08.size_vowel ..).1.trans (hf.cost Y).2).trans (mul_le_mul_of_nonneg_right hQ (Work.G08.size_nonneg ..))
end YM.PhysicalNext.Repeat.Quince
