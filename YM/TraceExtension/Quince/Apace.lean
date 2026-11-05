import YM.TraceExtension.Quince.Nectar
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
variable {G:Gauge}{M:Metals G}{D:Rolls M.p}{A:Alloy M D}{X:Factor A}{C:ℕ→ℝ}{K:Worth}(b:Bandage X C K)(Z:Bolt A)
local notation "T"=> A.B.a
local notation "H"=> Issue.trail Z
local notation "J"=> A.B.a.clock.J
set_option quotPrecheck false
variable {m d i w n k:ℕ}
variable (hZ:Nest X Z)(hq:Skill b (bear K))(hG:G.Simple)(he:Ordeal A.B.a) (hx:d+3≤ A.B.a.clock.J m)
local notation "F"=> ((Labels.frames G).level d)
local notation "L"=> A.B.a.S.block i
local notation "P"=> C (J (i+1))
local notation "cX"=> (H).levels.clock
include he
include hZ hq hG b hx
-- ALL steps sufficiently large torus at target k. arbitrarily choose ξ.Bias payout P.Le
lemma pricey {k:ℕ} (hi:m≤ i)(hk:i<k): ∀ᶠ n:ℕ in atTop,∀ N:ℕ,k≤N→∀ (B : Duet (Issue.trail Z) F N n m k) (w t:ℝ),Duet.Woke B (hol G) K (localSection G d) w → (∀ i,B.atPoint i=0)→(∀ j,m≤j→ j≤k→ B.cost j+(F).coeffSize (B.voice j).x ≤ t/gainChart H k j)→0≤t →
    (F).coeffSize (B.voice i).x ≤ t/gainChart H k i / cameo A.B.a i → (F).coeffSize (B.voice (i+1)).x ≤ t/gainChart H k (i+1) / cameo A.B.a (i+1):=by
    let S:ℕ→ℝ:= fun i=>gainChart H k i; let y j:= cameo A.B.a j; have hS i:0<S i:=Real.exp_pos _
    let L':= A.B.a.S.block i
    have ht:d+3 ≤ A.B.a.clock.J i:=hx.trans (A.B.a.fits.mono hi)
    let P':= C (A.B.a.clock.J (i+1)); obtain ⟨hP,hb⟩:= tillP b Z ht; change 1 ≤ P' at hP; have hP':0<P':=zero_lt_one.trans_le hP
    let e:ℝ:= L'.val; let v:=Doors.rate L'; have hv: 0<v:=Doors.rate_pos _; have hv':0≤e:=Nat.cast_nonneg _
    let X:= S; let l:=(i+1); let I(i):=(X i)⁻¹/(y i)
    have ht0(j):0<y j:= cameo_pos ..
    have hg:S i=S l*puffs L':=by
        unfold S gainChart puffs l; rw [(H).S.scale_succ,Real.rpow_def_of_pos (by positivity), ← Real.exp_add]; congr 1; rw [show (H).S.block i=L' from rfl]; ring
    let p0:= puffs L'; have hp0:1≤p0:=Real.one_le_rpow (by exact_mod_cast L'.property) (by positivity)
    let H':= (S i)⁻¹+(P'*e^d + v)/(S l); have hH: 0<H':=by unfold H'; have hx:=hS l; have hp:=hS i;positivity
    let Y:= I l/(10*P'*H'); have hY: 0<Y:=by unfold Y I X; have hx:=hS l; have hk:=ht0 l;positivity
    let s:=sprite G (A.B.a.clock.hatBeta i) L' (bear K (J (i+1)) (J i)); have hs:0 ≤ s:=(sprite_pos _ (bear_pos ..)).le
    filter_upwards [rideE (m:=i) b Z hZ hG hq ht (bear_pos ..) Y hY] with n hp N hN B w t hB hu h' hK hL
    obtain ⟨h₀,h₁,h₂,hQ⟩:=hp N (hk.trans_le hN)
    let V:=Warehouse.flight H N i; let T0:=Seal.donne (localSection G d) (sound G d) M.p.kernel.penalty_pos h₀ (Next.Foundations.valuation G d) V h₁ h₂
    have hf:P' * I i ≤ (1/2)* I l:=by
       have hf(k): I k=(S k * y k)⁻¹:=by unfold I X; rw [div_eq_mul_inv,← mul_inv]
       rw [hf i,hf l, ← div_eq_mul_inv P',← div_eq_mul_inv (1/2:ℝ)]
       apply (div_le_div_iff₀ (mul_pos (hS i) (ht0 _)) (mul_pos (hS l) (ht0 _))).mpr
       have hj:y l ≤ 2*y i:= he i; have hz: P'*y l ≤ puffs L' *y i/2:=by
          apply (mul_le_mul_of_nonneg_left hj hP'.le).trans; nlinarith only [mul_le_mul_of_nonneg_right hb (ht0 i).le]
       rw [hg]; linarith only [mul_le_mul_of_nonneg_left hz (hS l).le]
    obtain ⟨hu₀,hr⟩:=hB.origin i hi hk.le; obtain ⟨hv₀,hξ⟩:= hB.origin l (hi.trans i.le_succ) hk
    rw [hu] at hu₀ hr hv₀ hξ
    have hx:= hB.transfers i hi hk; rw [hu, hu] at hx
    have hA:=hQ _ _ _ _ hu₀ hv₀ hr hξ hx; let U:=B.voice i; let V':=B.voice l; let X₀:= (F).coeffSize V'.x; let W₀:= (F).coeffSize U.x; let μ:= t/S (i+1); have hu0:= rem_nonneg hr; have hv0:=rem_nonneg hξ
    have hh: B.cost l+ X₀ ≤ t/S l:= h' l (hi.trans i.le_succ) hk; have hu:B.cost i+ W₀≤ t/S i:= h' i hi hk.le
    have hv: 0≤ X₀:=Work.G08.size_nonneg ..; have hu' :0≤ W₀:=Work.G08.size_nonneg ..
    let q:= T0.leads L' V'.x; have hlim : (F).coeffSize (U.x-q) ≤ s* (t/S l)+Y* (t*H'):=by
         apply hA.trans
         refine add_le_add (mul_le_mul_of_nonneg_left (LE.le.trans (add_le_add_left (Work.G08.size_core F _) _) ((add_comm ..).trans_le hh)) hs) (mul_le_mul_of_nonneg_left ?_ hY.le)
         have hx : B.cost l ≤ t/S l:=by linarith only [hv,hh]
         have hp:X₀ ≤ t/S l:=by linarith only [hh,hv0]
         have he:= ((Work.G08.size_vowel F L' ((F).core V'.x)).2.trans (mul_le_mul_of_nonneg_left (Work.G08.size_core .. |>.trans hp) (pow_nonneg hv' d)))
         have ht := hu
         apply (add_le_add (by linarith only [ht, hu'] : B.cost i ≤ t/S i) (add_le_add (mul_le_mul_of_nonneg_left he hP'.le) (mul_le_mul_of_nonneg_left hx ‹0<v›.le))).trans_eq; unfold H'; change t/S i+(P'*(e^d*_)+v*(t/S l))=_; ring
    have heq:L'= D.L (J (i+1)):=Push.PriceCompiler.block_eq A.B.valid i
    have hw: X₀ ≤ P'*(F).coeffSize q:=by unfold q; rw [heq]; exact spends b Z ht (show Next.Free.Flight (J (i+1)) (J i) from V) h₀ h₁ h₂ V'.x
    have hyc:s= bear K (J (i+1)) (J i)/(y l):=by unfold s sprite y l; rw [heq,cameo_next (A:=A)]
    have h0': 2*P'*bear K (J (i+1)) (J i) ≤ 1/3:=till_gain b Z ht zero_le_one
    have hω : P'* (s*(t/S l)) ≤ t*I l/3:=by
       rw[hyc]; unfold I X; have hp:=hS l; have hx:=ht0 l; calc
        _ ≤ (1/3)*(t*((S l)⁻¹/(y l))):=by
           have ht':P'*bear K (J (i+1)) (J i) ≤1/3:=by nlinarith only[h0']
           apply le_trans _ (mul_le_mul_of_nonneg_right ht' (by positivity)); ring_nf; exact le_rfl
        _ = _:=by ring
    have hh': P'* (Y*(t*H'))= (1/10)*(t*I l):=by unfold Y; field_simp
    have ht: t/S l / y l=t*I l:=by unfold I X; ring;
    have hL: W₀ ≤ t*I i:= (hL.trans_eq (show _= _ from (show t/S i / y i= t*I i by unfold I X;ring)))
    have hv:= Work.G08.size_triangle F q U.x; rw [Work.G08.size_sub_rev] at hv
    change X₀ ≤ t/S l/y l; rw [ht]; refine hw.trans ((mul_le_mul_of_nonneg_left (hv.trans (add_le_add hL hlim)) hP'.le).trans ?_); linarith only [hω, hh',mul_le_mul_of_nonneg_left hf hK,(show 0 ≤ t*I l by unfold I X; have hx:=hS l; have ht:=ht0 l;positivity)]
lemma ascend (h:k ≥ m): ∀ᶠ n:ℕ in atTop, ∀ N:ℕ,k≤N→ ∀ (B : Duet (Issue.trail Z) F N n m k) (w:ℝ), Duet.Woke B (hol G) K (localSection G d) w → (∀ i,B.atPoint i=0)→ 0 ≤ w → cameo T k * (F).coeffSize (B.voice k).x ≤ 4*(1+((H).levels.params k).columns)*w:=by
   filter_upwards [(Finset.Ico m k).eventually_all.mpr (fun j hj=> pricey b Z hZ hq hG he hx (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2)] with n hp N hN B w hB hΩ hw
   let x(i):=(F).coeffSize (B.voice i).x; let t:=4*(1+((H).levels.params k).columns)*w; have ht:0≤t:=by unfold t; positivity [(H).levels.params k|>.columns_ge];
   have hr(j:ℕ)(hi:m≤j)(he:j≤k): B.cost j+x j ≤ t/gainChart H k j:=by apply (le_div_iff₀ (Real.exp_pos _)).mpr; rw [mul_comm]; exact Work.G09.answer K (H) b.clock.room b.clock.bank N n d m k F (localSection G d) (hol G) B w hw hB j hi he
   have hQ(j:ℕ)(hi:m≤j): j≤k→ x j≤t/(gainChart H k j)/ cameo T j:=by
        induction j,hi using Nat.le_induction with
        | base=> intro h; simp only [x,hB.pairing,Frame.coeffSize, Pi.zero_apply,norm_zero,Finset.sum_const_zero]; unfold gainChart; positivity [cameo_pos (T) m]
        | succ j hj ih=> intro hk; exact hp _ (Finset.mem_Ico.mpr ⟨hj,hk⟩) _ hN B w _ hB hΩ hr ht (ih (by omega))
   have hv:= hQ k h le_rfl; simp only [gainChart,sub_self,mul_zero,Real.exp_zero,div_one] at hv; rw [mul_comm]; exact (le_div_iff₀ (cameo_pos _ k)).mp hv
end YM.PhysicalNext.Repeat.Quince
#print axioms YM.PhysicalNext.Repeat.Quince.ascend
