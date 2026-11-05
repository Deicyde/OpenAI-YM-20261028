import YM.TraceExtension.Quince.Soot
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
variable {G:Gauge}
variable {M:Metals G}{D:Rolls M.p}{A:Alloy M D}{X:Factor A}{C:ℕ→ℝ}{K:Bid.Worth}(b:Bandage X C K)(Z:Bolt A)
open Bid Labels
set_option quotPrecheck false
local notation "H" => Issue.trail Z
variable {m d:ℕ}{p:ℕ→ℕ→ℝ}
local notation "F"=> ((Labels.frames G).level d)
local notation "B₁"=> A.B.a.budget m
local notation "L"=> A.B.a.S.block m
local notation "β"=> A.B.a.clock.hatBeta m
local notation "J"=> A.B.a.clock.J
local notation "Φ"=> sprite G β L (p (J (m+1)) (J m))
-- Uniform over all voices. (one-period-large caveat expires separately in B.)
lemma rideE (h:Nest X Z)(hG:G.Simple)(hp:Skill b p)(hk:d+3 ≤ A.B.a.clock.J m) (hy:0<p (J (m+1)) (J m)):
    ∀ (ε:ℝ),0<ε → ∀ᶠ n:ℕ in atTop, ∀ N:ℕ,m<N→ let P':=Warehouse.flight H N m
    ∃ (h:4≤ (H).levels.clock.J m)(hp:d ≤ (H).levels.clock.J (m+1))(hx: PPX.Blend 2 (A.B.a.budget (m+1)).threshold (A.B.a.budget m).threshold), let V:=Seal.donne _ (sound G d) M.p.kernel.penalty_pos h (Next.Foundations.valuation G d) P' hp hx; let l:=localSection G d
      ∀ (P:Coefficient F ((H).S.side m n))(Q:Coefficient F ((H).S.side (m+1) n))(u v:ℝ), P.Format 0 (hol G) ((H).rep N n m)→ Q.Format 0 (hol G) ((H).rep N n (m+1))→ P.remBound 0 ((H).rep N n m) (Push.Local.kappa H m) u → Q.remBound 0 ((H).rep N n (m+1)) (Push.Local.kappa H (m+1)) v →P.density 0 l ((H).rep N n m)=blast H N n m d (Q.density 0 l ((H).rep N n (m+1))) →
       (F).coeffSize (P.x - V.leads L Q.x) ≤ Φ*((F).coeffSize ((F).core Q.x)+v) + ε*(u + (C (J (m+1))*(F).coeffSize (vowel F L ((F).core Q.x))+Doors.rate L*v)):=by
   intro ε hε
   let a:= fineK («H»:=hol G) F; let P:= A.B.a.budget m
   obtain ⟨k,hκ⟩:∃ k:ℕ,a*Real.exp (-P.supportExponent*k) ≤ ε:=by
       let y(x:ℕ):= -(P.supportExponent*x); have ht: Tendsto y atTop atBot:= tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop P.exponent_pos)
       obtain ⟨k,h⟩:= ((((show Tendsto (fun x=>Real.exp (y x)) atTop (𝓝 0) from Real.tendsto_exp_atBot.comp ht)).const_mul a).eventually (ge_mem_nhds (show a*0<ε from by simpa using hε))).exists
       exact ⟨k,by simpa only[neg_mul] using h⟩
   have hu:Tendsto (fun n=> (A.B.a.S.side m n).val) atTop atTop:=by apply StrictMono.tendsto_atTop; intro x y hy; exact mul_lt_mul_of_pos_right (A.B.a.S.period_strict hy) (A.B.a.S.denominator m |>.property)
   filter_upwards [hu.eventually (eventually_gt_atTop (20*(radiusD β+Heir.reach β+1))), hu.eventually (eventually_gt_atTop (10*(k*(4*P.B+2)+2*P.B)))] with n hs hf N hN
   obtain ⟨h₁,h₂,hQ,hW⟩:= Cashbox b Z h hG hp hN hk hs
   intro P'; refine ⟨h₁,h₂,hQ,?_⟩; intro V l U W t v hu hv hK hP hx
   have hy : (H).Conv N n m:= Z.choice.represents N n m hN.le
   have hm: (H).Selected:= Z.choice
   have hb:= lively (A:=A) b.clock (d:=d) (show d ≤ J m from Nat.le_of_add_right_le hk) (n:=n)
   let Y:= C (J (m+1))*(F).coeffSize (vowel F L ((F).core W.x))+Doors.rate L*v
   obtain ⟨X,hα,hD,hH,hΩ⟩:=Surrey.include_one l H N n m (hol G) hm hN hW (sprite_pos _ ‹0 < p (J (m+1)) (J m)›|>.le) (Doors.rate_pos _ |>.le) W hv hP
   have hz:= unique_part (hy.vac.symm ▸ hb) hu hα hK hD (hx.trans hH.symm) k (hy.vac.symm ▸ hf)
   rw [hy.vac] at hz
   have he : Real.exp (-P.supportExponent*k) * a ≤ ε:= by rw [mul_comm]; exact hκ
   rw [show U.x-V.leads L W.x=(X.x-V.leads L W.x)+(U.x-X.x) from by abel]; apply (Extra.Histories.Size.add F _ _).trans; apply add_le_add hΩ (hz.trans _); rw[← mul_assoc]; exact mul_le_mul_of_nonneg_right hκ (add_nonneg (rem_nonneg hK) (rem_nonneg hD))
end YM.PhysicalNext.Repeat.Quince
#print axioms YM.PhysicalNext.Repeat.Quince.rideE
