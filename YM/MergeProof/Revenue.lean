import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mercury
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Leibniz
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.MergeProof.Buys
import YM.MergeProof.Permit
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Courier
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Blueprint
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsHood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Eco
import YM.SectorNext.RECONNECTED_LOCALITY.Missing

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}

open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
open MergeProof  MergeProof.Menu Extra.Multi Merge
variable (Q:ConnectedActivityE6.Target G P)
-- make simplified expense powers at step.

def station (x:ℝ):ℝ := x^(-(1:ℝ))
def probe (x:ℝ):ℝ:= x^(-(2:ℝ))
variable (L:Side) (N:ℕ) (μ : ℝ)

def radiusTab (K N:ℕ)(a:ℝ):= (N*Extra.Multi.siteFactor K*a+4*a)
structure Tariff (Q:ConnectedActivityE6.Target G P)(L:Side)(N:ℕ)(μ x:ℝ): Prop where
   nonneg : 0≤ station (betaF G x L)
   probeT : 0 < probe (betaF G x L)
   small : probe (betaF G x L)≤1
   shipping : Palette.shipPrice L Q x N (station (betaF G x L))
   buy : let k:=radiusTab (radiusB (betaF G x L)) N (probe (betaF G x L)); k+Real.exp k*k ≤ station (betaF G x L)
   -- uses radiusB x/current after K
   lodging : ((radiusB x+radiusB x+1:ℕ):ℝ)^4*(straw μ L G x + N*siteFactor (radiusB x)*probe (betaF G x L)) ≤ 1/2
   credits : Real.exp (straw μ L G x+ N*siteFactor (radiusB x)*probe (betaF G x L))-1 ≤ 1
lemma warmLane {r: ℝ→ℕ} (h:Rate G L 0 (fun i=>(r i:ℝ))):Rate G L 0 (fun i=> siteFactor (r i)):=by
   have hx := (((((h.mul_left 16).add (Rate.const 9)).mul_left 2).pow 4).mul_left (Real.exp 1)); simpa only [siteFactor,zero_mul] using! hx
variable (h:0<μ)
include h
set_option maxRecDepth 4096 in
lemma thaws : ∀ᶠ x in atTop,Tariff Q L N μ x:=by
   let A x:= radiusB x; let a x:= betaF G x L; let B x:=radiusB (a x); let f x:=station (a x); let y x:=probe (a x); let k x:=radiusTab (B x) N (y x)
   let r x:=siteFactor (A x); let g x:= ((N:ℝ)*r x); let z x:= straw μ L G x+g x*y x
   have heG:Rate G L (-2) z:= (infuso L (G:=G) 2 (μ/4) (1/4) (by positivity) (by norm_num) (-2)).add (by simpa only [zero_add] using! (((warmLane L Rate.radius_price).mul_left (N:ℝ)).mul (show Rate G L (-2) y from Rate.power)))
   have hS:Rate G L (0:ℝ) (fun i=>(B i:ℝ)):=by
      have hi:= Rate.radius_price (L:=L) (G:=G)|>.mul_left 2 -- current to pressure
      have hh:= AbsoluteSums.Fees.horizons G L 0 (ε:=Q.ε) Q.usable (le_refl 0) (show 2*Q.ε < P.top.supportExponent from by linarith [Q.grants.1,Q.usable])
      refine hi.compare (hh.mono fun x hx=> ((by
        have hr: (B x:ℝ)≤ 2*(radiusB x:ℝ):=by exact_mod_cast hx.2.1
        change |(B x:ℝ)|≤|2*(radiusB x:ℝ)|; rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (by positivity)]; exact hr)))
   have hK:Rate G L (-2) k:=by
      have H:= show Rate G L (-2) y from Rate.power; have hp:= ((warmLane L hS).mul_left (N:ℝ)).mul H; rw [zero_add] at hp; exact hp.add (H.mul_left 4)
   have hV:Rate G L (-2) (fun i=>k i+Real.exp 1*k i):= hK.add (hK.mul_left _)
   have hu: Rate G L (-2) (fun i=>((A i+A i+1:ℕ):ℝ)^4 * z i):=by
      have hx:=Rate.radius_price (L:=L) (G:=G); simpa only [zero_mul,zero_add,Nat.cast_add,Nat.cast_one] using! ((((hx.add hx).add (Rate.const 1)).pow 4).mul heG)
   let C := Footprint.preCost (Q.halo+5); let E:= Real.exp ((Q.relative+1)*C); let D:= Real.exp (Q.relative*C)
   have hd: Rate G L (-1) (fun i=>g i*(E*f i)/D):=by
      simp_rw [div_eq_mul_inv]; simpa only [zero_add] using! (((((warmLane (G:=G) L Rate.radius_price).mul_left (N:ℝ)).mul ((show Rate G L (-1) f from Rate.power).mul_left E)).mul_right D⁻¹))
   have hy:0<Real.log 2:=Real.log_pos (by norm_num)
   filter_upwards [Delay.shift_pos G L,(show Rate G L (-2) y from Rate.power).below (by norm_num) 1 one_pos,
      hd Q.rate (by linarith only [Q.start]), hK.below (by norm_num) _ one_pos,hV _ (by norm_num : -(2:ℝ)< -1),hu.below (by norm_num) (1/2) (by norm_num),heG.below (by norm_num) _ hy] with x hx hb hf hk hv ha he
   have hp:0<f x:=Real.rpow_pos_of_pos hx _; have hh:0<y x:=Real.rpow_pos_of_pos hx _; refine ⟨hp.le,hh,(le_abs_self _).trans hb,?_,?_,(le_abs_self _).trans ha,?_⟩
   · unfold Palette.shipPrice Daisy.ribbon; change g x*(E*f x) ≤ Q.goal L x * D; exact (div_le_iff₀ (show 0<D from Real.exp_pos _)).1 ((le_abs_self _).trans hf)
   · have hz : 0 ≤ k x :=by unfold k radiusTab siteFactor; positivity
     exact (add_le_add_right (mul_le_mul_of_nonneg_right (Real.exp_monotone ((le_abs_self _).trans hk)) hz) (k x)).trans ((le_abs_self _).trans hv)
   have ht : Real.exp (z x) ≤ 2:= (Real.exp_monotone ((le_abs_self _).trans he)).trans_eq (Real.exp_log (by norm_num)); change Real.exp (z x)-1≤ 1; linarith
end YM.PhysicalNext.Repeat.Mallow
