import YM.FullVolume.Tess.Shoe
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
local notation "Φ"=> R.alloy.B.a.clock
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I]
open Face Face.Economics
local notation "S"=> R.alloy.B.a.S
open MergeProof.Ribbons Next.Rank Next.Rank.Spindle
namespace Face
open Metric
open Ray
variable {W:Pillars R T}{p:ℕ}
local notation "P!"=>R.alloy.B.a
namespace Fan
variable (F:Fan T W p){n:ℕ}(V₀:Fin n→ R.family.book.Token)
local notation "δ"=> intervalClock R
local notation "a"=> R.family.S.a
variable (l:List (MotionIndex n))
open Difference
variable (H:T.Winter)(hx:Jams.Wild R.kit.shape R.alloy.delay)
variable {w:sun} {K:Set (Points n)} (h:IsCompact K) (hp:K⊆ NoHit R.alloy.B.a.S p n)
variable {v:ℕ→ℕ→ℝ}{Θ:Luna.Tableau T.width 300}(hk:Sky R T Θ v)
local notation "B!"=>Beam ℂ
abbrev tac (n:ℕ):ℝ:=8*n
/-- after radius restrictions and estimation omega True across Macro layouts. -/
structure Spines (w:sun)(U:ℕ→ℕ→Positions n→ Beam ℂ) (K:Set (Points n))(l:List (MotionIndex n))(L r:ℝ)(P:ℕ→ℝ) : Prop where
   old:Pledge F V₀ l w K L r
   launched j:0 ≤ P j
   ends : Summable P
   emits : ∀ᶠ j:ℕ in atTop,∀ N:ℕ,∀ (hn:j ≤ N)(x:Positions n),tag (R.family.S.a j) x∈K → ∀ s:sun, read ℂ s (U j N x)= swellK F V₀ w j N hn l s x
   earns : ∀ᶠ j in atTop,∀ N:ℕ,∀ (x y:Positions n),j < N→tag (a j) x∈K →tag (a (j+1)) y∈K→ dist (tag (a (j+1)) y) (tag (a j) x) ≤ tac n *a j→ dist (U (j+1) N y) (U j N x) ≤ P j
   views : ∀ᶠ j in atTop,∀ x:Positions n,tag (a j) x∈K→ CauchySeq (fun N:ℕ=> U j N x)
include H hx h hp hk
lemma astronomer : ∃ (L r:ℝ) (w:sun) (U:ℕ→ℕ→Positions n→ Beam ℂ) (g:ℕ→ℝ),0<w.val ∧ Spines F V₀ w U K l L r g:=by
    obtain ⟨C,L,r,w,b,U,hC,hΩ,hφ,ht⟩:=traceS F V₀ l h hp H hx hk -- order
    obtain ⟨M,hM,hB⟩:= hφ.payCost F V₀ l (tac n) (by unfold tac; positivity)
    obtain ⟨D,hD,hA⟩:= tideP b C hC (R:=R)
    obtain ⟨c,V,hc,hV,hU⟩:= Amp.Beam.ear D M hD hM (2*b)
    let t:sun:=⟨1/2,by norm_num [sun]⟩; have hz:0<t.val:=by unfold t; norm_num
    let d := scaleSun V w; let Z (j N:ℕ)(x:Positions n):= Amp.Beam.fit V (U j N x); let σ:= scaleSun t d
    let Y (j N:ℕ)(x:Positions n):= Amp.Beam.fit t (Z j N x)
    let P(j):=c/Real.sqrt (δ j); have hp :∀ i, 0 ≤ P i:= fun i=> div_nonneg hc (Real.sqrt_nonneg _)
    have HZ:= lightsFixed F V₀ l H hx h (show K⊆ NoHit _ p n from (by assumption)) w
    refine ⟨L,r,σ,Y,P,mul_pos (mul_pos hΩ hV) hz, hφ.restrict F V₀ l V|>.restrict F V₀ l t, hp, economySteps c, ?_, ?_,?_⟩
    · filter_upwards [ht] with j hj N hn x hx s; unfold Y Z; rw [fitL,fitL,(hj _ hn _ hx).2]; unfold swellK; rw [show ∀ v s, slash (v:sun).val v.property (s:sun)=scaleSun v s from fun _ _=> rfl]; simp_rw [← show ∀ (s:sun), scaleSun t s= slash t.val t.property s from fun _=> rfl,px];
      rw [show scaleSun (scaleSun t V) w=σ from (by ext; change _*(_*_)=(_*_)*_; ring)]
    · obtain ⟨m,hm⟩:= eventually_atTop.mp ht
      filter_upwards [hB,eventually_ge_atTop m] with j hj hi N x y hz hh hV' hy; let A:=U (j+1) N y-U j N x
      have hxV:= hm j hi N hz.le x hh; have hyV:= hm (j+1) (hi.trans j.le_succ) N hz y hV'
      have hr:‖A‖≤ D*(δ j)^(2*b):= (norm_sub_le ..).trans ((add_le_add hyV.1 hxV.1).trans (hA j))
      have hX : ‖Amp.Beam.fit V A‖ ≤ P j:= hU _ A (one_clock j) hr (fun s=>by
            unfold A; rw [map_sub,hyV.2,hxV.2,← dist_eq_norm]; exact hj _ hz _ _ hh hV' hy s)
      unfold Y;rw [dist_eq_norm,← fitD]; apply (fitN ..).trans; unfold Z; rw [←fitD]; exact hX
    filter_upwards [ht,HZ] with j hj hZ x hx'; apply dampBound (by norm_num [t]) (C:=C*δ j^b) ?_ ?_
    · filter_upwards [eventually_ge_atTop j] with N hn; exact (fitN ..).trans (hj N hn x hx').1
    intro s; refine Rising.cauchy_copy (hZ x hx' (scaleSun V s)) ?_
    filter_upwards [eventually_ge_atTop j] with N hn; rw [dif_pos hn]; unfold Z; rw [fitL,(hj N hn x hx').2]
end Fan
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Fan.astronomer
