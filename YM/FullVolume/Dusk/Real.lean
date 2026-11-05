import YM.FullVolume.Dusk.Wince
import YM.FullVolume.Dusk.Gates
import YM.FullVolume.Literal
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
open YM.MergeProof
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp
open Pillars Bandage Pass Muse Contest Ovens
variable {R:Run G} (T:Campaign R)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
local notation "o"=> R.alloy.B.a.clock.bar
open Spirit Branch
open Boutique
open Extraction Extraction.Lease
variable (W: Pillars R T)
-- Diagram frame physical labels.Select.Stream REAL and branch.
namespace Face
open Filter Set Function MeasureTheory Metric Extraction Extraction.Lease Difference YM.FullVolume.Dusk Next.Extract MergeProof Cells Next.Rank
open Market
variable (H':T.Winter) (hx:Jams.Wild R.kit.shape R.alloy.delay)
local notation "C₁"=> centerF T W
variable (P:Face T W)(p:ℕ)
local notation "β"=> R.alloy.B.a.clock.bar
local notation "S'"=> P.V T W
local notation "R₀"=> R.family
include H' hx
open FullVolume Push.RelayDifference
variable (h : Tendsto (fun i=> evalV T W P p i) atTop (𝓝 R.alloy.B.a.clock.bar))
variable (hq : ∀ q:ℕ,q≠p→∀ n:ℕ, Courant (((centerF T W).score.mat n q)) (P.score.mat n q))
-- compact C.Lip for all Lease q.N once radius geometry fixed, needed for analytic comparison.
variable {n:ℕ}(K:Set (Points n))(v:Fin n→R.family.book.Token)(l:List (MotionIndex n))(hK:IsCompact K)(hk: K⊆ NoHit R.family.S p n)
include hK hk
omit h hq in
lemma biding : ∀ᶠ c in 𝓝[>] (0:ℝ), ∃ B:ℝ, 0 ≤ B ∧ ∀ᶠ N in atTop,∀ U:Face T W,
     |evalV T W U p N- β|≤ c → ∀ x:Positions n, tag (R.family.S.a N) x∈ K → ‖gKernel (V T W U) v l N p x‖ ≤ B:=by
   obtain ⟨r,hr,hR⟩:=Gaps.some R.family.S p hK hk
   filter_upwards [headlands T W H' hx p n v l r hr] with c ⟨B,hB,H⟩; refine ⟨B,hB,?_⟩
   filter_upwards [H] with N h U hv x hp; exact h U hv x (fun u w hu=> Gaps.gridSeparation _ _ rfl (hR _ hp) _ _ hu.symm)
lemma living : ∀ᶠ c in 𝓝[>] (0:ℝ), ∃ t B:ℝ, 0 < t ∧ 0 ≤ B ∧ ∀ᶠ N in atTop,∀ U:Face T W,
     |evalV T W U p N- β|≤ c → let s:=R.family.S; ∀ x y:Positions n, tag (s.a N) x∈ K → dist (tag (s.a N) y) (tag (s.a N) x) ≤ t →
       dist (gKernel (V T W U) v l N p y) (gKernel (V T W U) v l N p x) ≤ B * dist (tag (s.a N) y) (tag (s.a N) x) :=by
  obtain ⟨r,hr,hT⟩ := hK.exists_cthickening_subset_open (nohitOpen R.family.S p n) hk
  filter_upwards [eventually_all.mpr (fun j:MotionIndex n=> biding T W H' hx p _ v (j::l) hK.cthickening hT)] with c hC -- binder hK
  choose f hf hF using hC
  obtain ⟨b,hb,hB⟩:= ((eventually_ge_atTop (0:ℝ)).and (eventually_all.mpr fun j=>eventually_ge_atTop (f j))).exists
  refine ⟨r,b*Fintype.card (MotionIndex n),hr,mul_nonneg hb (Nat.cast_nonneg _),?_⟩
  filter_upwards [eventually_all.mpr hF] with i hi S₂ h₂ s x y hx hy
  let t:= s.a i; let F:=gKernel (V T W S₂) v l i p
  refine stroll (s.a_pos i) F _ _ _ _ hb hy (fun u j hu=> ?_)
  rw [dist_eq_norm,unique_units F (s.a_pos _) j u,norm_smul, Real.norm_of_nonneg (s.a_pos _).le]
  exact mul_le_mul_of_nonneg_left ((hi j S₂ h₂ u (mem_cthickening_of_dist_le _ _ _ _ hx hu)).trans (hB j)) (s.a_pos _).le
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.living
