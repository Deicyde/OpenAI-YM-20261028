import YM.FullVolume.Luna.Espir
import YM.FullVolume.Glitz.RockG
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Luna
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Next.Foundations Jams YM.Source Labels
open YM.Source Planned.GuardedAtom Labels -- Angles
open Guard MergeProof MergeProof.Matric Extra.Histories
open YM.PhysicalNext.Repeat.Roof
variable {G:Gauge}{n:Side}{ι:Type*}{B:BudgetPoint}{X:ℕ→Support n}{o:Site n}{p q r s t u v a b c:ℝ}
variable {i:ℕ}{R:Rep G n}{r v s t u q p z y x:ℝ}{k:ℕ→Support n} {F:Labels.Frame G i} {f:sun→ Pin F n}{a:F.Coeff}{Y:sun→Response G n}
variable {U V S T W:ℝ}
namespace LanternX
variable (h:LanternX G F B p q k f a r v s Y t)
include h in
lemma enlarge (hr:r ≤ U)(hv:v ≤ V)(hs:s ≤ S)(ht:t ≤ T):LanternX G F B p q k f a U V S Y T:=by
    obtain ⟨hp,hA,⟨u,hK,hX⟩,⟨p,hV,hY⟩⟩:=h; refine ⟨fun w η hw=> (hp w η hw).trans (mul_le_mul_of_nonneg_left hr (stripe_pos hw)), hA.leaner hv, ?_,?_⟩
    exact ⟨_,Local.sumBudget_mono hK hK.1 le_rfl hs,hX⟩
    exact ⟨_,Local.sumBudget_mono hV hV.1 le_rfl ht,hY⟩
variable {κ v':ℝ}
local notation "Φ'"=>Motion.orbitCost F
local notation "Ω"=>B.supportExponent+2
lemma rebateF {γ x E K:ℝ}(hv:LanternX G F B p q k f a (r +t*(Φ' * (u*E))) (u*(s+t*E)) (K+γ*(2*(u*(s+t*E)))) Y (2*(u*(s+t*E))))(hG:0 ≤ u)(h:t*E≤ x)(hg:0 ≤ κ)(hh:0≤γ)(ht:γ ≤κ)(hR:K ≤κ*x) : LanternX G F B p q k f a (r +Φ' *u*x) (u*(s+x)) (κ*(x+2*(u*(s+x)))) Y (2*(u*(s+x))) :=by
    have hh := budget_nonneg (hv.gifts.lamps.choose_spec.1)
    have he : u*(s+t*E) ≤ u*(s+x):=mul_le_mul_of_nonneg_left (add_le_add_right h s) hG
    have hf:=mul_le_mul_of_nonneg_left he (zero_le_two (α:=ℝ)); refine enlarge hv (add_le_add le_rfl ?_) he ?_ hf
    · rw [show t*(Φ' * (u*E))= Φ' * u*(t*E) by ring]; exact mul_le_mul_of_nonneg_left h (mul_nonneg (zero_le_one.trans (Motion.orbitCost_one_le F)) hG)
    rw [mul_add κ]; exact add_le_add hR (mul_le_mul ht hf (mul_nonneg zero_le_two hh) hg)
-- Combine read probes. Before stage if quorum q, trace all movement.
end LanternX
end YM.PhysicalNext.Repeat.Luna
