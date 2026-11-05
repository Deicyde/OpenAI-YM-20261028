import YM.FullVolume.Luna.Stipe
import YM.FullVolume.Luna.Lumen
import YM.FullVolume.Mark.Prism
/-! Cost stencil: explicit pre-L exterior, true above.Lane retain coda. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Luna
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open YM.Source Planned.GuardedAtom Labels MergeProof MergeProof.Matric Extra.Histories Guard Jams
variable {G:Gauge}{n:Side}{i:ℕ}{R:Rep G n}{r v s t u q p z y x:ℝ}{k:ℕ→Support n} {F:Labels.Frame G i} {f:sun→ Pin F n}{a:F.Coeff}{Y:sun→Response G n}
variable {U V S T W κ:ℝ}
local notation "B"=> R.p
local notation "λ!"=> Motion.orbitCost F
local notation "Ψ"=> Local.turnCost (R.p.order) (R.p.power)
lemma divDia (ha:1 ≤ U)(hU:0 ≤ κ)(hq:0≤v)(hs:0 ≤ s)(hx:x≥0)(hd:y≥0)(hb: λ! *U*y ≤ s)(hy:s ≤ V)(h:LanternX G F B p q k f a (v*s+ λ! * U*y) (U*(v*(x/(Ψ*U))+y)) (κ*(y+2*(U*(v*(x/(Ψ*U))+y)))) Y (2*(U*(v*(x/(Ψ*U))+y)))) : LanternX G F B p q k f a ((v+1)*s) (v*x+V) (κ*(3*V+2*v*x)) Y (2*(v*x+V)):=by
   have hu:= Motion.orbitCost_one_le F; have h' := (xi_pos R.p)
   have hv:0<U:=zero_lt_one.trans_le ha
   have hΨ:0 < (Ψ):=zero_lt_one.trans_le h'; have hO: y≤V:=(le_mul_of_one_le_left hd (one_le_mul_of_one_le_of_one_le hu ha)).trans (hb.trans hy)
   let z:= U*(v*(x/(Ψ*U))+y); let m:=v*x+V
   have hV: U*y≤ V:= by rw [mul_assoc] at hb; exact (le_mul_of_one_le_left (mul_nonneg hv.le hd) hu).trans (hb.trans hy)
   have hZ:z≤ m:=by
      unfold z; rw [mul_add]; refine add_le_add ?_ hV; rw [show U*(v*(x/(Ψ*U)))= v*x/Ψ from (by field_simp)]; exact div_le_self (mul_nonneg hq hx) h'
   apply LanternX.enlarge h
   · rw [add_mul, one_mul]; linarith only [hb]
   · exact hZ
   · apply mul_le_mul_of_nonneg_left _ hU; exact (add_le_add hO (mul_le_mul_of_nonneg_left hZ zero_le_two)).trans_eq (by unfold m; ring)
   exact mul_le_mul_of_nonneg_left hZ zero_le_two
lemma divDis (ha:1 ≤ U)(hU:0 ≤ κ)(hq:0≤v)(hs:0 ≤ s)(hx:x≥0)(hd:y≥0)(hb: λ! *U*y ≤ s)(hy:s ≤ x)(h:LanternX G F B p q k f a (v*s+ λ! * U*y) (U*(v*(x/(Ψ*U))+y)) (κ*(y+2*(U*(v*(x/(Ψ*U))+y)))) Y (2*(U*(v*(x/(Ψ*U))+y)))) : LanternX G F B p q k f a ((v+1)*s) ((v+1)*x) (κ*((3+2*v)*x)) Y ((2*(v+1))*x):=by
   refine (divDia (R:=R) ha hU hq hs hx hd hb hy h).enlarge le_rfl (le_of_eq ?_) (le_of_eq ?_) (le_of_eq ?_)<;> ring
end YM.PhysicalNext.Repeat.Luna
