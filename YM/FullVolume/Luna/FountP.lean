import YM.FullVolume.Luna.PayX
import YM.FullVolume.Panel.Cable
/-! General geometric color tool for all views. Future Frame.Connection with Port.Br.K
 Do not hide choice of motion inside budget. Raw stamps chosen identically across kernel
 ties.H permits from canonical Witness mold.
-/
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
local notation "λ!"=> Motion.orbitCost F
local notation "Ω"=> R.p.supportExponent
open Motion
local notation "PS"=> Legato.Bandage
lemma noMotion {B:BudgetPoint}{k:ℕ→Support n}(h:0 ≤ t) (hz:0≤ v) (hr:0≤ r) (hp:0 ≤ s) (hq:1≤q): LanternX G F B p q k (fun _=>0) 0 v r t (fun _=>0) s:=by
   refine ⟨fun w η hw=> ?_,?_,?_,?_⟩
   · change _* F.coeffSize (mix w fun i=> (0:F.Coeff)-0) ≤ _; rw [show (fun i:sun=>(0:F.Coeff)-0)=(fun _=>0) from funext (fun i=>sub_self _),mix_z]; simp only [Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero,mul_zero]; exact mul_nonneg (stripe_pos hw) hz
   · have hh:Brill B (mapSeat (n:=n)) (fun _=>0) (B.supportExponent+2) r:=Local.sumBudget_mono (br_zero ..) (br_zero ..|>.1) le_rfl hr
     refine ⟨fun _=>0,hh,fun i=>le_rfl,fun i w η _=> ?_⟩; rw [mul_zero]; change B.supBounds (0:Site n) _ (mix w (fun i=>(0:Config G n→ℂ))) _; rw [mix_z];exact (regular0 ..).2
   · have hh:Brill B k (fun _=>0) (B.supportExponent) t:=Local.sumBudget_mono (br_zero ..) (br_zero ..|>.1) le_rfl h
     refine ⟨fun _=>0,hh,fun i U=>?_⟩;exact (Scout.still hq (0:ℂ)).enlarged norm_zero.le
   have hh:Brill B id (fun _ : Support n=>0) (B.supportExponent+2) s:=Local.sumBudget_mono (br_zero ..) (br_zero ..|>.1) le_rfl hp
   refine ⟨fun _=>0,hh,fun i U=>?_⟩;exact (Scout.still hq (0:ℂ)).enlarged norm_zero.le
lemma unitPin {B:BudgetPoint}{k:ℕ→Support n}(f:F.Coeff) (hq:1≤q): LanternX G F B p q k (fun _=>(f,0)) f 0 0 0 (fun _=>0) 0:=by
   obtain ⟨h,hp,hx,hs⟩:= noMotion (G:=G) (F:=F) (p:=p) (B:=B) (k:=k) (t:=0) le_rfl (v:=0) le_rfl (r:=0) le_rfl (s:=0) le_rfl hq; refine ⟨fun w η hw=> ?_ ,hp,hx,hs⟩
   rw [show mix w (fun _=>f-f)= (0:F.Coeff) from by rw [sub_self]; exact mix_z _]; simp only [Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero,mul_zero,le_refl]
end YM.PhysicalNext.Repeat.Luna
