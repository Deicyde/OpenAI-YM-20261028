import YM.FullVolume.Luna.Berries
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
open YM.Source Planned.GuardedAtom Labels MergeProof MergeProof.Matric Extra.Histories Guard Jams
variable {G:Gauge}{n:Side}{ι:Type*}{B:BudgetPoint}{X:ι→Support n}{o:Site n}{p q r s t u v a b c:ℝ}
structure LanternX (G:Gauge){c:Side}{i:ℕ}(F:Labels.Frame G i)(B:BudgetPoint)(u v:ℝ)(k:ℕ→Support c)(f:sun→ Pin F c)(x:F.Coeff) (r s t:ℝ)(y:sun→ Response G c)(h:ℝ): Prop where
   axes : ∀ z:Rung,∀ η,Stripe z u η→ Extra.Histories.Motion.orbitCost F * F.coeffSize (mix z fun i=> (f i).1-x) ≤ η*r
   gifts: Wires B 0 mapSeat (fun i=> (f i).2.1) v (B.supportExponent+2) s
   joys : RollsUp B k (fun i=> (f i).2.2) v B.supportExponent t
   rays : RollsUp B id y v (B.supportExponent+2) h
variable {S:ℕ→Support n}{d k:ℕ}{F:Labels.Frame G d}{C: SectionData F}{Y:Hol G}{R:sun→RG.Rep G n}
local notation "zr"=> Config G n→ℂ
-- pieces retained & rebate Hart.Field and Frame
variable {X: ℕ→Support n} {M:sun→ Push.Local.Raw F n} {A:sun→ Coefficient F n}
variable (hk:∀ i,(R i).p=B)
variable (hO:∀ i,(R i).activities.forced=(R Jams.tip).activities.forced)
variable (ht:Local.Readable Y C B n u)
variable (hs:∀ i,(M i).seed=0)
variable (hh:∀ i, ∃ T: Berths (R i).p (R i).activities (fun j=> Local.joint C 0 (X j)), A i=mint T (M i) Y)
variable {xL:F.Coeff} (hf:∀ i,Graces.Effort C (R i) Y X (M i) xL u a b v)
variable (hp:0<a)
local notation "Φ"=> Local.factor Y C B.supportExponent u
local notation "λ!"=>Extra.Histories.Motion.orbitCost F
local notation "ξ!"=> Local.turnCost B.order B.power
set_option quotPrecheck false
local notation "U₀"=> R Jams.tip
local notation "B!"=> (Real.sqrt a)
local notation "R'"=> (R Jams.tip).activities
local notation "k!"=> Local.patch (U₀).activities
variable (p0:p≥1) (hq:p<q)(T:Tableau q k) (hY:q≤r)
variable {α μ σ:ℝ}
variable (hz:Wires B 0 X (fun i=>(M i).bulk) r (B.supportExponent+2) t) (hA:RollsUp B (Local.patch (R Jams.tip).activities) (fun i=>(M i).forced) p B.supportExponent α) (hK:league (Local.patch (R tip).activities) B.B (fun i=> (R i).activities.K) B.supportExponent p μ)
variable {Ψ C₁ D E:ℝ} (hT:∀ i,(R i).Lawful Ψ C₁ D E a) (hS:∀ i, Keeper (R i).p (R i).activities) (hP:∀ i, cart (hS i)=cart (hS Jams.tip))
-- omit A witness. arbitrary f' since real Gala.Formula. cut Kron before V.
include hp ht hz hA hK hT hk hf hs hO hP hY
lemma curt (hg:2≤q)(hh:p=q/2)(ht': Local.hitWidth B*μ ≤ 1)(F':sun→ Pin F n)(hpF:∀ t,F' t=gala (hS t) C Y (M t) X) (Z:sun→ Response G n)(hZ:∀ t,Z t= MergeProof.coda C Y 0 X (M t) (R t)):
   let y:= Local.factor Y C B.supportExponent u*(T.price*(v/(ξ! *Φ))+T.liftT r*t); let k:=Real.sqrt a
   LanternX G F B q p (Local.patch (R tip).activities) F' xL (T.price*b+T.liftT r*(λ! * (Φ*t))) y (α+Local.hitWidth B*μ*(2*y)) Z (2*y):=by
     intro vT k; let l i:= (hS i).supply (fun j=> Local.joint C 0 (X j))
     let u' i:= mint (l i) (M i) Y
     have hvb :∀ i,∃ T:Berths (R i).p (R i).activities (fun j=> Local.joint C 0 (X j)),u' i=mint T (M i) Y:=fun i=>⟨l i,rfl⟩
     have htA := confect hk hO ht hs hvb hf hp (p0:=by linarith only [hg,hh]) (by linarith) T hY hz hA hK hT hS hP ht'
     dsimp only at htA; rw [show (1-p/q)⁻¹=(2:ℝ) from (by rw [hh];have he:q>0:=(by linarith);field_simp;ring) ] at htA
     rw [show F'= _ from funext hpF,show Z=_ from funext hZ]; obtain ⟨u,h,l,z⟩:=htA; exact ⟨u,h,l,z⟩
end YM.PhysicalNext.Repeat.Luna
