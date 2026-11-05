import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Card
/-! # Exact balance between Anchored charges Hp and loc beacon of auxiliary views.
    All V. Orthogonality gives vanishing discrepancy on unpolluted. No Local purchase needed for α. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Trio
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C' F:Side} {j i m n W w r k l h:ℕ} {B : BudgetPoint} {Y:Stars→Side}
variable (Q:∀ i:Stars,(Y i).val=2*(w+i.val))
abbrev pad (i : Stars) : Track (Y i):= Slide.cognac (Q i).ge
def emerge (i : Stars) (x:Site (Y i)) (o:Site c) := o-wrap c (Slide.stage (pad Q i) x)
variable (z: ℕ) (fa:∀ i:Stars,Offer G (Y i)) (V:Config G c)
-- REQUIRE z≥w+4 so halos cover all journeys and then k≥z+(w+4)
lemma sway (i:Stars) (x:Site (Y i)) (o:Site c): separation o (emerge Q i x o) ≤ w+i.val:= by
  let u:=emerge Q i x o; rw [separation_comm]; have he:= Slide.village (C:=Y i) (w:=w+i.val) (Q i).ge u x
  have hv:Slide.sites (pad Q i) u x=o:= by unfold Slide.sites u emerge; abel
  change separation u o≤_; rw [← hv]; exact he
lemma patch (hp:w+4≤z) (i:Stars) (x:Site (Y i)) (o:Site c) (h:2*z≤k): neighbors z (emerge Q i x o)⊆ neighbors k o:= by
  let u:= emerge Q i x o
  intro j hj; apply (neighbors_mem ..).2; have hv:= (neighbors_mem ..).1 hj
  apply le_trans (separation_triangle o u _); have ht:= sway Q i x o; change separation o u≤_ at ht; change separation u j≤_ at hv; have hi:= i.isLt; omega
lemma hint (i:Stars) (hp:w+4≤z) (o:Site c) (h:Healthy B.threshold (neighbors z o) V): flags B.threshold (Slide.shape (pad Q i) o V) =∅ := by
  apply allFlag _ _ _ _ _ _ B.threshold_pos.le h; intro x; apply (neighbors_mem ..).2; apply (Slide.village _ _ x).trans
  have hh:= (Q i); have hx : i.val ≤ 4:= by have ht:=i.isLt; omega
  omega

variable (B)
def unit (i: Stars) (x:Site (Y i)) (o:Site c) (V:Config G c): ℝ:= fa i x (Slide.shape (pad Q i) o V)
def beacon (o:Site c) (V:Config G c):= ∑ i:Stars,Slide.ray i*∑ x:Site (Y i),unit Q fa i x o V
def unearned (o:Site c) (V:Config G c):= ∑ i:Stars, Slide.ray i*∑ x: Site (Y i),
    let s:=emerge Q i x o; masked B.threshold (neighbors z s) (unit Q fa i x s) V

lemma parade : ∑ i : Site c, masked B.threshold (neighbors z i) (beacon Q fa i) V= ∑ i:Site c, unearned B Q z fa i V:= by
  have ht i: masked B.threshold (neighbors z i) (beacon Q fa i) V=∑ j: Stars,Slide.ray j *∑ x:Site (Y j),masked B.threshold (neighbors z i) (unit Q fa j x i) V:= by
    by_cases he:Healthy B.threshold (neighbors z i) V; · simp [masked_eq,he,beacon]
    simp [masked_ne,he] -- formatting
  unfold unearned; simp_rw [ht]; rw [Finset.sum_comm]; conv_rhs => rw [Finset.sum_comm]
  apply sum_congr rfl; intro i _
  rw [← mul_sum,← mul_sum]; apply congr_arg; rw [sum_comm]; conv_rhs => rw [sum_comm]
  apply sum_congr rfl; intro y _
  symm; exact Equiv.sum_comp (Equiv.subRight (wrap c (Slide.stage (pad Q i) y))) (fun o=> masked B.threshold (neighbors z o) (unit Q fa i y o) V)

-- Pointwise cancellation in each healthy stack: ALL angular columns. classify.
variable (o:Site c) (hp:w+4≤z) (hr:2*r≤w) (hg:2*z≤ k) (hC:4*r+16≤c.val) (hU : Healthy B.threshold (neighbors k o) V)
local notation "C₀" => (charm w r)
include hp Q hU hg
lemma cash (i: Stars) (x: Site (Y i)) : masked B.threshold (neighbors z (emerge Q i x o)) (Trio.unit Q fa i x (emerge Q i x o)) V= unit Q fa i x (emerge Q i x o) V:= by
  apply masked_eq; exact hU.mono_left (patch Q z hp i x o hg)

variable (f₀ : Offer G c) (h₀:CompatibleP B r f₀ fa)
include hr h₀
lemma pricingAnchor (i : Stars) (x: Site (Y i)) :
    let p:= emerge Q i x o; let W:=Slide.shape (pad Q i) p V
    unit Q fa i x p V=fa i (Slide.ascended (Q i) x) W ∧ flags B.threshold W=∅ ∧
       Agrees (Lattice.box r) (expandAt (Slide.ascended (Q i) x) W) (Slide.thing (Slide.charm (w+i.val) r x) o V):= by
  intro p W; refine ⟨?_, Trio.hint Q z V i hp p (hU.mono_left (patch Q z hp i x o hg)), Slide.wandered (Q i) (hr.trans (Nat.le_add_right ..)) x o V⟩ -- order
  obtain ⟨v,hv⟩:= Slide.snap (Q i) x; rw [← hv, ← add_zero ((Slide.slant v).act x), show (Slide.slant v).act x+0=Lattice.affine (Slide.slant v) 0 x from rfl, ← h₀.moves]
  rw [show pull (Slide.slant v) 0 W=W from Slide.traps (Q i) v V p]; rfl
include hC
lemma cruising (hm:0<r) : unearned B Q z fa o V=f₀ o V:= by
  choose x hx using Slide.presents (Q 0) (Z:=r) (hr.trans (Nat.le_add_right ..)) hm -- order edit
  let P (p: Petals r):= Trio.unit Q fa (0:Stars) (x p) (emerge Q 0 (x p) o) V
  have hk i y:= pricingAnchor B Q z fa V o hp hr hg hU f₀ h₀ i y
  have hz (i:Stars) (x' : Site (Y i)): Trio.unit Q fa i x' (emerge Q i x' o) V=P (Slide.charm (w+i.val) r x'):= by
    let q:= charm (w+i.val) r x'; obtain ⟨hf,hQ,hJ⟩:= hk i x'; let y:=x q
    obtain ⟨ht,he,hh⟩:= hk 0 y; have hh' : charm (w+(0:Stars).val) r y=q:= hx q
    rw [hh'] at hh; change _=Trio.unit Q fa 0 y _ V; rw [hf,ht]; apply h₀.pace _ _ _ _ _ _ hQ he; exact fun i hi hj=>(hJ i hi hj).trans (hh i hi hj).symm
  change (∑ i:Stars,ray i*∑ y:Site (Y i),masked B.threshold _ _ V)= _
  simp_rw [cash B Q z fa V o hp hg hU,hz, Slide.collects _ hm hr Q P]
  let x' := x (Slide.rosy r); let p:=emerge Q 0 x' o; change Trio.unit Q fa 0 x' p V=_
  obtain ⟨hz,hk,he⟩:= hk 0 x'; rw [hz]; rw [show charm (w+(0:Stars).val) r x'=Slide.rosy r from hx _,Slide.self] at he
  obtain ⟨T,hT,hL⟩:= Slide.shifts V o r (by omega) B.threshold B.threshold_pos.le (hU.mono_left (show neighbors r o ⊆ neighbors k o from (fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (by omega)))))
  exact Eq.trans (h₀.forks 0 _ o _ T hk hT (fun i hi hj=> (he _ hi hj).trans (hL _ hi hj).symm)) (h₀.visitL o T V (readNear o (by omega) hL))
end YM.PhysicalNext.Repeat.Trio
