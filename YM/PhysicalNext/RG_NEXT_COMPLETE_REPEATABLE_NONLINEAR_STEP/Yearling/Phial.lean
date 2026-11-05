import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter

/-!
 # Curve drift consumer with Compounded. The *actual* mask convention and Offers.
 Need not assume Majorizes out of beta history.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Yearling
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet March Hues
open Gas Ursell Trees Multiple Alabaster Match Greenbelt Letter
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Geo Ovens RG.Shoot Next.Scheduling
open Push.BetaTransport
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R : ℝ → RG.Rep G f} {U : RG.Rep G f}
    {x μ C v e d D s : ℝ} {i j n m : ℕ} {χ : Chi}

lemma feathered {X : Listing G c} {q : BudgetPoint} {p: ℝ→ Collection.Source G c} {w : Set ℝ}
    (h : ∀ x∈w,∀ t> (0:ℝ),∀ᶠ y in 𝓝[w] x, deviation q (X.read (p x)) (X.read (p y)) t)
    (he : ∀ x∈w,∃ f g:ℕ→ℝ,Summable f ∧ Summable g ∧ Majorizes q f g (X.read (p x))) : Compared X q p w:= by
  constructor
  · intro x hx; constructor
    · intro i t ht; filter_upwards [h _ hx t ht] with y h
      obtain ⟨c,d,hf,hg,hC,hD⟩:= h; refine ⟨ht.le,fun z hz l hl hq=> ?_⟩; exact ((hf i).2 z hz l hl hq).trans (budget_single (budget_unweighted (fun i=> (hf i).1) hC) i)
    intro i t ht; filter_upwards [h _ hx t ht] with y h U
    obtain ⟨c,d,hf,hg,hC,hD⟩:= h; exact ((hg i).2 U).trans (budget_single (budget_unweighted (fun i=> (hg i).1) hD) i)
  intro x hx u hu
  obtain ⟨r,hr,H⟩:= extraction_forall_of_eventually fun j:ℕ=> hu.eventually (h x hx ((1/2:ℝ)^j) (by positivity))
  obtain ⟨f,g,hf,hg,hM⟩:= he x hx
  choose c d hc hd hC hD using H
  obtain ⟨F,hF,h'⟩:= collect_margin summable_geometric_two (fun i j=> (hc i j).1) hC
  obtain ⟨G,hG,h''⟩:= collect_margin summable_geometric_two (fun i j=> (hd i j).1) hD
  let E:=f+F; let D:=g+G
  have he' i : 0 ≤ F i:=(hc 0 i).1.trans (hF 0 i); have hd' i : 0 ≤ G i:=(hd 0 i).1.trans (hG 0 i)
  have hE : Majorizes q E D (X.read (p x)) :=⟨fun i=> VerifiedReset.sup_le (hM.1 i) (le_add_of_nonneg_right (he' i)),fun i=> ⟨(hM.2 i).1.trans (le_add_of_nonneg_right (hd' i)),fun y=> ((hM.2 i).2 y).trans (le_add_of_nonneg_right (hd' i))⟩⟩
  refine ⟨r,E,D,hr.tendsto_atTop,hf.add (budget_unweighted he' h').2.1,hg.add (budget_unweighted hd' h'').2.1,hE,Eventually.of_forall fun j=> ⟨fun i=> ⟨(hE.1 i).1,?_⟩,fun i=>⟨(hE.2 i).1,?_⟩⟩⟩
  · intro u hv l hl hp
    have hq:= (hM.1 i).2 u hv l hl hp; have hz:= (hc j i).2 u hv l hl hp
    have h : ∀ x y:ℝ, ‖y‖≤‖x‖+‖x-y‖:= fun x y=> by nth_rw 1 [← sub_sub_cancel x y]; exact norm_sub_le ..
    apply (h _ _).trans; exact add_le_add hq (hz.trans (hF j i))
  intro z
  have hp : ∀ x y:ℝ, ‖y‖≤‖x‖+‖x-y‖:= fun x y=> by nth_rw 1 [← sub_sub_cancel x y]; exact norm_sub_le ..
  exact (hp ..).trans (add_le_add ((hM.2 _).2 z) (((hd j i).2 z).trans (hG j i)))

lemma blue (V:ChartRatio G) (hV:LocalRatio V) {p:BudgetPoint} {s:Set ℝ} (hc : Curve p R s) (hp : ∀ x∈s,(R x).p=p)
    {x : ℝ} (hx:x∈s) (h : ∀ y∈s,Facing (R x) (R y)) (t:ℝ) (hy:0<t) : ∀ᶠ y in 𝓝[s] x, ∃ a b:ℕ→ℝ, Equalized V (R x) (R y) a b t:= by
  let f y:= (R y).beta; have he:Tendsto f (𝓝[s] x) (𝓝 (f x)):= hc.beta x hx
  have hβ:0 < f x:= (h x hx).pos
  have hX:0 < V.scale:=hV.scale; have hB:0 < measure_g V (f x):= by unfold measure_g gStep; positivity
  have hG:= he.sqrt; have hg:= hG.inv₀ (Real.sqrt_pos.mpr hβ).ne'
  have hM : Tendsto (fun y=>Real.log (measure_g V (f y))) (𝓝[s] x) (𝓝 (Real.log (measure_g V (f x)))):= (((hg.const_mul _).pow _).const_mul _).log hB.ne'
  have hk := (he.inv₀ hβ.ne')
  have he' : Tendsto (fun y=>low (R x) (R y) ^ 2) (𝓝[s] x) (𝓝 1) := by
    have ht : Tendsto (fun y=> low (R x) (R y) ^2) (𝓝[s] x) (𝓝 (low (R x) (R x)^2)):= ((hg.inv₀ (Fare.gS _ hβ).1.ne').const_mul _).pow _
    convert ht using 2; unfold Alabaster.low; rw [mul_inv_cancel₀ (show gStep (R x).beta≠0 from (Fare.gS _ hβ).1.ne'), one_pow]
  have hh {Z:ℝ} {G:ℝ→ℝ} (h:Tendsto G (𝓝[s] x) (𝓝 Z)) : ∀ᶠ y in 𝓝[s] x,|Z-G y|≤t:= (h.eventually (Metric.ball_mem_nhds Z hy)).mono (fun i hi=> by rw [abs_sub_comm]; exact (Metric.mem_ball.mp hi).le)
  filter_upwards [self_mem_nhdsWithin,hc.continuous t hy _ hx,hh he,hh hM,hh he'] with y hy' ht hB hF hL
  obtain ⟨c,d,hc,hd,hC,hD⟩:=ht; refine ⟨c,d,h y hy',?_,(fun i U=> (hd i).2 U),budget_unweighted (fun i=> (hc i).1) hC, budget_unweighted (fun i=> (hd i).1) hD,by rw [abs_sub_comm]; exact hL,hB,hF⟩
  intro i U; unfold Activities.regularOccurrence; rw [hp _ hx,hp _ hy',← (h y hy').reg]
  by_cases he : Healthy p.threshold ((R x).activities.reg i).support U
  · rw [masked_eq _ _ _ _ he, masked_eq _ _ _ _ he]; exact (hc i).2 U he [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ he,sub_self,abs_zero]; exact (hc i).1
end YM.PhysicalNext.Repeat.Yearling
