import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Term
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Blox
/-!
 # Finite cutoffs eventually on a compact curve, fixed P. Not yet uniform
 over all periods (not needed for Listing). Keep emitted turnout unchanged.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {s : Set ℝ} {A : BudgetPoint} {H Z : Listing G c}
lemma supHeight {n : Side} (B : BudgetPoint) : ∃ K : ℝ, 1 ≤ K ∧∀ (s o:Site n) (X : Support n) (f : Config G n→ℝ),B.Regular X f → ∀ p : ℝ,B.supBounds s X f p → B.supBounds o X f (K*p):= by
  let d := ((univ: Finset (Site n)) ×ˢ (univ: Finset (Site n))).sup fun i=> Lattice.separation i.1 i.2
  refine ⟨((1+(d:ℝ))^B.power)^B.order,one_le_pow₀ (one_le_pow₀ (by simp)),fun s o X f hv p hp=>?_⟩
  have he := Push.Local.bound_shift (sup_real hv|>.2 hp) (regular_mapped Complex.ofRealCLM hv) o
  have hf : separation s o≤d:= le_sup (f:=fun i:Site n × Site n=> separation i.1 i.2) (show (s,o)∈ (univ×ˢuniv) from mem_product.mpr ⟨mem_univ s,mem_univ o⟩)
  apply CouplingShape.sup_larger ((sup_real hv).1 he); gcongr; exact hp.1
lemma furlough (p:BudgetPoint) (h : ∀ i,(Z.reg i).support=(H.reg i).support) {w T : ℝ} {Y : Collection.Source G c} (hr : Collection.Local Z p Y w T):
   ∃ f:ℕ→ℝ,Summable f∧ ∀ i,p.supBounds (H.reg i).site (H.reg i).support (Y.logRead i) (f i):= by
  obtain ⟨a,b,hF⟩:=hr.cheap; obtain ⟨K,hK,hq⟩:= Meadow.supHeight (G:=G) (n:=c) p
  have hv := Boulevard.planetary hF fun i=> (b i).1
  refine ⟨fun i=>K *a i,hv.2.1.mul_left _,fun i=>?_⟩; rw [← h]; exact hq _ _ _ _ (hr.smooth i) _ (b i)
lemma night (P : ℕ→ ℝ→Prop) (h : IsCompact s) (he:∀ x∈s, ∃ Z ∈ 𝓝[s] x, ∀ᶠ k in atTop,∀ y∈Z, P k y) : ∀ᶠ k in atTop,∀ x∈s,P k x := by
  letI hc : CompactSpace s:= isCompact_iff_compactSpace.mp h
  choose u hu hy using fun x : s=> he x x.property
  let v (x:s):=(Subtype.val : s→ ℝ) ⁻¹' u x
  have hv (x:s): v x ∈ 𝓝 x := by
    change (Subtype.val : s→ℝ) ⁻¹' (u x) ∈ _; have h:= hu x; rw [← map_nhds_subtype_val] at h; exact h
  obtain ⟨t,ht,hZ⟩:= (isCompact_univ (X:=s)).elim_nhds_subcover v (fun x _=> hv x)
  filter_upwards [(eventually_all_finset t).mpr (fun k hk=> hy k)] with k hk x hx
  obtain ⟨p,hb⟩:= Set.mem_iUnion.mp (hZ (Set.mem_univ (⟨x,hx⟩:s)))
  obtain ⟨q,hq⟩:= Set.mem_iUnion.mp hb; exact hk p q x hq
lemma cashier {u : ℝ→ Collection.Source G c} (hf : ∀ i,(Z.reg i).support=(H.reg i).support) (p : BudgetPoint) (P : ℕ→ℕ→Prop) (h : IsCompact s)
    (he:∀ i,∀ᶠ k in atTop,¬P k i) (hm : Compared H p u s) (hu : ∀ x∈s,∃ w T,Collection.Local Z p (u x) w T) (a : ℝ) (ha : 0<a):
    ∀ᶠ k in atTop,∀ x∈s,Meadow.Budget p H.reg (fun i=> if P k i then (u x).logRead i else 0) a:= by
  have hy x (hx:x∈s) i : p.Regular (H.reg i).support ((u x).logRead i):= by rw [← hf]; obtain ⟨w,T,h'⟩:=hu x hx; exact h'.smooth i
  exact night _ h (fun i hi=> by obtain ⟨w,T,hB⟩:= hu i hi; exact exceeded p P hm hy hi (furlough p hf hB) he a ha)
end YM.PhysicalNext.Repeat.Meadow
