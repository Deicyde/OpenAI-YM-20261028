import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Fault
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Finch
import YM.Push.GRID_APPROXIMATION.Major
/-! # Bolus library lift to all Molecule's integrals. Grain accepted room needed anew
 on drawing X, interpolation never weakens seeds at new R.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {Pt : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G Pt} {o : Target.Order G W} {R I : RG.Rep G f}
    {p μ C C' v M d r D K' : ℝ} {i : ℕ} {χ : Chi} {H : Cash W p μ L Q o C T R} (Ξ : Utopia H i v d r D χ)
section hold
variable (X : Coat T F) (I : RG.Rep G f)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {z:Air f G} {U:E→ Config G c} {V:E→ Directions G f} {Z:E→ Air f G} {x:E}
    (hX:X.x=p) (h : Clutch X z o.a R.beta d x i U V Z)
include h
lemma clutch_warp (he : Facing R I) : Clutch X (low R I • z) o.a I.beta d x i U V (fun i=> low R I • Z i) := by
  refine ⟨h.atV, he.pos',(by rw [h.birth]), h.pulse, fun y=> by rw [moving he,h.moving],h.price,fun i=> ?_, ?_⟩
  · simp_rw [moving he]; exact h.bud _
  rw [moving he]; exact h.patch
include H hX
omit I in
lemma fester (k : Molecule S): let f i := Polar.floating (vary X (U i)) o.a R W Q.table (Z i) (own k) Q.halo k
    f=ᶠ[𝓝 x] fun i=> ∏ l∈k, wraps T X R.beta o.a W Q.table 1 Q.halo R (own k) z U V Z l i := by
  intro f; filter_upwards [h.patch] with y hy
  have hv := h.moving y
  unfold f floating; rw [hv]; refine prod_congr rfl fun i _=>?_
  unfold wraps; rw [one_smul]; exact (plastic hy h.pulse).reeled (show Room Pt _ _ _ from (show Room _ _ _ X.x from hX.symm ▸ H.laws.data.room)) W Q.table (own k) Q.halo (show Intake Pt _ _ R from (show Intake _ _ X.x R from hX.symm ▸ H.laws.intake)) i (Z y)
end hold
variable (A : ℝ) (he : 0≤A) (h : StampPrice T o p d v χ i A)
local notation "u" => coin Ξ
include h he Ξ
lemma warpPriced : ∃ K : ℝ, 0 ≤ K ∧ ∃ s:ℝ, 0<s∧ ∀ {C':ℝ} (I : RG.Rep G f) (_: Cash W p μ L Q o C' T I) (a b : ℕ→ℝ) (t:ℝ), Equalized Q.table R I a b t→ t ≤ s → 0<t → ∃ f : Molecule S→ℝ, SumBudget f K ∧
    ∀ (F:Forest S.ratio) (X:Coat T F), X.width=o.K→X.x=p→X.manifest→ X.χ=χ →∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (z:Air _ G) (U:E→ Config G c) (V:E→ Directions G _) (Z:E→ Air _ G) (x:E), Mode U x i v→ Clutch X z o.a R.beta d x i U V Z→ ∀ k, Healthy (Pressure.temp X.x) (H.unionP k) X.V →
       let Y R y:= Polar.floating (vary X (U y)) o.a R W Q.table (Z y) (own k) Q.halo k
       let Q' y:= Polar.floating (vary X (U y)) o.a I W Q.table (low R I • Z y) (own k) Q.halo k
       Brush i (f k) 1 Q' x ∧Brush i (t*f k) 1 (Q'-Y R) x := by
  obtain ⟨K,hK,s,hs,hS⟩:=bolus Ξ A he h; let k:= ∑' i,u i
  refine ⟨Real.exp (3*3^i*(k+K)),Real.exp_nonneg _,min s 1,lt_min hs zero_lt_one,?_⟩; intro C' I H' a b t hp hv ht
  obtain ⟨f',hl,hT⟩:= hS I a b t hp (hv.trans (min_le_left ..))
  let a (i:Head S):= u i+f' i/t; let Y i:= 3*(3:ℝ)^‹ℕ›* a i
  let f (p:Molecule S):=∏ i∈p,Y i; have hf: SumBudget u k:= ⟨coin_pos Ξ,retail Ξ,le_rfl⟩
  refine ⟨f,insured _ _ t _ hf hl ht,?_⟩ -- metavar K output
  intro F X hx hR hw hχ E _ _ _ z U V Z x hU hC j Hx f₁ f₂
  let A₁:= wraps T X R.beta o.a W Q.table 1 Q.halo R (own j) z U V Z; let A₂:= wraps T X R.beta o.a W Q.table (low R I) Q.halo I (own j) z U V Z
  have hp₁ : f₁ R=ᶠ[𝓝 x] fun x=>∏ i∈j, A₁ i x := fester X (H:=H) hR hC j
  have hp₂ : f₂=ᶠ[𝓝 x] fun x=>∏ i∈j, A₂ i x:= by
    have h := fester X (H:=H') hR (clutch_warp X I hC hp.toFacing) j
    refine h.trans (Eventually.of_forall fun x=>?_); apply prod_congr rfl; intro i hi; unfold A₂ wraps; dsimp only; rw [one_smul,moving hp.toFacing]
  have hu k (hk:k∈j) : Healthy (Pressure.temp X.x) (H.supportP k) X.V:= Finset.disjoint_of_subset_left (subset_biUnion_of_mem _ hk) Hx
  obtain ⟨ha,hb⟩:= walks A₁ A₂ a x j ht.le (hv.trans (min_le_right ..)) (fun i hi=> (sung X Ξ z U V Z x hx hR hχ hw hU hC _ i (hu i hi)).climb (le_add_of_nonneg_right (div_nonneg (hl.1 i) ht.le)) le_rfl)
    (fun i hi=> (hT F X hx hR hw hχ E z U V Z x hU hC i (own j) (hu _ hi)).climb (show f' i ≤ t*a i from (by unfold a; rw [mul_add,mul_comm t (f' i/t), div_mul_cancel₀ (f' i) ht.ne']; exact le_add_of_nonneg_left (mul_nonneg ht.le (coin_pos Ξ i)))) le_rfl)
  refine ⟨ha.shimmy hp₂,hb.shimmy (by filter_upwards [hp₁,hp₂] with y hy hh using congr_arg₂ (fun x y:ℝ=>y-x) hy hh)⟩
end YM.PhysicalNext.Repeat.Alabaster
