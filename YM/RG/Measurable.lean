import YM.RG.Patch

/-!
# Pieces of the exact kernel are Borel

On the two interior minimizing branches the selected points are continuous
(under uniqueness, a separate substantial obligation). Fallback is defined
Borel, not assumed smooth. Use the actual finite likelihoods, normalized at
fixed fields.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG

open Set MeasureTheory Filter Lattice Wilson
open scoped Topology Matrix.Norms.Frobenius

/-- Compact target: unique fiber of a closed relation controls all choices. -/
theorem minArg_cont {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (f : X → Y) (M : Set (X × Y)) (hf : ∀ x, (x,f x) ∈ M)
    (hclosed : IsClosed M) (a : X) (ha : ∃! y, (a,y) ∈ M) : ContinuousAt f a := by
  apply tendsto_nhds.mpr
  intro V h hv
  let D := Prod.fst '' (M ∩ Prod.snd ⁻¹' Vᶜ)
  have hd : IsClosed D := isClosedMap_fst_of_compactSpace _ (hclosed.inter (h.isClosed_compl.preimage continuous_snd))
  have hi : a ∈ Dᶜ := by
    rintro ⟨⟨b,y⟩, ⟨hy,hc⟩, ee⟩
    change b=a at ee
    subst b
    exact hc (ha.unique (hf a) hy ▸ hv)
  apply mem_of_superset (hd.isOpen_compl.mem_nhds hi)
  intro x hx
  change f x ∈ V
  by_contra! H
  exact hx ⟨(x,f x),⟨hf x,H⟩,rfl⟩

namespace Patch

variable (P : Patch) {C : KernelChoices} {G : Gauge}

theorem min_closed : IsClosed {z : CoverConfig G × P.Frame G | P.minimizing z.1 z.2} := by
  rw [show {z : CoverConfig G × P.Frame G | _} =
      {z : CoverConfig G × P.Frame G | z.2 P.center = 1} ∩ ⋂ y : {h' : P.Frame G // h' P.center = 1},
        {z : CoverConfig G × P.Frame G | P.score z.1 z.2 ≤ P.score z.1 y} by
    ext; simp [Patch.minimizing]]
  exact (isClosed_eq ((continuous_apply P.center).comp continuous_snd) continuous_const).inter
    (isClosed_iInter fun y => isClosed_le P.score_cont (by fun_prop))

theorem selected_cont (h : P.Branches C G) : ContinuousOn P.selected {u : CoverConfig G | P.usesMin C u} := by
  intro x hx
  exact (minArg_cont P.selected {z : CoverConfig G × P.Frame G | P.minimizing z.1 z.2} (fun y ↦ (P.min_exists y).choose_spec) P.min_closed x
    (h.frame_unique x hx)).continuousWithinAt

theorem best_cont (h : P.Branches C G) : ContinuousOn P.best {Y : P.Connector G | P.usesBest C Y} := by
  intro Y hy
  have he : IsClosed {z : P.Connector G × G.El | ∀ v, P.bondCost z.1 z.2 ≤ P.bondCost z.1 v} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun T => isClosed_le P.bondCost_cont (by fun_prop)
  exact (minArg_cont P.best {z : P.Connector G × G.El | ∀ v, P.bondCost z.1 z.2 ≤ P.bondCost z.1 v} (fun y ↦ (P.bond_min y).choose_spec) he Y
    (h.predictor_unique Y hy)).continuousWithinAt

theorem min_open : IsOpen {u : CoverConfig G | P.usesMin C u} := by
  simp only [Patch.usesMin, setOf_forall]
  refine isOpen_iInter_of_finite fun l ↦ isOpen_iInter_of_finite fun k ↦ isOpen_iInter_of_finite fun x ↦
    isOpen_iInter_of_finite fun y ↦ isOpen_lt ?_ continuous_const
  unfold via axial; fun_prop

theorem best_open : IsOpen {u : P.Connector G | P.usesBest C u} := by
  have h (u : P.Connector G) : P.usesBest C u ↔ ∃ t, P.bondCost u t < C.predictor_cut :=
    ⟨fun hx ↦ ⟨_,hx⟩, fun ⟨t,hx⟩ ↦ ((P.bond_min u).choose_spec t).trans_lt hx⟩
  simp only [h, setOf_exists]
  exact isOpen_iUnion fun t ↦ isOpen_lt (by fun_prop) continuous_const

@[fun_prop] theorem facesum_cont : Continuous (P.facesum (G := G)) := by
  unfold facesum
  refine continuous_finsetSum _ fun x _ ↦ continuous_finsetSum _ fun q _ ↦ ?_
  split
  · unfold faceValue; fun_prop
  exact continuous_const

@[fun_prop] theorem axialCost_cont (t : P.FrameTag) :
    Continuous (fun u : CoverConfig G => P.axialCost u t) := by
  unfold axialCost
  refine continuous_finsetSum _ fun x _ ↦ continuous_finsetSum _ fun q _ ↦ ?_
  split
  · unfold axial; fun_prop
  exact continuous_const

theorem eligible_set (t : P.FrameTag) :
    MeasurableSet {u : CoverConfig G | t ∈ P.eligible C u} := by
  simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (isClosed_le (P.axialCost_cont _) (by fun_prop)).measurableSet

theorem count_meas : Measurable fun u : CoverConfig G => ((P.eligible C u).card : ℝ) := by
  classical
  have h (u : CoverConfig G) : ((P.eligible C u).card : ℝ) =
      ∑ i : P.FrameTag, ite (i ∈ P.eligible C u) (1 : ℝ) 0 := by simp
  simp only [h]
  refine Finset.measurable_fun_sum _ fun i _ ↦ ?_
  exact Measurable.ite (P.eligible_set i) measurable_const measurable_const

theorem frameMass_meas (t : P.FrameTag) :
    Measurable fun u : CoverConfig G => P.frameMass C u t := by
  unfold frameMass
  refine Measurable.ite P.min_open.measurableSet measurable_const
    (Measurable.ite (P.eligible_set t) ?_ measurable_const)
  exact P.count_meas.inv

theorem frame_meas (h : P.Branches C G) (t : P.FrameTag) :
    Measurable fun u : CoverConfig G => P.frame C u t := by
  classical
  have hc : Continuous (fun u : CoverConfig G => fun x => (P.axial u t P.center)⁻¹ * P.axial u t x) := by
    unfold axial; fun_prop
  exact (P.selected_cont h).measurable_piecewise hc.continuousOn P.min_open.measurableSet

theorem predictorMass_meas (x : P.Points) :
    Measurable fun f : P.Connector G => P.predictorMass C f x := by
  unfold predictorMass
  exact Measurable.ite P.best_open.measurableSet measurable_const measurable_const

theorem predict_meas (h : P.Branches C G) (x : P.Points) :
    Measurable fun f : P.Connector G => P.predict C f x := by
  classical
  exact (P.best_cont h).measurable_piecewise (continuous_apply x).continuousOn P.best_open.measurableSet

theorem frameMass_sum (h : P.Branches C G) (U : CoverConfig G) :
    ∑ i, P.frameMass C U i = 1 := by
  classical
  by_cases ht : P.usesMin C U
  · have hh : 0 < (Fintype.card P.FrameTag : ℝ) := by exact_mod_cast Fintype.card_pos
    simp only [frameMass, if_pos ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ hh.ne']
  simp_rw [frameMass, if_neg ht]
  have hc : (P.eligible C U).card ≠ 0 := (Finset.card_pos.mpr (h.axial_exists U)).ne'
  simp [hc]

theorem predictorMass_sum (Y : P.Connector G) : ∑ i, P.predictorMass C Y i = 1 := by
  classical
  by_cases ht : P.usesBest C Y
  · have hh : 0 < (Fintype.card P.Points : ℝ) := by exact_mod_cast Fintype.card_pos
    simp only [predictorMass, if_pos ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ hh.ne']
  simpa only [predictorMass, if_neg ht] using P.weight_sum
end Patch
end YM.RG
