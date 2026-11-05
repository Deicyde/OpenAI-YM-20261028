import YM.Further.DENSE_MIXED_KERNELS.HeldMeasure

/-!
# Extra held coordinates in a single mixed-sector integral
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels.Port
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Module
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {A : ChartRatio G} {ι : Type} [Fintype ι] (H : Port A)

def swing (g : ℝ) (u x : H.Room ι) := g • x + u
def track (g : ℝ) (u y : H.Room ι) := g⁻¹ • (y-u)
def field (g : ℝ) (u : H.Room ι) (w : H.Bound ι) (x : H.Room ι) := H.dispatch w (H.swing g u x)
def line (g : ℝ) (u : H.Room ι) (w y : H.Bound ι) := H.track g u (H.hear w y)
def zone (g : ℝ) (u : H.Room ι) := (H.swing g u) ⁻¹' H.present
abbrev dimension (_p : Port A) (ι : Type) [Fintype ι] := finrank ℝ (ι → G.Color)

omit [Fintype ι] in
lemma line_ok (g : ℝ) (hg : 0<g) (u : H.Room ι) (w : H.Bound ι) {x : H.Room ι} (hx : x∈H.zone g u) :
    H.line g u w (H.field g u w x)=x := by
  unfold field line track; rw [H.heard w hx]; unfold swing; rw [add_sub_cancel_right,inv_smul_smul₀ hg.ne']

omit [Fintype ι] in
lemma swing_cont (g : ℝ) (u : H.Room ι) : Continuous (H.swing g u) := by unfold swing; fun_prop
lemma swing_preserve {g : ℝ} (hp : 0<g) (u : H.Room ι) : Measure.map (H.swing g u) volume =
    ENNReal.ofReal ((g ^ H.dimension ι)⁻¹) • volume := by
  unfold swing
  let f := fun i : H.Room ι => g • i
  rw [show (fun x:H.Room ι=>g • x + u)=(fun i=>i+u) ∘ f from rfl,
    ←Measure.map_map (μ:=volume) (by fun_prop) (by unfold f; fun_prop)]
  unfold f; rw [Measure.map_addHaar_smul _ hp.ne', Measure.map_smul, (measurePreserving_add_right volume u).map_eq,
    abs_of_nonneg (by positivity)]

lemma swing_inside {g : ℝ} (hp : 0<g) (u : H.Room ι) : Measure.map (H.swing g u) (volume.restrict (H.zone g u)) =
    ENNReal.ofReal ((g ^ H.dimension ι)⁻¹) • volume.restrict H.present := by
  unfold zone; rw [← Measure.restrict_map (H.swing_cont g u).measurable H.open_present.measurableSet,
    H.swing_preserve hp u,Measure.restrict_smul]

lemma charged_swing {g : ℝ} (hp : 0<g) (u : H.Room ι) :
    Measure.map (H.swing g u) ((volume.restrict (H.zone g u)).withDensity fun _ : H.Room ι => ENNReal.ofReal (g^H.dimension ι)) =
      volume.restrict H.present := by
  rw [withDensity_const,Measure.map_smul,H.swing_inside hp u,smul_smul,← ENNReal.ofReal_mul (by positivity),
    mul_inv_cancel₀ (by positivity : g^H.dimension ι ≠ 0),ENNReal.ofReal_one,one_smul]

lemma through (g : ℝ) (hp : 0<g) (u : H.Room ι) (w : H.Bound ι) :
    Measure.map (H.field g u w) ((volume.restrict (H.zone g u)).withDensity
      (fun x => ENNReal.ofReal (g^H.dimension ι*H.stamp (H.swing g u x)))) = heldLaw.restrict (H.touch w) := by
  let M : Measure (H.Room ι) := volume.restrict (H.zone g u)
  let J (a : H.Room ι) := ENNReal.ofReal (H.stamp a)
  let q : H.Room ι→ℝ≥0∞ := fun x => ENNReal.ofReal (g^H.dimension ι*H.stamp (H.swing g u x))
  have h := pump (k:=q) (swing_cont H g u).measurable H.stamp_meas.ennreal_ofReal measurable_const (H.charged_swing hp u)
    (show q=ᵐ[M] _ * (J ∘ H.swing g u) from Eventually.of_forall fun i => ENNReal.ofReal_mul (by positivity))
  rw [show field H g u w = H.dispatch w ∘ H.swing g u from rfl,
    ← Measure.map_map (H.dispatch_cont w).measurable (H.swing_cont g u).measurable]
  change Measure.map _ (Measure.map _ (M.withDensity q))=_; rw [h]; exact H.purse w

section Extra
variable {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]

abbrev front (_p : Port A) (ι : Type) (X : Type) := _p.Room ι × X
abbrev back (_p : Port A) (ι : Type) (X : Type) := _p.Bound ι × X
abbrev jump (g : ℝ) (u : H.Room ι) (w : H.Bound ι) : H.front ι X → H.back ι X := Prod.map (H.field g u w) id
abbrev slideBack (g : ℝ) (u : H.Room ι) (w : H.Bound ι) : H.back ι X → H.front ι X := Prod.map (H.line g u w) id

def debit (g : ℝ) (u : H.Room ι) (x : H.front ι X) := g^H.dimension ι * H.stamp (H.swing g u x.1)

/-- ACCOUNTED with the prefactor and Jacobians still paid once. -/
theorem deck (g : ℝ) (hp : 0<g) (u : H.Room ι) (w : H.Bound ι) :
    Measure.map (H.jump g u w) ((((volume : Measure (H.Room ι)).prod ν).restrict (H.zone g u ×ˢ Set.univ)).withDensity
      (fun x : H.front ι X => ENNReal.ofReal (H.debit g u x))) = (heldLaw.prod ν).restrict (H.touch w ×ˢ Set.univ) := by
  rw [←prod_restrict, ←prod_restrict,Measure.restrict_univ]
  let m := volume.restrict (H.zone g u)
  let j (a : H.Room ι) := ENNReal.ofReal (g^H.dimension ι * H.stamp (H.swing g u a))
  change Measure.map _ ((m.prod ν).withDensity (fun x => j x.1))=_
  have hm := (H.dispatch_cont w).comp (H.swing_cont g u) |>.measurable
  have hs : SigmaFinite m := by unfold m; infer_instance
  have hm' : Measurable j := Measurable.ennreal_ofReal (measurable_const.mul (H.stamp_meas.comp (H.swing_cont g u).measurable))
  rw [← prod_withDensity_left hm',show jump H g u w = Prod.map (H.field g u w) (@id X) from rfl,
    ← Measure.map_prod_map _ _ (show Measurable (H.field g u w) from hm) measurable_id,
    show Measure.map (H.field g u w) (m.withDensity j) = _ from H.through g hp u w, Measure.map_id]

/-- Extended by zero. -/
def route (g : ℝ) (u : H.Room ι) (w : H.Bound ι) (f : H.front ι X → ℝ) (v : H.back ι X) :=
    if v.1∈ H.touch w then
      (g^H.dimension ι)⁻¹ * (H.stamp (H.hear w v.1))⁻¹ * f (H.slideBack g u w v)
    else 0

lemma line_meas (g : ℝ) (u : H.Room ι) (w : H.Bound ι) : Measurable (H.line g u w) := by
  have hh : Measurable (H.hear w) := measurable_pi_lambda _ fun i => H.undo_meas.comp
    ((measurable_pi_apply i).mul_const _)
  exact (show Continuous (H.track g u) by unfold track; fun_prop).measurable.comp hh
lemma route_meas (g : ℝ) (u : H.Room ι) (w : H.Bound ι) {f : H.front ι X→ℝ} (h : Measurable f) : Measurable (H.route g u w f) := by
  have he : Measurable fun v : H.back ι X => H.hear w v.1 := measurable_pi_lambda _ fun i => H.undo_meas.comp
    (((measurable_pi_apply i).comp measurable_fst).mul_const _)
  have ht : Measurable (H.slideBack g u w (X:=X)) := Measurable.prodMap (H.line_meas g u w) measurable_id
  exact Measurable.ite (measurable_fst (H.open_touch w).measurableSet)
    ((measurable_const.mul (H.stamp_meas.comp he).inv).mul (h.comp ht)) measurable_const

/-- FKer holds on the patch for *any* measurable nonnegative weight.
No re-blocking of a kernel when a source path wants to visit a held link. -/
theorem replaces (g : ℝ) (hp : 0<g) (u : H.Room ι) (w : H.Bound ι) {f : H.front ι X→ℝ} (hf : Measurable f)
    (_hn : ∀ x,0 ≤ f x) : Measure.map (H.jump g u w) ((((volume : Measure (H.Room ι)).prod ν).withDensity
      (fun x => ENNReal.ofReal (f x))).restrict (H.zone g u ×ˢ Set.univ)) = (heldLaw.prod ν).withDensity
        (fun x => ENNReal.ofReal (H.route g u w f x)) := by
  have hv : MeasurableSet (H.zone g u ×ˢ (Set.univ:Set X)) := MeasurableSet.prod
    ((H.swing_cont g u).measurable H.open_present.measurableSet) MeasurableSet.univ
  rw [restrict_withDensity hv]
  let j := H.field g u w
  let P : Measure (H.front ι X) := ((volume : Measure (H.Room ι)).prod ν).restrict (H.zone g u ×ˢ Set.univ)
  let D x := ENNReal.ofReal (H.debit g u (x : H.front ι X))
  let J (x : H.back ι X) := ENNReal.ofReal (H.route g u w f x)
  have hJ : Measurable J := (H.route_meas g u w hf).ennreal_ofReal
  have hd : Measurable D := (measurable_const.mul (H.stamp_meas.comp ((H.swing_cont g u).measurable.comp measurable_fst))).ennreal_ofReal
  have hs : Measurable (H.jump g u w (X:=X)) := Measurable.prodMap
    (show Measurable j from (H.dispatch_cont w).measurable.comp (H.swing_cont ..).measurable) measurable_id
  let S := H.touch w ×ˢ (Set.univ:Set X)
  have he : S.indicator J = J := funext fun i => by
    by_cases h : i.1∈H.touch w
    · exact indicator_of_mem (show i∈S from ⟨h,Set.mem_univ _⟩) J
    simp only [S,J,indicator_of_notMem (show i∉ S from fun hi => h hi.1),route,if_neg h,ENNReal.ofReal_zero]
  change Measure.map _ (P.withDensity _)=(heldLaw.prod ν).withDensity J
  rw [← he,withDensity_indicator ((H.open_touch w).measurableSet.prod MeasurableSet.univ)]
  refine pump hs hJ hd (H.deck ν g hp u w) ?_
  filter_upwards [ae_restrict_mem (μ:=(volume : Measure (H.Room ι)).prod ν) hv] with x hx
  have hx' := hx.1
  have hj : H.swing g u x.1 ∈ H.present := hx'
  have hk : H.slideBack g u w (H.jump g u w x)=x := Prod.ext (H.line_ok g hp u w hx') rfl
  dsimp only [D, comp_apply,J,debit,route, Pi.mul_apply]
  rw [hk,show (H.jump g u w x).1=_ from rfl,if_pos (show (H.jump g u w x).1 ∈ H.touch w from H.enters_when w hj),
    show H.hear w (H.jump g u w x).1= _ from H.heard w hj]
  have hz := H.demanded hj
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1; field_simp

end Extra
end YM.Further.DenseMixedKernels.Port
