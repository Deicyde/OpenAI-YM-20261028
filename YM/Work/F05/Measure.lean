import YM.Work.F05.PiDensity
import YM.Work.F05.Transport


/-!
# Coordinate expression for the actual measure on slice links

Push restricted products to and from the physical slice. In particular,
restrict on the chart per link *relative* to the given background.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F05
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Exterior Tree
open scoped Topology ENNReal BigOperators Matrix.Norms.Frobenius

variable {c f : Side} {G : Gauge} {g : Ratio c f} (B : Forest g)

def parcel (P : ChartRatio G) : Set (AxisChart G B) :=
  Set.univ.pi (fun _ => Metric.ball 0 P.radius)

/-- Product chart ratio and also its version scaled to probability
Haar. They will be used *inside* the specified LocalRatio chart. -/
def toll (P : ChartRatio G) (y : AxisChart G B) : ℝ := ∏ i, P.J (y i)

def load (P : ChartRatio G) (y : AxisChart G B) : ℝ := ∏ i, P.scale * P.J (y i)

lemma load_eq (P : ChartRatio G) (y : AxisChart G B) :
    load B P y = P.scale ^ Fintype.card B.Free * toll B P y := by
  simp [load,toll,Finset.prod_mul_distrib]

lemma parcel_zero {P : ChartRatio G} (h : LocalRatio P) :
    parcel B P ∈ 𝓝 (0 : AxisChart G B) :=
  (isOpen_set_pi finite_univ (fun (_ : B.Free) _ => Metric.isOpen_ball)).mem_nhds
    (fun _ _ => Metric.mem_ball_self (x:= (0:G.Color)) h.patch)

lemma toll_pos {P : ChartRatio G} (h : LocalRatio P) {y : AxisChart G B} (hy : y ∈ parcel B P) :
    0 < toll B P y := Finset.prod_pos (fun i _ => h.pos _ (hy i (mem_univ _)))

lemma load_pos {P : ChartRatio G} (h : LocalRatio P) {y : AxisChart G B} (hy : y ∈ parcel B P) :
    0 < load B P y := by rw [load_eq]; exact mul_pos (pow_pos h.scale _) (toll_pos B h hy)

lemma load_cont {P : ChartRatio G} (h : LocalRatio P) {y : AxisChart G B} (hy : y ∈ parcel B P) :
    ContinuousAt (load B P) y := by
  have hi (i : B.Free) : ContinuousAt (fun z : AxisChart G B => P.scale * P.J (z i)) y :=
    continuousAt_const.mul ((h.germ (y i) (hy i (mem_univ _))).continuousAt.comp
      (f:= fun z : AxisChart G B => z i) (continuous_apply i).continuousAt)
  exact tendsto_finsetProd _ (fun i _ => hi i)

private def chip (P : ChartRatio G) : Set G.Color := Metric.ball 0 P.radius

private def native (P : ChartRatio G) (a : G.Color) := ENNReal.ofReal (P.scale * P.J a)

private def active (P : ChartRatio G) (V : G.El) :=
  ((fun x : G.El => x * V) '' (G.lieExp '' chip P))

private lemma push_link {P : ChartRatio G} (h : LocalRatio P) (V : G.El) :
    MeasurePreserving (fun a => G.lieExp a * V)
      ((volume.restrict (chip P)).withDensity (native P))
      (G.probHaar.restrict (active P V)) := by
  let L := MeasurableEquiv.mulRight V
  have hp : MeasurePreserving L G.probHaar G.probHaar := measurePreserving_mul_right _ _
  have hf : MeasurePreserving G.lieExp ((volume.restrict (chip P)).withDensity (native P))
      (G.probHaar.restrict (G.lieExp '' chip P)) := ⟨G.lieExp_cont.measurable,h.actual⟩
  have hk : (G.probHaar.map L).restrict (active P V) =
      (G.probHaar.restrict (L ⁻¹' active P V)).map L := L.restrict_map ..
  have hh : MeasurePreserving L (G.probHaar.restrict (G.lieExp '' chip P))
      (G.probHaar.restrict (active P V)) := by
    have ht : (L ⁻¹' active P V) = (G.lieExp '' chip P) := L.injective.preimage_image _
    rw [hp.map_eq, ht] at hk
    exact ⟨hp.measurable,hk.symm⟩
  exact hh.comp hf

private lemma push_slice {P : ChartRatio G} (h : LocalRatio P) (x : Bid.Dir G c) :
    MeasurePreserving (exposure B x)
      ((volume.restrict (parcel B P)).withDensity (fun y => ∏ i : B.Free, native P (y i)))
      ((B.order G).restrict (Set.univ.pi fun i => active P (replica g (represent x) i))) := by
  let μ : Measure G.Color := volume.restrict (chip P)
  have hm : (volume : Measure (AxisChart G B)).restrict (parcel B P) = Measure.pi (fun _ => μ) :=
    Measure.restrict_pi_pi ..
  haveI : SigmaFinite μ := by unfold μ; infer_instance
  have hv (i : B.Free) : Measurable (native P) := (measurable_const.mul h.borel).ennreal_ofReal
  haveI : SigmaFinite (μ.withDensity (native P)) := SigmaFinite.withDensity_ofReal _
  have hz := piDensity (fun _ : B.Free => μ) (fun _ : B.Free => native P) hv
  rw [hm, hz, Forest.order, Measure.restrict_pi_pi]
  exact measurePreserving_pi _ _ (fun i : B.Free => push_link h (replica g (represent x) i))

lemma exposure_inj {P : ChartRatio G} (h : LocalRatio P) (x : Bid.Dir G c) :
    InjOn (exposure B x) (parcel B P) := by
  intro a ha b hb he
  funext i
  exact h.inject (ha i (mem_univ i)) (hb i (mem_univ i))
    (mul_right_cancel (congr_fun he i))

/-- Compact sets suffice to compare Jacobians pointwise near a point. -/
lemma order_exposed {P : ChartRatio G} (h : LocalRatio P) (x : Bid.Dir G c)
    (s : Set (AxisChart G B)) (hs : IsCompact s) (hV : s ⊆ parcel B P) :
    (B.order G) (exposure B x '' s) = ∫⁻ y in s, ENNReal.ofReal (load B P y) := by
  let T := Set.univ.pi fun i : B.Free => active P (replica g (represent x) i)
  let Q : Measure (AxisChart G B) := (volume.restrict (parcel B P)).withDensity
    (fun y => ∏ i : B.Free, native P (y i))
  let F := exposure B x
  have hF : Continuous F := (exposure_continuous B).comp (f:= fun y => (x,y))
    (continuous_const.prodMk continuous_id)
  have ht : F '' s ⊆ T := by
    rintro _ ⟨u,hu,rfl⟩ i _
    exact ⟨_, ⟨u i,hV hu i (mem_univ i),rfl⟩, rfl⟩
  have he : MeasurableSet (F '' s) := (hs.image hF).measurableSet
  have hm : (B.order G) (F '' s) = ((B.order G).restrict T) (F '' s) := by
    rw [Measure.restrict_apply he, inter_eq_left.mpr ht]
  change (B.order G) (F '' s) = _
  rw [hm, ← show Q.map F = (B.order G).restrict T from (push_slice B h x).map_eq,
    Measure.map_apply hF.measurable he]
  have hy : F ⁻¹' (F '' s) ∩ parcel B P = s := by
    refine Subset.antisymm (fun y hy => ?_) (fun y hy => ⟨mem_image_of_mem _ hy,hV hy⟩)
    obtain ⟨⟨w,hw,hh⟩,hv⟩ := hy
    exact exposure_inj B h x (hV hw) hv hh ▸ hw
  unfold Q
  rw [withDensity_apply _ (hF.measurable he), Measure.restrict_restrict (hF.measurable he), hy]
  refine setLIntegral_congr_fun hs.measurableSet (fun i hi => ?_)
  exact (ENNReal.ofReal_prod_of_nonneg (s:=Finset.univ) (fun j _ =>
    (mul_pos h.scale (h.pos (i j) (hV hi j (mem_univ j)))).le)).symm
end YM.Work.F05
