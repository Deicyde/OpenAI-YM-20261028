import YM.Analysis.Polydisc
import YM.Pressure.Seeds
import YM.Work.F05.PiDensity


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Exponential substitution at physical relative links

F05 compares determinants via compact tests on
`exposure` near flat. Here make a change of variables for the RG integral:
allow *any* selected sublist of the non-tree variables, integrate rather
than hold them, and hold other variables outside their charts on the
original Haar measure. And arbitrary background rather than an exponential
coarse V. Give integrability as well as the actual Bochner identity (use
with complete space and L¹!). Also works for complex or signed probes.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Tree Metric
open scoped Topology ENNReal BigOperators Matrix.Norms.Frobenius

section links
variable {G : Gauge} {ι : Type}

/-- Native coordinates on any sublist. ATTENTION: `‖ ‖` on LogArray is
Pi sup norm, on each `G.Color` Euclidean. `volume` on LogArray is
nevertheless COUNTING coordinate volume (product of color volumes). -/
abbrev LogArray (G : Gauge) (ι : Type) := ι → G.Color
abbrev LinkArray (G : Gauge) (ι : Type) := ι → G.El

def release (ν : LinkArray G ι) (a : LogArray G ι) : LinkArray G ι := fun i =>
  G.lieExp (a i) * ν i

def mouth (Z : ChartRatio G) : Set (LogArray G ι) :=
  Set.univ.pi (fun _ => ball 0 Z.radius)

def groupLip (Z : ChartRatio G) (v : G.El) : Set G.El :=
  (fun x : G.El => x * v) '' (G.lieExp '' (ball 0 Z.radius))

def covered (Z : ChartRatio G) (ν : LinkArray G ι) : Set (LinkArray G ι) :=
  Set.univ.pi (fun i => groupLip Z (ν i))

variable [Fintype ι]

def piHaar (G : Gauge) (ι : Type) [Fintype ι] : Measure (LinkArray G ι) := Measure.pi (fun _ => G.probHaar)
instance (G : Gauge) : IsProbabilityMeasure (piHaar G ι) := by unfold piHaar; infer_instance

lemma mouth_meas (Z : ChartRatio G) : MeasurableSet (mouth (ι:=ι) Z) :=
  MeasurableSet.univ_pi fun _ => isOpen_ball.measurableSet

lemma covered_isOpen {Z : ChartRatio G} (h : LocalRatio Z) (ν : LinkArray G ι) : IsOpen (covered Z ν) := by
  apply isOpen_set_pi finite_univ
  intro i _
  change IsOpen ((Homeomorph.mulRight (ν i)) '' (G.lieExp '' (ball 0 Z.radius)))
  exact (Homeomorph.mulRight _).isOpenMap _ h.isOpen

lemma covered_meas {Z : ChartRatio G} (h : LocalRatio Z) (ν : LinkArray G ι) : MeasurableSet (covered Z ν) :=
  (covered_isOpen h ν).measurableSet

omit [Fintype ι] in
lemma release_image (Z : ChartRatio G) (ν : LinkArray G ι) :
    release ν '' mouth Z = covered Z ν := by
  ext y; constructor
  · rintro ⟨a,ha,rfl⟩ i _
    exact ⟨_, ⟨_, ha i (mem_univ _), rfl⟩, rfl⟩
  intro h
  have hi i : ∃ a : G.Color, a ∈ ball 0 Z.radius ∧ G.lieExp a * ν i = y i := by
    obtain ⟨_,⟨x,hx,rfl⟩,he⟩ := h i (mem_univ _)
    exact ⟨x,hx,he⟩
  choose a ha he using hi
  exact ⟨a,fun i _ => ha i,funext he⟩

omit [Fintype ι] in
lemma release_injOn {Z : ChartRatio G} (h : LocalRatio Z) (ν : LinkArray G ι) :
    InjOn (release ν) (mouth Z) := fun _ ha _ hb e => funext fun i =>
      h.inject (ha i (mem_univ i)) (hb i (mem_univ i)) (mul_right_cancel (congr_fun e i))

omit [Fintype ι] in
@[fun_prop] lemma release_continuous (ν : LinkArray G ι) : Continuous (release ν) := by unfold release; fun_prop

def pay (Z : ChartRatio G) (a : LogArray G ι) : ℝ := ∏ i, Z.scale * Z.J (a i)

def ennPay (Z : ChartRatio G) (a : LogArray G ι) : ℝ≥0∞ := ∏ i, ENNReal.ofReal (Z.scale * Z.J (a i))

def logMeasure (Z : ChartRatio G) (ι : Type) [Fintype ι] : Measure (LogArray G ι) :=
  (volume.restrict (mouth Z)).withDensity (ennPay Z)

lemma pay_meas {Z : ChartRatio G} (h : LocalRatio Z) : Measurable (pay (ι:=ι) Z) := by
  unfold pay; exact Finset.measurable_fun_prod _ fun i _ => measurable_const.mul (h.borel.comp (measurable_pi_apply i))
lemma ennPay_meas {Z : ChartRatio G} (h : LocalRatio Z) : Measurable (ennPay (ι:=ι) Z) := by
  unfold ennPay; exact Finset.measurable_fun_prod _ fun i _ =>
    (measurable_const.mul (h.borel.comp (measurable_pi_apply i))).ennreal_ofReal

lemma toReal_pay {Z : ChartRatio G} (h : LocalRatio Z) {a : LogArray G ι}
    (ha : a ∈ mouth Z) : (ennPay Z a).toReal = pay Z a := by
  have hi (i : ι) : 0 < Z.scale * Z.J (a i) := mul_pos h.scale (h.pos _ (ha i (mem_univ _)))
  unfold ennPay pay
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (hi i).le), ENNReal.toReal_ofReal]
  exact Finset.prod_nonneg fun i _ => (hi i).le

lemma pay_complete (Z : ChartRatio G) (a : LogArray G ι) : ennPay Z a < ⊤ := ENNReal.prod_lt_top fun i _ => by simp

/-- Physical probability Haar, restricted around V with unchanged scale. -/
lemma link_release {Z : ChartRatio G} (h : LocalRatio Z) (v : G.El) :
    MeasurePreserving (fun y => G.lieExp y * v)
      ((volume.restrict (ball 0 Z.radius)).withDensity (fun y : G.Color => ENNReal.ofReal (Z.scale * Z.J y)))
      (G.probHaar.restrict (groupLip Z v)) := by
  let e := MeasurableEquiv.mulRight v
  let L := G.lieExp '' (ball 0 Z.radius)
  have he : MeasurePreserving e G.probHaar G.probHaar := measurePreserving_mul_right ..
  have hx : MeasurePreserving e (G.probHaar.restrict L) (G.probHaar.restrict (groupLip Z v)) := by
    have ht := e.restrict_map G.probHaar (groupLip Z v)
    have hl : e ⁻¹' groupLip Z v = L := e.injective.preimage_image _
    rw [he.map_eq, hl] at ht
    exact ⟨e.measurable, ht.symm⟩
  exact hx.comp (f:=G.lieExp) ⟨G.lieExp_cont.measurable,h.actual⟩

lemma array_release {Z : ChartRatio G} (h : LocalRatio Z) (ν : LinkArray G ι) :
    MeasurePreserving (release ν) (logMeasure Z ι) ((piHaar G ι).restrict (covered Z ν)) := by
  let μ : Measure G.Color := volume.restrict (ball 0 Z.radius)
  let p := fun y : G.Color => ENNReal.ofReal (Z.scale * Z.J y)
  have hp : Measurable p := (measurable_const.mul h.borel).ennreal_ofReal
  haveI : SigmaFinite μ := by unfold μ; infer_instance
  haveI : SigmaFinite (μ.withDensity p) := SigmaFinite.withDensity_ofReal _
  unfold logMeasure ennPay piHaar covered mouth
  rw [Measure.restrict_pi_pi]
  rw [show (volume : Measure (LogArray G ι)).restrict _ = Measure.pi (fun _ => μ) from Measure.restrict_pi_pi ..]
  rw [Work.F05.piDensity (fun _ : ι => μ) (fun _ : ι => p) (fun _ => hp)]
  exact measurePreserving_pi _ _ fun i : ι => link_release h (ν i)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Integrability and identity for exponential release. Includes empty
index set and zero-dimensional Lie algebra. -/
theorem log_transport {Z : ChartRatio G} (h : LocalRatio Z) (ν : LinkArray G ι) (g : LinkArray G ι → X)
    (hg : StronglyMeasurable g) :
    (IntegrableOn g (covered Z ν) (piHaar G ι) ↔
      IntegrableOn (fun y => pay Z y • g (release ν y)) (mouth Z)) ∧
    (∫ a in covered Z ν, g a ∂piHaar G ι) = ∫ y in mouth Z, pay Z y • g (release ν y) := by
  let μ : Measure (LogArray G ι) := volume.restrict (mouth Z)
  let v := g ∘ release ν
  have ht := array_release h ν
  have hy : ∀ᵐ y ∂μ, ennPay Z y < ⊤ := Eventually.of_forall (pay_complete Z)
  have hx : (fun y => (ennPay Z y).toReal • v y) =ᵐ[μ] (fun y => pay Z y • v y) := by
    filter_upwards [show ∀ᵐ (y : LogArray G ι) ∂μ, y∈mouth Z from ae_restrict_mem (mouth_meas Z)] with y hh
    rw [toReal_pay h hh]
  constructor
  · change Integrable g _ ↔ Integrable _ _
    rw [← ht.integrable_comp hg.aestronglyMeasurable,logMeasure,
      integrable_withDensity_iff_integrable_smul' (ennPay_meas h) hy]
    exact integrable_congr hx
  rw [← ht.map_eq, integral_map ht.aemeasurable hg.aestronglyMeasurable, logMeasure,
    integral_withDensity_eq_integral_toReal_smul (ennPay_meas h) hy]
  exact integral_congr_ae hx

/-- Total integral form (zero off the domain, to which our intact-sector
applications reduce). Indicator on the right is essential for a global
exponential, e.g. near multiple logarithms. -/
theorem release_integral {Z : ChartRatio G} (h : LocalRatio Z) (ν : LinkArray G ι) (g : LinkArray G ι → X)
    (hg : StronglyMeasurable g) (hv : ∀ y ∉ covered Z ν, g y = 0) :
    let v : LogArray G ι → X := (mouth Z).indicator fun y => pay Z y • g (release ν y)
    (Integrable g (piHaar G ι) ↔ Integrable v) ∧
    (∫ a, g a ∂piHaar G ι) = ∫ y, v y := by
  classical
  intro v
  have he : (covered Z ν).indicator g = g := by
    funext y
    by_cases hy : y ∈ covered Z ν
    · exact indicator_of_mem hy _
    rw [indicator_of_notMem hy _,hv y hy]
  obtain ⟨hl,hh⟩ := log_transport h ν g hg
  rw [← integral_indicator (covered_meas h ν), he, ← integral_indicator (mouth_meas Z)] at hh
  refine ⟨?_,hh⟩
  have ht := integrable_indicator_iff (μ:=piHaar G ι) (f:=g) (covered_meas h ν)
  rw [he] at ht
  exact (ht.trans hl).trans (integrable_indicator_iff (mouth_meas Z)).symm

end links

section slice
variable {G : Gauge} {c f : Side} {r : Ratio c f} (F : Forest r) (cold : F.Free → Prop)
  [DecidablePred cold]

abbrev Held := Subtype cold
abbrev Regular := Subtype (fun i => ¬ cold i)

/-- Same physical slice (one positive link each), split into disjoint lists;
`thaw` will put the arguments back at their OWN addresses. -/
def divide : F.Slice G ≃ᵐ (LinkArray G (Held F cold) × LinkArray G (Regular F cold)) :=
  MeasurableEquiv.piEquivPiSubtypeProd _ cold

def freeze (Y : LinkArray G (Held F cold)) (u : LinkArray G (Regular F cold)) :=
  (divide F cold).symm (Y,u)

def thaw (ν : Config G f) (Y : LinkArray G (Held F cold)) (a : LogArray G (Regular F cold)) :=
  freeze F cold Y (release (fun i => ν i.val.val) a)

@[simp] lemma freeze_held (Y : LinkArray G (Held F cold)) (u : LinkArray G (Regular F cold)) (j : Held F cold) :
    freeze F cold Y u j.val = Y j := congr_fun (congr_arg Prod.fst ((divide F cold).apply_symm_apply (Y,u))) j

@[simp] lemma freeze_regular (Y : LinkArray G (Held F cold)) (u : LinkArray G (Regular F cold)) (j : Regular F cold) :
    freeze F cold Y u j.val = u j := congr_fun (congr_arg Prod.snd ((divide F cold).apply_symm_apply (Y,u))) j

@[fun_prop] lemma freeze_meas : Measurable (uncurry (freeze (G:=G) F cold)) := (divide F cold).symm.measurable

lemma divided : MeasurePreserving (divide (G:=G) F cold) (F.order G)
    ((piHaar G (Held F cold)).prod (piHaar G (Regular F cold))) := by
  unfold Forest.order piHaar divide
  exact measurePreserving_piEquivPiSubtypeProd _ cold

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Iterated release theorem for the actual slice and any sublist. In
`hu` just ask the chart condition ON SUPPORT of g, in particular for
a bill times a likelihood won't test a dead tag. Returns outer and
section integrability as well. -/
theorem thaw_integral {Z : ChartRatio G} (h : LocalRatio Z) (ν : Config G f) (g : F.Slice G → X)
    (hg : StronglyMeasurable g) (C : ℝ) (hc : ∀ x, ‖g x‖ ≤ C)
    (hu : ∀ x, g x ≠ 0 → ∀ i : Regular F cold, x i.val ∈ groupLip Z (ν i.val.val)) :
    let I := fun Y => (mouth Z).indicator (fun y : LogArray G (Regular F cold) => pay Z y • g (thaw F cold ν Y y))
    Integrable g (F.order G) ∧ (∀ Y, Integrable (I Y)) ∧
    Integrable (fun Y => ∫ y, I Y y) (piHaar G (Held F cold)) ∧
    (∫ a, g a ∂F.order G) = ∫ Y, ∫ y, I Y y ∂volume ∂piHaar G (Held F cold) := by
  intro I
  have he : Integrable g (F.order G) := Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hc)
  have hs := (divided (G:=G) F cold).symm
  let v Y u := g (freeze F cold Y u)
  have hm (Y : LinkArray G (Held F cold)) : StronglyMeasurable (v Y) :=
    hg.comp_measurable ((divide F cold).symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hy Y : Integrable (v Y) (piHaar G (Regular F cold)) := Integrable.of_bound
    (hm Y).aestronglyMeasurable C (Eventually.of_forall fun _ => hc _)
  have ht Y : Integrable (I Y) ∧ (∫ u, v Y u ∂piHaar G (Regular F cold)) = ∫ y, I Y y := by
    let N := fun i : Regular F cold => ν i.val.val
    have hx (u : LinkArray G (Regular F cold)) (hi : u ∉ covered Z N) : v Y u = 0 := by
      by_contra hh
      exact hi fun i _ => freeze_regular F cold Y u i ▸ hu (freeze F cold Y u) hh i
    obtain ⟨hk,hj⟩ := release_integral h N (v Y) (hm Y) hx
    exact ⟨hk.mp (hy Y),hj⟩
  have hw : Integrable (uncurry v) ((piHaar G (Held F cold)).prod (piHaar G (Regular F cold))) :=
    hs.integrable_comp_of_integrable he
  refine ⟨he, fun Y => (ht Y).1,?_,?_⟩
  · simp_rw [← fun Y => (ht Y).2]; exact hw.integral_prod_left
  rw [← hs.integral_comp' g]
  change (∫ x, uncurry v x ∂_) = _
  rw [integral_prod _ hw]; simp_rw [Function.uncurry, fun Y => (ht Y).2]

end slice
end YM.Next.SectorChange
