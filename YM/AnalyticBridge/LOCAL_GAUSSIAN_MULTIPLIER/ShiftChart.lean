import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Curtain
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Moments


/-!
Path derivative uses of the multiplier require ALL hard arguments to stay
fixed in that query. License using probability-Haar coordinates for those
regular links *also appearing in that local component*. There is still one
Gaussian and no privilege to resample the H links when a different term in
the product needs another estimate. The theorem includes return to the
original Gaussian for value or derivative majorants with the corresponding
restriction.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian.Curtain
open Function Filter Set Lattice Wilson RG Next.SectorChange Next.SectorChange.Gaussian Moments
open MeasureTheory ProbabilityTheory WithLp Matrix Precision Metric
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff ENNReal

section main
variable {G : Gauge} {H R : Type} [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R]
    (J : ChartRatio G) (g r : ℝ)

abbrev Chart (G : Gauge) (H R : Type) := Next.SectorChange.Gaussian.Table ((H⊕R) × G.ColorIndex)

/-- W r guard has analytic snap and uses the same chartRatio as the sector. -/
structure Ready : Prop where
  localPrice : LocalRatio J
  pos : 0 < r
  seen : r ≤ J.radius
  ins : r ≤ firstRadius G
  heat : 0 < g

variable (m : Prices G H) (v : LinkArray G H) (C : Chart G H R)

/-- Log of with-density on Haar-of-held and native Lebesgue of open;
only interpret inside chart. Note there are *two* log uses of J:
here the compensator for the coordinate change when integrating, and
separately in the E exponent after the original SectorChange. -/
def tab (p : Pair G H R) :=
    -Real.log (g ^ Fintype.card (H × G.ColorIndex)) -
      (∑ i, Real.log (J.scale * J.J (unlit v p.2 i))) +
      (-Real.log (coat C) - force C (poured g m v p) / 2)

def fare (p : Pair G H R) := Real.exp (tab J g m v C p)

open scoped Classical in
def coverFee (p : Pair G H R) := if validBack r v p then fare J g m v C p else 0

def rewriteAt (f : Coordinates G H R → ℝ) (p : Pair G H R) : ℝ :=
    coverFee J g r m v C p * f (poured g m v p)

lemma cover_out (f : Coordinates G H R → ℝ) (p : Pair G H R) (h : ¬ validBack r v p) :
    rewriteAt J g r m v C f p = 0 := by simp [rewriteAt,coverFee,h]

@[fun_prop] lemma force_meas : Measurable (force C) := by
  unfold force mulVec dotProduct; fun_prop

lemma fare_pos (p : Pair G H R) : 0 < fare J g m v C p := Real.exp_pos _

lemma cover_nonneg (p : Pair G H R) : 0 ≤ coverFee J g r m v C p := by
  unfold coverFee; split
  · exact (fare_pos ..).le
  exact le_rfl
lemma cover_fee_meas (h : Ready J g r) :
    Measurable (Function.uncurry fun m => coverFee J g r m v C) := by
  unfold uncurry coverFee
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurable_snd.comp measurable_snd) (read_open v h.ins).measurableSet
  have hu := (read_open v h.ins).measurableSet
  let X := Prices G H × Pair G H R
  have hx (i) : Measurable (fun p : X => unlit v p.2.2 i) :=
    (measurable_pi_apply i).comp ((unlit_meas v).comp (measurable_snd.comp measurable_snd))
  unfold fare tab
  exact ((measurable_const.sub (Finset.measurable_fun_sum _ fun i _ =>
    (measurable_const.mul (h.localPrice.borel.comp (hx i))).log)).add
    (measurable_const.sub (((force_meas C).comp (poured_meas g v)).div_const _))).exp

lemma rewrite_meas_of {Y : Type*} [MeasurableSpace Y] (M : Y → Prices G H) (hh : Measurable M)
    (f : Y → Coordinates G H R → ℝ) (hf : Measurable (Function.uncurry f)) (h : Ready J g r) :
    Measurable (Function.uncurry fun y => rewriteAt J g r (M y) v C (f y)) :=
  let he := (hh.comp (measurable_fst (α:=Y) (β:=Pair G H R))).prodMk measurable_snd
  ((cover_fee_meas J g r v C h).comp he).mul (hf.comp
    (measurable_fst.prodMk ((poured_meas g v).comp he)))

lemma rewrite_meas (f : Coordinates G H R → ℝ) (hf : Measurable f) (h : Ready J g r) :
    Measurable (rewriteAt J g r m v C f) := by
  have hx : Measurable (fun p : Unit × Coordinates G H R => f p.2) := hf.comp measurable_snd
  have hp : Measurable (fun p : Unit × Pair G H R => rewriteAt J g r m v C f p.2) :=
    rewrite_meas_of J g r v C (fun _ : Unit => m) measurable_const (fun _ => f) hx h
  have he : Measurable (fun p : Pair G H R => ((),p)) := measurable_prodMk_left
  convert! hp.comp he using 1

/-- Only uses the reciprocal Jacobian *where it is defined*. -/
theorem vested (p : Pair G H R) (h : validBack r v p) (hr : Ready J g r) (hC : C.PosDef) :
    coverFee J g r m v C p =
      (g ^ Fintype.card (H × G.ColorIndex))⁻¹*(pay J (unlit v p.2))⁻¹ * ratio C (poured g m v p) := by
  unfold coverFee; rw [if_pos h]
  have hu i : 0 < J.scale*J.J (unlit v p.2 i) := mul_pos (shrink hr.localPrice hr.pos hr.seen hr.ins).scale
    ((shrink hr.localPrice hr.pos hr.seen hr.ins).pos _ (on_shelf J hr.ins h i (Set.mem_univ _)))
  rw [fare,tab,← Real.log_prod (f:=fun i => J.scale*J.J (unlit v p.2 i)) (fun i _ => (hu i).ne'),
    Real.exp_add,sub_eq_add_neg,Real.exp_add,Real.exp_neg,Real.exp_neg,
    Real.exp_log (pow_pos hr.heat _), Real.exp_log (Finset.prod_pos (fun i _ => hu i)),sub_eq_add_neg,Real.exp_add,Real.exp_neg, Real.exp_log (coat_pos hC)]
  unfold ratio pay; rw [neg_div]

/-- Cost of the move by g,m in just the held coordinates. -/
private lemma recenter (m : Prices G H) (g : ℝ) (hg : 0 < g) (f : LogArray G H → ℝ) :
    (Integrable f ↔ Integrable (fun z => f (displaced m g z))) ∧
    (∫ a,f a) = g ^ (Fintype.card (H × G.ColorIndex)) * ∫ z, f (displaced m g z) := by
  obtain ⟨h1,h2⟩ := Gaussian.paid_scale hg (f ∘ tape) m
  refine ⟨?_,?_⟩
  · exact ((tape_volume (G:=G) (ι:=H)).integrable_comp_emb tape.measurableEmbedding).symm.trans h1
  rw [← (tape_volume (G:=G) (ι:=H)).integral_comp' f]; exact h2

/-- Zero hypotheses in Lie algebra a, pre exp where an out-of-chart z can
still produce a group element in the chart. -/
def Shelters (f : Coordinates G H R → ℝ) :=
    ∀ z : Coordinates G H R, f z ≠ 0 → issued m g z ∈ mouth (smaller J r)

lemma sheltered_half (hr : Ready J g r) (hC : C.PosDef) (f : Coordinates G H R → ℝ)
    (hf : Measurable f) (h : Shelters J g r m f) (a : Prices G R) :
    let l := fun b : Prices G H => ratio C (Curtain.join a b) * f (Curtain.join a b)
    let p := fun y : LinkArray G H => rewriteAt J g r m v C f (a,y)
    (Integrable l ↔ Integrable p (piHaar G H)) ∧ (∫ z, l z) = ∫ y, p y ∂piHaar G H := by
  classical
  intro l p; let u := smaller J r
  have he := shrink hr.localPrice hr.pos hr.seen hr.ins
  have hout y (hy : y ∉ covered (smaller J r) v) : p y = 0 := cover_out J g r m v C f (a,y) (show ¬ validBack r v (a,y) from fun hx => hy ((read_cover v J r) ▸ (show y ∈ readBack r v from hx)))
  obtain ⟨h1,h2⟩ := release_integral he v p ((rewrite_meas J g r m v C f hf hr).comp (measurable_prodMk_left (x:=a))).stronglyMeasurable hout
  let s : LogArray G H → ℝ := (mouth u).indicator (fun x => pay u x • p (release v x))
  change Integrable p _ ↔ Integrable s at h1
  change (∫ y, p y ∂_)=∫ x,s x at h2
  obtain ⟨h3,h4⟩ := recenter m g hr.heat s
  let b := g ^ (Fintype.card (H × G.ColorIndex)); have hb : 0 < b := pow_pos hr.heat _
  have hz (z) : s (displaced m g z) = b⁻¹*l z := by
    let w := displaced m g z
    change s w=_; unfold s
    by_cases hv : w∈mouth u
    · rw [indicator_of_mem hv]; change pay u w * p (release v w) = _
      have hw : validBack r v (a,release v w) := by
        change release v w ∈ readBack r v; rw [read_cover v J r,← release_image]; exact mem_image_of_mem _ hv
      have hx : poured g m v (a,release v w) = Curtain.join a z := by
        unfold poured; rw [unlit_read v hr.ins (J:=J) hv, inverts g m hr.heat]
      have hh : unlit v (release v w)=w := unlit_read v hr.ins hv
      have H : 0<pay u w := Finset.prod_pos fun i _ => mul_pos he.scale (he.pos _ (hv i (Set.mem_univ _)))
      unfold p rewriteAt
      rw [hx, vested J g r m v C (a,release v w) hw hr hC,hx]; change pay u w*(b⁻¹*(pay u _ )⁻¹ * _ * _) = _
      rw [hh]; unfold l; field_simp
    rw [indicator_of_notMem hv]; have hx : f (Curtain.join a z) = 0 := by
      by_contra hh; apply hv
      simpa only [issued, close_join] using (h _ hh)
    simp [l,hx]
  change (∫ x,s x) = b*_ at h4
  simp_rw [hz] at h3 h4
  rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hb.ne',one_mul] at h4
  refine ⟨Iff.symm (h1.trans (h3.trans ?_)), h4.symm.trans h2.symm⟩
  constructor
  · intro h
    have hh := h.const_mul b
    convert! hh using 1
    ext1; rw [← mul_assoc, mul_inv_cancel₀ hb.ne',one_mul]
  intro h; exact h.const_mul _

private lemma cross {α β ν : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace ν]
    {μ : Measure α} {μ' : Measure β} {ρ : Measure ν} [SFinite μ] [SFinite μ'] [SFinite ρ]
    {x : α × β → ℝ} {y : α × ν → ℝ} (hx : Measurable x) (hy : Measurable y)
    (he : ∀ a, (Integrable (fun b => x (a,b)) μ' ↔ Integrable (fun c => y (a,c)) ρ) ∧
      (∫ b,x (a,b)∂μ')=(∫ c,y (a,c) ∂ρ) ∧ (∫ b, ‖x (a,b)‖∂μ')=(∫ c, ‖y (a,c)‖ ∂ρ)) :
    (Integrable x (μ.prod μ') ↔ Integrable y (μ.prod ρ)) ∧ (∫ p,x p∂μ.prod μ')=(∫ p,y p∂μ.prod ρ) := by
  have hh : Integrable x (μ.prod μ') ↔ Integrable y (μ.prod ρ) := by
    rw [integrable_prod_iff hx.aestronglyMeasurable,integrable_prod_iff hy.aestronglyMeasurable]
    simp_rw [fun i => (he i).1,fun i => (he i).2.2]
  refine ⟨hh,?_⟩
  by_cases hz : Integrable x (μ.prod μ')
  · rw [integral_prod _ hz,integral_prod _ (hh.mp hz)]
    simp_rw [fun i => (he i).2.1]
  rw [integral_undef hz,integral_undef (fun hv => hz (hh.mpr hv))]

lemma rewrite_norm (f : Coordinates G H R → ℝ) (p) :
    ‖rewriteAt J g r m v C f p‖ = rewriteAt J g r m v C (fun z => ‖f z‖) p := by
  unfold rewriteAt; rw [norm_mul, Real.norm_of_nonneg (cover_nonneg ..)]

/-- Held-variable replacement. Bochner equality; license it on either
side before use. -/
theorem covered_price (hr : Ready J g r) (hC : C.PosDef) (f : Coordinates G H R → ℝ)
    (hf : Measurable f) (hh : Shelters J g r m f) :
    let p := rewriteAt J g r m v C f
    (Integrable f (cloud C) ↔ Integrable p (measure G H R)) ∧ (∫ z,f z∂cloud C)=∫ z,p z∂measure G H R := by
  intro p; let μ : Measure (Prices G R) := volume
  let u : Coordinates G H R → ℝ := fun z => ratio C z*f z
  let X : Prices G R × Prices G H → ℝ := u ∘ separate.symm
  have hp : Measurable p := rewrite_meas J g r m v C f hf hr
  have hx : Measurable X := ((measurable_ratio _).mul hf).comp separate.symm.measurable
  have hv a : (Integrable (fun b => X (a,b)) volume ↔ Integrable (fun c => p (a,c)) (piHaar G H)) ∧
      (∫ b,X (a,b))=(∫ c,p (a,c) ∂piHaar G H) ∧ (∫ b, ‖X (a,b)‖)=(∫ c, ‖p (a,c)‖ ∂piHaar G H) := by
    obtain ⟨hl,hY⟩ := sheltered_half J g r m v C hr hC f hf hh a
    refine ⟨hl,hY,?_⟩
    have hi := (sheltered_half J g r m v C hr hC (fun z => ‖f z‖) hf.norm (fun z hz => hh z (norm_ne_zero_iff.mp hz)) a).2
    simp_rw [p,rewrite_norm]
    unfold X u; simp only [Function.comp_apply,norm_mul, Real.norm_of_nonneg (ratio_pos hC _).le]; exact hi
  obtain ⟨hs,he⟩ := cross (μ:=μ) hx hp hv
  have hc := separate_price (G:=G) (H:=H) (R:=R)
  refine ⟨(charged hC f).1.trans ((hc.symm.integrable_comp_emb separate.symm.measurableEmbedding).symm.trans hs),?_⟩
  apply (charged hC f).2.trans
  change (∫ z,u z)=_; rw [← hc.symm.integral_comp' u]; exact he

/-- Coupled with all *frozen* Y variables. `M` is held sector mean (H
projection) *at that Y*. Keep it across every factor. -/
theorem coupled {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [SFinite μ]
    (hr : Ready J g r) (hC : C.PosDef) (M : Y → Prices G H) (hM : Measurable M)
    (f : Y → Coordinates G H R → ℝ) (hf : Measurable (Function.uncurry f))
    (h : ∀ y, Shelters J g r (M y) (f y)) :
    let p := Function.uncurry fun y => rewriteAt J g r (M y) v C (f y)
    let l := Function.uncurry f
    (Integrable l (μ.prod (cloud C)) ↔ Integrable p (μ.prod (measure G H R))) ∧
      (∫ z,l z∂μ.prod (cloud C))=∫ z,p z∂μ.prod (measure G H R) := by
  intro p l
  refine cross hf (rewrite_meas_of J g r v C M hM f hf hr) fun a => ?_
  have ha : Measurable (f a) := hf.comp (measurable_prodMk_left (x:=a))
  have hh := covered_price J g r (M a) v C hr hC (f a) ha (h a)
  refine ⟨hh.1,hh.2,?_⟩
  simp_rw [p,l,uncurry,rewrite_norm]; exact (covered_price J g r (M a) v C hr hC _ ha.norm
    (fun z hz => h a z (norm_ne_zero_iff.mp hz))).2

/-- Even a majorant without this support is tested only on the chart when
making the return change of variables. -/
lemma restrict_invokes (hr : Ready J g r) (f : Coordinates G H R → ℝ) :
    rewriteAt J g r m v C f = rewriteAt J g r m v C ((issued m g ⁻¹' mouth (smaller J r)).indicator f) := by
  funext p
  by_cases h : validBack r v p
  · unfold rewriteAt
    have he : poured g m v p∈issued m g ⁻¹' mouth (smaller J r) := by
      change issued m g (poured g m v p) ∈ mouth (smaller J r)
      unfold issued poured; rw [close_join,attends _ _ hr.heat]; exact on_shelf J hr.ins h
    rw [indicator_of_mem he]
  rw [cover_out J g r m v C _ p h,cover_out J g r m v C _ p h]

lemma returns_cheaply {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [SFinite μ]
    (hr : Ready J g r) (hC : C.PosDef) (M : Y → Prices G H) (hM : Measurable M)
    (f : Y → Coordinates G H R → ℝ) (hf : Measurable (Function.uncurry f)) (hl : Integrable (Function.uncurry f) (μ.prod (cloud C)))
    (he : ∀ y z,0 ≤ f y z) :
    let p := Function.uncurry fun y => rewriteAt J g r (M y) v C (f y)
    Integrable p (μ.prod (measure G H R)) ∧
      (∫ z,p z∂μ.prod (measure G H R)) ≤ ∫ z,Function.uncurry f z∂μ.prod (cloud C) := by
  intro p
  let u (y : Y) := issued (R:=R) (M y) g ⁻¹' mouth (ι:=H) (smaller J r)
  let w (y : Y) := (u y).indicator (f y)
  let t : Set (Y × Coordinates G H R) := {z | z.2∈u z.1}
  have ht : MeasurableSet t := by
    have hk : Measurable fun z : Y × Coordinates G H R => closeHalf z.2 :=
      measurable_snd.comp (separate.measurable.comp measurable_snd)
    have he : Measurable fun z : Y × Coordinates G H R => issued (M z.1) g z.2 :=
      tape.measurable.comp ((hM.comp measurable_fst).add (hk.const_smul g))
    exact he (mouth_meas _)
  have hx : Function.uncurry w=t.indicator (Function.uncurry f) := by
    funext p
    by_cases h : p∈t
    · rw [indicator_of_mem h]; exact indicator_of_mem (show p.2∈u p.1 from h) (f p.1)
    rw [indicator_of_notMem h]; exact indicator_of_notMem (show p.2∉u p.1 from h) (f p.1)
  have hu : p = Function.uncurry (fun y => rewriteAt J g r (M y) v C (w y)) := funext fun z => congr_fun (restrict_invokes J g r (M z.1) v C hr (f z.1)) z.2
  obtain ⟨h1,h2⟩ := coupled J g r v C μ hr hC M hM w (by rw [hx]; exact hf.indicator ht)
    (fun y z hz => Classical.not_not.mp fun ht => hz (indicator_of_notMem (show z ∉ u y from ht) _))
  rw [hu]; have hp : Integrable (uncurry w) _ := hx ▸ hl.indicator ht
  refine ⟨h1.mp hp,h2.symm.trans_le (integral_mono hp hl ?_)⟩
  rw [hx]; exact Set.indicator_le_self' (fun a _ => he a.1 a.2)
end main
end YM.AnalyticBridge.LocalGaussian.Curtain
