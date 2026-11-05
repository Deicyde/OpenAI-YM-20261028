import YM.Next.EXTRACTION.Mixture
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Counting
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Held


/-!
# Hold the true fine arguments for hard factors: chart and inverse

Borel totalized chart lookup and exact partial-coordinate cook/read
maps. Indicators are for the *moving* domain. Prove separately that
selected letters keep their chart use on smaller closed domains
(e.g., include broad profiles). Haar later still probability Haar with
the original LocalRatio scale; we just shrink the open patch inside it.
Use small relative links, not links necessarily near flat globally.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian.Curtain
open Function Filter Set Lattice Wilson RG Next.SectorChange Next.SectorChange.Gaussian
open MeasureTheory ProbabilityTheory WithLp Matrix Precision Metric
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff ENNReal

variable {G : Gauge}
section patch
variable {J : ChartRatio G}
def smaller (J : ChartRatio G) (r : ℝ) : ChartRatio G := { J with radius := r }

def patchGeom (G : Gauge) (r : ℝ) := G.lieExp '' ball 0 r
lemma geom_pay {r : ℝ} (hr : r ≤ firstRadius G) : LocalH.Geom G (patchGeom G r) (ball 0 r) :=
  (LocalH.geom_patch G).choose_spec.2 _ hr

lemma shrink (h : LocalRatio J) {r : ℝ} (hr : 0 < r) (he : r ≤ J.radius) (ht : r ≤ firstRadius G) :
    LocalRatio (smaller J r) := by
  let s := ball (0:G.Color) r; let t := ball (0:G.Color) J.radius
  have hu : s ⊆ t := ball_subset_ball he
  have hl := (geom_pay ht).1
  refine ⟨h.scale,hr,h.inject.mono hu,fun x hx => h.pos _ (hu hx),h.anchored,
    fun x hx => h.germ _ (hu hx),h.borel,?_,hl⟩
  ext u huu
  let f := fun x => ENNReal.ofReal (J.scale*J.J x)
  change ((volume.restrict s).withDensity f).map G.lieExp u = _
  have hV : Measurable G.lieExp := G.lieExp_cont.measurable
  have hB : G.lieExp '' s ⊆ G.lieExp '' t := image_mono hu
  have hz := Measure.restrict_restrict (μ:=G.probHaar) (s:=G.lieExp '' s) (t:=G.lieExp '' t) hl.measurableSet
  rw [inter_eq_left.mpr hB,← h.actual] at hz
  change _ = G.probHaar.restrict (G.lieExp '' s) u; rw [← hz]
  change IsOpen (G.lieExp '' s) at hl
  rw [Measure.restrict_apply huu,Measure.map_apply hV (huu.inter hl.measurableSet), Measure.map_apply hV huu]
  rw [withDensity_apply _ (hV (huu.inter hl.measurableSet)),withDensity_apply _ (hV huu),
    Measure.restrict_restrict (hV (huu.inter hl.measurableSet)),Measure.restrict_restrict (hV huu)]
  have hh : G.lieExp ⁻¹' (G.lieExp '' s) ∩ t = s := by
    ext x; constructor
    · rintro ⟨⟨y,hy,hx⟩,hy'⟩; exact h.inject (hu hy) hy' hx ▸ hy
    exact fun hx => ⟨mem_image_of_mem _ hx, hu hx⟩
  rw [preimage_inter,inter_assoc,hh]

/-- Borel lookup even off the chart. Do not use its return-value
as though a chosen global logarithm. -/
def peek (G : Gauge) := (firstChart G).indicator (LocalH.snap G)
lemma peek_ok {r : ℝ} (hr : r ≤ firstRadius G) {g : G.El} (hg : g ∈ patchGeom G r) :
    peek G g = LocalH.snap G g := indicator_of_mem (image_mono (ball_subset_ball hr) hg) _
@[fun_prop] lemma peek_meas (G : Gauge) : Measurable (peek G) := by
  classical
  have he := first_geom G
  have hi : ContinuousOn (LocalH.snap G) (firstChart G) := fun x hx =>
    (((he.2.2.2.2.2.2 _ hx).continuousAt).comp G.continuous_mat.continuousAt).continuousWithinAt
  exact hi.measurable_piecewise continuousOn_const he.1.measurableSet
end patch

section pairs
variable {H R : Type} [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R]

/-- Unchanged real coordinates first, then U arguments to be held. -/
abbrev Pair (G : Gauge) (H R : Type) := Prices G R × LinkArray G H
abbrev Coordinates (G : Gauge) (H R : Type) := Prices G (H⊕R)

def measure (G : Gauge) (H R : Type) [Fintype H] [Fintype R] : Measure (Pair G H R) :=
  volume.prod (piHaar G H)
instance (G : Gauge) (H R : Type) [Fintype H] [Fintype R] : SigmaFinite (measure G H R) := by unfold measure; infer_instance

def separate : Coordinates G H R ≃ᵐ (Prices G R × Prices G H) := tape.trans
  ((MeasurableEquiv.sumPiEquivProdPi _).trans ((tape.symm.prodCongr tape.symm).trans (MeasurableEquiv.prodComm ..)))
omit [DecidableEq H] [DecidableEq R] in
lemma separate_price : MeasurePreserving (separate (G:=G) (R:=R) (H:=H)) :=
  (Measure.measurePreserving_swap.comp
    (((tape_volume (ι:=H) (G:=G)).symm.prod (tape_volume (ι:=R) (G:=G)).symm).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : H⊕R => G.Color)))).comp tape_volume

-- `z_H,z_R` are native scalar indices ordered as in the sector.
def join (v : Prices G R) (w : Prices G H) : Coordinates G H R := separate.symm (v,w)
def openHalf (x : Coordinates G H R) := (separate x).1
def closeHalf (x : Coordinates G H R) := (separate x).2
omit [DecidableEq H] [DecidableEq R] in
lemma united (x : Coordinates G H R) : join (openHalf x) (closeHalf x)=x := separate.symm_apply_apply _
omit [DecidableEq H] [DecidableEq R] in
lemma open_join (v : Prices G R) (w : Prices G H) : openHalf (join v w)=v := by
  unfold openHalf join; rw [MeasurableEquiv.apply_symm_apply]
omit [DecidableEq H] [DecidableEq R] in
lemma close_join (v : Prices G R) (w : Prices G H) : closeHalf (join v w)=w := by
  unfold closeHalf join; rw [MeasurableEquiv.apply_symm_apply]

omit [DecidableEq H] [DecidableEq R] in
lemma open_apply (x : Coordinates G H R) (i) : openHalf x i = x (.inr i.1,i.2) := rfl
omit [DecidableEq H] [DecidableEq R] in
lemma close_apply (x : Coordinates G H R) (i) : closeHalf x i = x (.inl i.1,i.2) := rfl

omit [DecidableEq H] [DecidableEq R] in
lemma join_square (v : Prices G R) (w : Prices G H) :
    dotProduct (join v w) (join v w) = dotProduct v v + dotProduct w w := by
  rw [dotProduct_comm]
  unfold dotProduct; simp_rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
  exact add_comm ..

def issued (m : Prices G H) (g : ℝ) (v : Coordinates G H R) := displaced m g (closeHalf v)

def readBack (r : ℝ) (v : LinkArray G H) : Set (LinkArray G H) :=
  {y | ∀ i, y i*(v i)⁻¹ ∈ patchGeom G r}
def validBack (r : ℝ) (v : LinkArray G H) (q : Pair G H R) := q.2∈readBack r v

def unlit (v : LinkArray G H) (u : LinkArray G H) : LogArray G H := fun i => peek G (u i*(v i)⁻¹)
def retrieve (g : ℝ) (m : Prices G H) (a : LogArray G H) : Prices G H := g⁻¹ • (tape.symm a-m)
def poured (g : ℝ) (m : Prices G H) (v : LinkArray G H) (p : Pair G H R) : Coordinates G H R :=
  join p.1 (retrieve g m (unlit v p.2))

omit [DecidableEq H] in
lemma inverts (g : ℝ) (m : Prices G H) (hg : 0 < g) (w : Prices G H) : retrieve g m (displaced m g w) = w := by
  unfold retrieve displaced; rw [MeasurableEquiv.symm_apply_apply,add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hg.ne',one_smul]
omit [DecidableEq H] in
lemma attends (g : ℝ) (m : Prices G H) (hg : 0 < g) (a : LogArray G H) : displaced m g (retrieve g m a) = a := by
  unfold displaced retrieve
  rw [smul_smul,mul_inv_cancel₀ hg.ne',one_smul,add_comm,sub_add_cancel]; exact tape.apply_symm_apply a

omit [DecidableEq H] [Fintype H] in
lemma read_cover (v : LinkArray G H) (J : ChartRatio G) (r : ℝ) :
    readBack r v = covered (smaller J r) v := by
  ext y; constructor
  · intro hi i _
    obtain ⟨a,ha,h⟩ := hi i
    exact ⟨_,⟨_,ha,rfl⟩, by simp [h]⟩
  intro hi i
  obtain ⟨_,⟨a,ha,rfl⟩,hh'⟩ := hi i (Set.mem_univ _)
  refine ⟨a,ha,?_⟩; rw [← hh']; group

omit [DecidableEq H] in
lemma read_open (v : LinkArray G H) {r : ℝ} (hr : r ≤ firstRadius G) : IsOpen (readBack r v) := by
  unfold readBack; simp only [Set.setOf_forall]; apply isOpen_iInter_of_finite; intro i
  exact (geom_pay hr).1.preimage (show Continuous fun x : LinkArray G H => x i * (v i)⁻¹ by fun_prop)

omit [DecidableEq H] [Fintype H] in
lemma on_shelf {v : LinkArray G H} (J : ChartRatio G) {r : ℝ} (hr : r ≤ firstRadius G) {u : LinkArray G H}
    (hi : u ∈ readBack r v) : unlit v u ∈ mouth (smaller J r) := by
  intro i _; unfold unlit
  rw [peek_ok hr (hi i)]
  exact (geom_pay hr).2.2.2.2.1 (hi i)

omit [DecidableEq H] [Fintype H] in
lemma read_unlit (v : LinkArray G H) {r : ℝ} (hr : r ≤ firstRadius G) {u : LinkArray G H}
    (hi : u ∈ readBack r v) : release v (unlit v u)=u := by
  funext i; unfold release unlit; rw [peek_ok hr (hi i),(geom_pay hr).2.2.2.1 (hi i)]
  group
omit [DecidableEq H] [Fintype H] in
lemma unlit_read (v : LinkArray G H) {J : ChartRatio G} {r : ℝ} (hr : r ≤ firstRadius G) {a : LogArray G H}
    (hh : a∈mouth (smaller J r)) : unlit v (release v a)=a := by
  funext i; unfold release unlit
  rw [mul_inv_cancel_right]
  have hi := hh i (Set.mem_univ i)
  rw [peek_ok hr (mem_image_of_mem _ hi),(geom_pay hr).2.2.1 hi]

omit [DecidableEq H] [Fintype H] in
@[fun_prop] lemma unlit_meas (v : LinkArray G H) : Measurable (unlit v) := by
  unfold unlit; fun_prop
omit [DecidableEq H] in
@[fun_prop] lemma retrieve_meas (g : ℝ) : Measurable (Function.uncurry (retrieve g (G:=G) (H:=H))) := by
  unfold uncurry retrieve; fun_prop
omit [DecidableEq H] [DecidableEq R] in
@[fun_prop] lemma poured_meas (g : ℝ) (v : LinkArray G H) : Measurable (Function.uncurry fun m (p : Pair G H R) => poured g m v p) := by
  unfold uncurry poured join
  exact separate.symm.measurable.comp ((measurable_fst.comp measurable_snd).prodMk
    ((retrieve_meas g).comp (measurable_fst.prodMk ((unlit_meas v).comp (measurable_snd.comp measurable_snd)))))
end pairs
end YM.AnalyticBridge.LocalGaussian.Curtain
