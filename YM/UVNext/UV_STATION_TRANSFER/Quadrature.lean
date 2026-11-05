import YM.Next.UV_STRESS.Station


set_option warningAsError false

/-!
# Regulator-ordered Riemann sum in the exact smearing convention

Smooth-test/free terms only. It would be an error to stake the uniform
order-zero estimate itself on their modulus of continuity. We use this
lemma *after* picking the test (which the cutoff order in Admissible
permits), to see that the quadrature of the *free comparison term* can
be removed from the limsup budget. Right closed seam/corner and 4n as
in YM.Extraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.StationTransfer
open Function Set Filter MeasureTheory Metric Analysis Extraction
open Lattice Wilson Climb Ward Table Next.UVStress
open scoped Topology ContDiff BigOperators
variable {G : Gauge} (C : Family G) (F : Extraction.Order) {n : ℕ}

def quadrature (g : Points n → ℂ) (N p : ℕ) :=
  (C.S.a N : ℂ)^(4*n) * ∑ r : Fin n → Site (C.side N p), g (Extraction.Order.cells C N p r)

def integrand (g : Points n → ℂ) (N p : ℕ) :=
  stair C.S fun r : Var C.S n N p => g (Extraction.Order.cells C N p r)

lemma integral_eq (g : Points n → ℂ) (N p) : (∫ x, integrand C g N p x) = quadrature C g N p :=
  stair_integral _

lemma corner_tag {N p : ℕ} {x : Points n} (hx : x∈Fund C.S p n) :
    Extraction.Order.cells C N p (bucket (S:=C.S) N p x) = tag (C.S.a N) (address (C.S.a N) x) := by
  apply PiLp.ext
  intro i
  have h := congr_fun (show address (C.S.a N) x = _ from found (N:=N) hx) i
  simp only [Extraction.Order.cells,points_apply,tag,Schedule.place]
  exact congr_arg (C.S.gridPoint N) h.symm

lemma per_quad (g : Points n → ℂ) (hs : HasCompactSupport g) (hc : Continuous g)
    (p : ℕ) (hp : tsupport g ⊆ Inside C.S p n) :
    Tendsto (fun N : ℕ => quadrature C g N p) atTop (𝓝 (∫ x, g x)) := by
  classical
  let I := Fund C.S p n
  have hI := full_box C.S p n
  let z (N : ℕ) := integrand C g N p
  have he (x) : Tendsto (fun N => z N x) atTop (𝓝 (g x)) := by
    by_cases ht : x∈I
    all_goals unfold I at ht
    · unfold z integrand stair; simp_rw [indicator_of_mem ht, corner_tag C ht]
      exact hc.continuousAt.tendsto.comp (chosen (S:=C.S) x)
    have hx : g x = 0 := by
      refine image_eq_zero_of_notMem_tsupport (fun hi => ht (fun i a => ?_))
      exact ⟨(hp hi i a).1, (hp hi i a).2.le⟩
    unfold z integrand stair; simp_rw [indicator_of_notMem ht,hx]; exact tendsto_const_nhds
  obtain ⟨Y,hY⟩ := hc.bounded_above_of_compact_support hs
  let D := I.indicator fun _ => Y
  have hD : Integrable D := (integrable_indicator_iff hI.1).mpr (integrableOn_const hI.2.ne)
  have ht N : Integrable (z N) := stair_int _
  have hZ (N x) : ‖z N x‖ ≤ D x := by
    unfold z integrand stair D; by_cases hh : x∈I
    · rw [indicator_of_mem hh,indicator_of_mem hh]; exact hY _
    rw [indicator_of_notMem hh,indicator_of_notMem hh,norm_zero]
  have hg := tendsto_integral_filter_of_dominated_convergence (F:=z) (f:=g) D
    (Eventually.of_forall fun N => (ht N).aestronglyMeasurable)
    (Eventually.of_forall fun N => Eventually.of_forall (hZ N)) hD (Eventually.of_forall he)
  simpa only [z,integral_eq] using hg

theorem riemann (g : Points n → ℂ) (hs : HasCompactSupport g) (hc : Continuous g) :
    Tendsto (fun i : ℕ×ℕ => quadrature C g i.1 i.2) F.fuse (𝓝 (∫ x, g x)) := by
  refine Extraction.Order.along (L:=quadrature C g) (f:=F) (p:=fun p => tsupport g ⊆ Inside C.S p n)
    ⟨F.per.cofinal.eventually (room C.S hs), fun _ => _, fun i hi => (per_quad C g hs hc i hi).comp F.mesh.cofinal,
      tendsto_const_nhds⟩

/-- Reference integrand in *physical* units with Jacobian. -/
def quoteFree (K : Points n→ℂ) {r : ℝ} (hr : 0<r) (t : Test n) (x : Points n) :=
  (dilate hr t) x * K (r⁻¹ • x)

lemma continuous_quote (K : Points n→ℂ) (hc : ContinuousOn K (conf n)) {r : ℝ} (hr : 0<r) (t : Test n) :
    Continuous (quoteFree K hr t) := by
  let f := dilate hr t
  have ht : ContinuousOn (fun x : Points n => K (r⁻¹ • x)) (conf n) := hc.comp
    (by fun_prop) (fun x hx => (enlarged (inv_pos.mpr hr) x).1 hx)
  -- same proof as Test.smearing, but use it for quadrature
  apply continuous_iff_continuousAt.mpr; intro x
  by_cases h : x∈conf n
  · exact f.continuous.continuousAt.mul ((ht x h).continuousAt ((conf_open _).mem_nhds h))
  have he : ∀ᶠ y in 𝓝 x, y ∉ tsupport f := isOpen_compl_iff.mpr (isClosed_tsupport f)
    |>.mem_nhds (show x∈(tsupport f)ᶜ from fun w => h (f.tsupport_subset w))
  exact continuousAt_const.congr (f:=fun (_:Points n) => (0:ℂ)) (he.mono fun i hi => by
    unfold quoteFree; rw [image_eq_zero_of_notMem_tsupport hi,zero_mul])

lemma compacts_quote (K : Points n→ℂ) {r : ℝ} (hr : 0<r) (t : Test n) :
    HasCompactSupport (quoteFree K hr t) := (dilate hr t).hasCompactSupport.mul_right

lemma free_integrates (K : Points n→ℂ) {r : ℝ} (hr : 0<r) (t : Test n) :
    (∫ x, quoteFree K hr t x) = t.applyTo K := by
  unfold quoteFree
  rw [show (∫ x,_) = _ from zoom_integral t hr (fun x : Points n => K (r⁻¹ • x))]
  simp_rw [inv_smul_smul₀ hr.ne']

lemma quadrature_quoted (K : Points n→ℂ) (hc : ContinuousOn K (conf n)) {r : ℝ} (hr : 0<r) (t : Test n) :
    Tendsto (fun i : ℕ×ℕ => quadrature C (quoteFree K hr t) i.1 i.2) F.fuse (𝓝 (t.applyTo K)) := by
  rw [← free_integrates K hr]
  exact riemann C F _ (compacts_quote ..) (continuous_quote K hc ..)

end YM.UVNext.StationTransfer
