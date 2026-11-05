import YM.Analysis.Polydisc
import YM.Bid.Tar
import YM.Work.C13.Variation


/-!
# Analytic emission in the open tube

All frequencies and complex arguments are the *absolute* variables of the
base. At one strict tube point, use `Wide.cone` to reserve exponential decay
of the lens in every frequency seminorm. Its complex derivative in the
Schwartz topology then follows from `hasFDerivAt_shift`. Only after composing
with the distribution do we need to pass from differentiability to analyticity.

This doesn't require cone support of the distribution, or identify emissions
using different choices of cutoff. Properties at the boundary (e.g. in
`Blanket.Modified`) are not needed for this interior estimate.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.C13

open Function Filter Set Boundary Boundary.Surface Probe
open scoped Topology ContDiff BigOperators InnerProductSpace

variable {n : ℕ}

/-- Real-linear frequency coordinate, with complex values. -/
def flatCoord (i : Fin n × Axis) : Points n →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((EuclideanSpace.proj i).comp
    Points.flatten.toContinuousLinearEquiv.toContinuousLinearMap)

lemma flatCoord_apply (i : Fin n × Axis) (x : Points n) :
    flatCoord i x = ↑(Points.flatten x i) := rfl

/-- Curried exponent. `phase n p x` is `i sum_j p_j x_j`, not sesquilinear. -/
def phase (n : ℕ) : Full n →L[ℂ] (Points n →L[ℝ] ℂ) :=
  ∑ i : Fin n × Axis, (EuclideanSpace.proj i).smulRight (Complex.I • flatCoord i)

lemma phase_apply (p : Full n) (x : Points n) :
    phase n p x = ∑ i, p i * (Complex.I * ↑(Points.flatten x i)) := by
  simp [phase, flatCoord_apply]

lemma phase_parts (p : Full n) (x : Points n) :
    phase n p x = (↑(inner ℝ x (reality p)) : ℂ) * Complex.I - ↑(inner ℝ (shade p) x) := by
  have h (u v : Points n) : inner ℝ u v = ∑ i, inner ℝ (Points.flatten u i) (Points.flatten v i) :=
    Points.flatten.inner_map_map u v |>.symm.trans (PiLp.inner_apply ..)
  rw [phase_apply, h, h]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, reality, shade, mul_comm]

lemma lens_eq (D : Blanket n) (p : Full n) (x : Points n) :
    D.lens p x = Complex.exp (phase n p x) * ↑(D.cut x) := by
  rw [phase_parts, sub_eq_add_neg, Complex.exp_add]
  simp [Blanket.lens, plane, Blanket.attenuate, mul_assoc]

/-- At a strict imaginary shift the lens has exponential reserves. The cost
and rate may depend on the shift and on arity. -/
theorem lens_reserve (D : Blanket n) (hw : Bid.Wide n) (p : Full n) (hp : p ∈ tube n) :
    ExpReserve (D.lens p) := by
  rw [show D.lens p = fun x => Complex.exp (phase n p x) * ↑(D.cut x) from
    funext (lens_eq D p)]
  let y := shade p
  obtain ⟨c, hc, hcn⟩ := hw.cone y hp
  have hcone : ∀ z ∈ coneM n, c * ‖z‖ ≤ inner ℝ z y := mem_of_mem_nhds hcn
  let cut := fun x : Points n => (↑(D.cut x) : ℂ)
  have hcut : cut.HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.comp D.uses
  refine ExpReserve.of_cut hcut _ (A := 3 * (‖y‖ + c)) hc (fun x hx => ?_)
  have hx' : x ∈ tsupport D.cut := by
    have hs : Function.support cut = Function.support D.cut := by ext; simp [cut]
    rwa [tsupport, hs] at hx
  obtain ⟨z, hz, hxz⟩ := D.supported hx'
  have hdist : ‖z-x‖ ≤ 3 := by rw [dist_comm, dist_eq_norm] at hxz; exact hxz.le
  have hnorm : ‖x‖ ≤ ‖z‖ + 3 := calc
    ‖x‖ = ‖z - (z-x)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖z‖ + ‖z-x‖ := norm_sub_le ..
    _ ≤ _ := by gcongr
  have hinner : inner ℝ y z - inner ℝ y x ≤ ‖y‖ * 3 := by
    rw [← inner_sub_right]
    exact (real_inner_le_norm y (z-x)).trans
      (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
  have hcz : c * ‖z‖ ≤ inner ℝ y z := (hcone z hz).trans_eq (real_inner_comm y z)
  rw [phase_parts]
  have hpRe : ((↑(inner ℝ x (reality p)) : ℂ) * Complex.I - ↑(inner ℝ (shade p) x)).re =
      -inner ℝ y x := by simp [y]
  rw [hpRe]
  linarith [mul_le_mul_of_nonneg_left hnorm hc.le]

/-- Extend by a dummy test outside the open tube. -/
def interiorLens (D : Blanket n) (hw : Bid.Wide n) (p : Full n) : Joint n := by
  classical
  exact if h : p ∈ tube n then (lens_reserve D hw p h).toProbe else 0

lemma interiorLens_apply (D : Blanket n) (hw : Bid.Wide n) (p : Full n) (hp : p ∈ tube n)
    (x : Points n) : interiorLens D hw p x = D.lens p x := by
  simp only [interiorLens, hp, ↓reduceDIte, ExpReserve.toProbe_apply]

variable {G : Gauge} {L : Register G} {S : Table L} {W : Surface S} {D : ∀ i, Blanket i}

/-- The derivative works for any `Aurora`, since it uses the form of the
lens in the open tube only. -/
lemma hasFDerivAt_interior (X : W.Aurora D) (hw : Bid.Wide n) (p : Full n) (hp : p ∈ tube n) :
    HasFDerivAt (X.lens n) (shiftDeriv (phase n) (X.lens n p)) p := by
  apply hasFDerivAt_shift
  · rw [show (X.lens n p : Points n → ℂ) = (D n).lens p from funext (X.shape n p hp)]
    exact lens_reserve _ hw p hp
  · filter_upwards [(south n).mem_nhds hp] with q hq x
    have h : phase n q x = phase n (q-p) x + phase n p x := by simp
    rw [X.shape n q hq x, X.shape n p hp x, lens_eq, lens_eq, h, Complex.exp_add, mul_assoc]

lemma analytic_interior (X : W.Aurora D) (hw : Bid.Wide n) (v : Fin n → S.Union) :
    AnalyticOnNhd ℂ (X.emit v) (tube n) := by
  intro p hp
  apply PolyDisc.finiteD
  filter_upwards [(south n).mem_nhds hp] with q hq
  let F := Distn.fourier (W.W n v)
  have h : HasFDerivAt (fun x => F (X.lens n x))
      (F.comp (shiftDeriv (phase n) (X.lens n q))) q := by
    rw [hasFDerivAt_iff_isLittleOTVS]
    have ht := F.isBigOTVS_comp.trans_isLittleOTVS
      ((hasFDerivAt_iff_isLittleOTVS).mp (hasFDerivAt_interior X hw q hq))
    simpa only [Function.comp_def, map_sub, ContinuousLinearMap.comp_apply] using ht
  exact h.differentiableAt.const_mul _

theorem answer : YM.Bid.C13 := by
  intro G L S W D hw _
  let X : W.Aurora D := {
    lens n := interiorLens (D n) (hw n)
    shape n p hp := interiorLens_apply (D n) (hw n) p hp }
  exact ⟨X, fun n v => analytic_interior X (hw n) v⟩

end YM.Work.C13
