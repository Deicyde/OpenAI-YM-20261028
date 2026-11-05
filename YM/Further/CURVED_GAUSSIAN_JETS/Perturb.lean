import YM.Further.CURVED_GAUSSIAN_JETS.LineLog

/-!
# Transferring numerical kernel and paired determinant errors to nearby bills

To compare *cut* to *uncut* on the actual periods. An omission-smallness
transfer (could use a compulsory-direct/PriceGap certificate without it for
just the positive cost). Constants only numerical functions of the published
prices. `Rows.Bill`/`Both` on errors, not a dimension-dependent entries norm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Precision Progress.StationaryScenes
open Green (wt wt_pos Bottom)
open Rows (Bill major)
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
namespace Prices

def next (p : Prices) : Prices := ⟨p.width, p.gap/2,p.mass+p.gap/2,p.tags,p.width_pos,half_pos p.gap_pos, by linarith [p.mass_pos,p.gap_pos]⟩
lemma vanishes (p : Prices) : Tendsto p.deep atTop (𝓝 0) := by
  convert p.delay.div_const (p.mass*p.reserve) using 2
  · unfold error halo; have := p.mass_pos; have := p.reserve_pos; field_simp
  rw [zero_div]
end Prices

namespace Fits
variable {n : Side} {I : Type*} [Fintype I] {a : I → Site n} {A B : Table I} {p : Prices} (h : Fits a p A)
include h

lemma next : Fits a p.next A where
  symm := h.symm
  floor v := (mul_le_mul_of_nonneg_right (show p.gap/2 ≤ p.gap by linarith [p.gap_pos]) (Joint.dot_nonneg v)).trans (h.floor v)
  mult := h.mult
  entries := Rows.bigger h.entries (by change _ ≤ p.mass+p.gap/2; linarith [p.gap_pos])


variable [DecidableEq I]
lemma tender (u : ℝ) (hu : 0≤u) : Bill a p.speed (shifted A u)⁻¹ (p.reserve/(1+u)) :=
    Rows.slower (p.of_point h.mult hu (h.inverse hu)) (by linarith [p.speed_pos])

lemma compare {s : ℝ} (hB : Fits a p B) (he : Bill a p.width (B-A) s) (hs : 0≤s) (u : ℝ) (hu : 0≤u) :
    Bill a p.speed ((shifted A u)⁻¹-(shifted B u)⁻¹) ((p.reserve^2*s)*Line.bell u) := by
  have ha := h.tender u hu; have hb := hB.tender u hu
  have hh := Rows.slower he (h:=p.speed) (by linarith [p.speed_le,p.speed_pos]); have ht : 0 ≤ p.reserve/(1+u) := by have := p.reserve_pos; positivity
  convert! Rows.product p.speed_pos.le (Rows.product p.speed_pos.le ha hh ht hs) hb (mul_nonneg ht hs) ht using 1
  · conv_rhs => rw [show B-A = shifted B u-shifted A u by unfold shifted; abel, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc _ (shifted B u) _,Matrix.mul_nonsing_inv (shifted B u) (isUnit_iff_ne_zero.mpr (hB.shift_pos hu).det_pos.ne'),
      Matrix.nonsing_inv_mul (shifted A u) (isUnit_iff_ne_zero.mpr (h.shift_pos hu).det_pos.ne'),Matrix.mul_one, Matrix.one_mul]
  rw [Line.bell, pow_two (1+u), one_div, mul_inv]; ring

end Fits
end YM.Further.CurvedGaussianJets
