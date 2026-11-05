import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Progress.STATIONARY_SCENES.SliceGap
import YM.Push.STATIONARY_UNIFORM.Count



/-!
# Actual positive-orientation path-shortening bill at flat

Follow the same true length cutoff as Pressure.shortenTerm R 1 (not
shortest periodic paths!). Coefficients on physical real faces; identities
use F03 periodization of `Attached`, not image-by-a-nearest-path. Keep
coefficients distinct on every export that needs label budgets later;
taking abs after periodization enough ONLY for these matrix norms here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Cut
open Function Filter MeasureTheory Set Matrix Lattice  Wilson Tree RG Precision Work
open Progress.StationaryScenes Bid Exterior Bloch Pressure
open Green (link wt Both)
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {G : Gauge} {c f n : Side}

def turn (n : Side) : Cell n ≃ Body 2 n := Equiv.prodCongr (Equiv.refl _) plaqEquiv

def tick (W : PathData G) (N : ℕ) (z x : Cell n) (i : ℕ) : ℝ := if (W.row z.2 i).2.length ≤ N ∧
    E04.landing (W.row z.2 i).2 z.1 = x then (W.row z.2 i).1 else 0

def short (W : PathData G) (N : ℕ) (n : Side) := Matrix.of fun (z x : Body 2 n) => ∑' i, tick W N ((turn n).symm z) ((turn n).symm x) i

def more (W : PathData G) (N : ℕ) (z x : Cell n) (i : ℕ) : ℝ := if N<(W.row z.2 i).2.length ∧
    E04.landing (W.row z.2 i).2 z.1 = x then (W.row z.2 i).1 else 0



variable {W : PathData G} {N : ℕ} {p : Clip} {s w C Λ : ℝ} (hW : W.Bounds p s C Λ)

include hW
lemma sum_tick (z x : Cell n) : Summable (tick W N z x) ∧ Summable (more W N z x) := by
  have hs := F03.row_abs_summable W hW z.2
  constructor
  · exact Summable.of_norm_bounded hs (fun i => by unfold tick; split; exact le_rfl; exact norm_zero.trans_le (abs_nonneg _))
  exact Summable.of_norm_bounded hs (fun i => by unfold more; split; exact le_rfl; exact norm_zero.trans_le (abs_nonneg _))


def invoice (C w : ℝ) := C * (Fintype.card (TypeFace 2) * Push.Uniform.countCost w)
lemma pos_cost : 0≤C := by
  haveI : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩
  have h := hW.rows (Classical.arbitrary _)
  exact (tsum_nonneg h.1).trans h.2.2
omit hW in
lemma invoice_nonneg (C : ℝ) (h : 0≤C) {w : ℝ} (hw : 0<w) : 0 ≤ invoice C w := by unfold invoice; have := Push.Uniform.count_pos hw; positivity


end YM.Further.CurvedGaussianJets.Cut
