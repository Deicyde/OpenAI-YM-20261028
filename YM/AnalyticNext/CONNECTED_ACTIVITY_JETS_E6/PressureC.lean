import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Resolvent

/-!
# Symmetrized principal covariance invoice. Gliding interpolation.

Use all tags and all endpoints in theta invoice, but geometry remains those
chosen in `Coat` throughout gluings. Price of principal inverse differences
local from two matrices in a patch later. We use Interpolating `glide`
with identity for price of local diagonal logs (variation E).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Window
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type*} {c : Side} {a : ι→Site c} {B m : ℕ} (D : Window a B) [DecidableEq ι] [Fintype ι]
variable (A : Matrix ι ι ℝ) {X η r : ℝ}

def frameMean := ((1:ℝ)/2) • (D.pad A + (D.pad A).transpose)

def flawed := A * D.frameMean A - 1

omit [Fintype ι] in
lemma twin : IsHermitian (D.frameMean A) := by
  ext i j; simp [frameMean, add_comm,mul_add]

omit [Fintype ι] in
lemma width : Thin a a (D.frameMean A) (B+2) := by
  intro i j hij; rw [frameMean,Matrix.smul_apply, Matrix.add_apply,(D.thin A) i j hij,(D.thin A).transpose i j hij]; simp

lemma height {d : ℕ} (he : Thin a a A d) : Thin a a (D.flawed A) (d+(B+2)) := by
  intro i j hij; have hh : i≠j := by intro hi; subst i; simp at hij
  rw [flawed,Matrix.sub_apply,(he.mul (D.width A)) i j hij]; simp [hh]

def distPay (η r X : ℝ) (m B : ℕ) := payE η r X m*scraps η r X m B

namespace Allow

variable {A}
lemma mate (h : Allow A a m η r X) (D : Window a B) : Price a a (D.frameMean A) (retain η r X) (payE η r X m) := by
  have he := increase (h.primal D) (show retain η r X ≤ _ by linarith [h.weather.1]) le_rfl
  refine increase (weighted_by (paid_add he (flipped he)) (1/2)) le_rfl ?_
  exact le_of_eq (by rw [abs_of_nonneg (by norm_num : 0≤(1/2:ℝ))]; ring)
lemma drift (h : Allow A a m η r X) (D : Window a B) : Price a a (D.frameMean A-A⁻¹) (retain η r X) (distPay η r X m B) := by
  let H := D.pad A-A⁻¹
  have hh : IsHermitian A⁻¹ := h.symmetry.inv
  have hf := paid_add (h.breach D) (flipped (h.breach D))
  rw [show D.frameMean A-A⁻¹=((1:ℝ)/2) • (H+H.transpose) from by
    have he : A⁻¹.transpose=A⁻¹ := by rw [← show (A⁻¹)ᴴ=A⁻¹.transpose from by ext; simp,hh.eq]
    rw [frameMean]; dsimp only [H]; rw [transpose_sub,he]; module]
  refine increase (weighted_by hf (1/2)) le_rfl ?_
  unfold distPay; exact le_of_eq (by rw [abs_of_nonneg (by norm_num : 0≤(1/2:ℝ))]; ring)
lemma flank (h : Allow A a m η r X) (D : Window a B) : Price a a (D.flawed A) (retain η r X) (X*distPay η r X m B) := by
  have he : D.flawed A=A*(D.frameMean A-A⁻¹) := by rw [flawed,mul_sub,h.initial.1]
  rw [he]; exact paid_mul h.relented (h.drift D) h.weather.1.le h.fuel.le (mul_nonneg h.disc (h.heap B))

lemma ground_C (h : Allow A a m η r X) (D : Window a B) (hr : distPay η r X m B ≤ X⁻¹/2) : Bottom (D.frameMean A) (X⁻¹/2) := by
  have he := bilinear_floor (h.drift D) h.weather.1.le
  intro v; have hv := he v
  rw [Matrix.sub_mulVec,dotProduct_sub] at hv
  linarith only [hv, lower_inverse h.relented h.weather.1.le h.fuel h.symmetry h.ground h.down.le h.initial.1 v,
    mul_le_mul_of_nonneg_right hr (nn v)]
end Allow

/-- Jacobi gliding alternative to spectral logdet diagonal contour.
E entries adapt uniformly on every finite actual window. -/
def glide (s : ℝ) := 1 + s • (A-1)
omit [Fintype ι] in
lemma glide_end : glide A 1=A := by unfold glide; abel_nf; simp
omit [Fintype ι] in
lemma glide_start : glide A 0=1 := by unfold glide; simp
omit [Fintype ι] in
lemma Thin.glides {d : ℕ} (h : Thin a a A d) (s : ℝ) : Thin a a (glide A s) d := by
  intro i j he; have hv : i≠j := by intro hi; subst i; simp at he
  simp [glide,h i j he,hv]
omit [Fintype ι] in
lemma affine (s : ℝ) : glide A s = (1-s) • 1 + s • A := by unfold glide; rw [sub_smul,smul_sub,one_smul]; abel
variable {A}
lemma Allow.glide (h : Allow A a m η r X) (he : r ≤ 1) (hg : 1 ≤ X) (s : ℝ) (hh : s∈Set.Icc 0 1) :
    Allow (Window.glide A s) a m η r X := by
  obtain ⟨hh,hw⟩ := hh; have hf : 0 ≤ 1-s := by linarith
  rw [affine]
  refine ⟨h.census,?hSym,h.eta,h.down,h.fuel,?_,?_⟩
  case hSym =>
    apply IsHermitian.add
    · rw [IsHermitian,Matrix.conjTranspose_smul]; simp
    rw [IsHermitian,Matrix.conjTranspose_smul,h.symmetry.eq,star_trivial]
  · have ht := (weighted_by (one_pay a η) (1-s)).1.plus (weighted_by (density _ _ _ h.symmetry h.price) s).1
    exact pricing ht le_rfl (by rw [abs_of_nonneg hh,abs_of_nonneg hf]; nlinarith)
  intro v
  rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_smul,dotProduct_smul]
  simp only [smul_eq_mul]
  have he := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (nn v) he) hf
  nlinarith only [he, mul_le_mul_of_nonneg_left (h.ground v) hh]
end YM.ConnectedActivityE6.Window
