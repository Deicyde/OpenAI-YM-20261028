import YM.RG08.Ballast.Jets
import YM.RG08.Ballast.Ribbons

/-! # Finite-period heat contractions in all variables

Covariance on joint variables has zeros on fixed-external legs.
`lap` includes the half, `arch` hasn't. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff
variable {α X : Type} {σ θ A C : ℝ} {r n : ℕ} {m : Side}
section cal
variable [Fintype X] [DecidableEq X]
abbrev Psalm (X : Type) := (X → ℝ) → ℝ
abbrev zpk (i : X) : X→ℝ := (Pi.single i (1:ℝ))
def lap (M : Matrix X X ℝ) (f : Psalm X) (x : X → ℝ) := (1/2:ℝ)*∑ i,∑ j,M i j*D (zpk j) (D (zpk i) f) x
def arch (M : Matrix X X ℝ) (f g : Psalm X) (x : X → ℝ) := ∑ i,∑ j,M i j*D (zpk i) f x *D (zpk j) g x
-- Use ω or ∞ later; functions polynomial.
variable (M : Matrix X X ℝ)
variable {f g h : Psalm X}
omit [DecidableEq X] in
lemma dune (v : X → ℝ) (h : ContDiff ℝ ω f) : ContDiff ℝ ω (D v f) := by
  unfold D; exact (h.fderiv_right (by simp)).clm_apply contDiff_const
lemma lap_prime (hv : ContDiff ℝ ω f) : ContDiff ℝ ω (lap M f) := contDiff_const.mul (ContDiff.sum (fun _ _=>ContDiff.sum fun _ _=> contDiff_const.mul (dune _ (dune _ hv))))
lemma arch_prime (hf : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g) : ContDiff ℝ ω (arch M f g) := ContDiff.sum fun _ _=> ContDiff.sum fun _ _=> (contDiff_const.mul (dune _ hf)).mul (dune _ hg)
omit [DecidableEq X] in
lemma Daddition (u : X → ℝ) (hf : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g) : D u (f+g)=D u f+D u g := funext fun x=> by
  unfold D; rw [fderiv_add]; rfl
  exacts [hf.differentiable (by simp) x,hg.differentiable (by simp) x]
omit [DecidableEq X] in
lemma DscaleL (u : X → ℝ) (a : ℝ) (hf : ContDiff ℝ ω f) : D u (a • f)=a • D u f := funext fun x=> by
  unfold D; rw [fderiv_const_smul (hf.differentiable (by simp) x)]; rfl
omit [DecidableEq X] in
lemma Dproduct (u : X → ℝ) (hf : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g) : D u (f*g)=D u f*g+f*D u g := funext fun x=> by
  simp only [Pi.add_apply,Pi.mul_apply,D]; rw [fderiv_mul]; swap
  · exact hf.differentiable (by simp) x
  swap; · exact hg.differentiable (by simp) x
  simp; ring

lemma lap_total (hf : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g) : lap M (f+g)=lap M f+lap M g := by
  ext1 x; simp only [lap, Daddition _ hf hg, Daddition _ (dune _ hf) (dune _ hg),Pi.add_apply,mul_add,sum_add_distrib]
lemma lap_scale (hf : ContDiff ℝ ω f) (a : ℝ) : lap M (a • f)=a • lap M f := by
  ext1 x; simp only [lap, DscaleL _ _ hf, DscaleL _ _ (dune _ hf),Pi.smul_apply,smul_eq_mul,mul_left_comm _ a,← Finset.mul_sum]
lemma lap_joint (h : Mᵀ=M) (hf : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g) : lap M (f*g)=lap M f*g+f*lap M g+arch M f g := by
  ext1 x
  unfold lap arch
  have hm (v u : X→ℝ) : D u (D v (f*g))=D u (D v f)*g+D v f * D u g + (D u f * D v g + f*D u (D v g)) := by
    have hZ : ContDiff ℝ ω (D v f*g) := (dune v hf).mul hg
    have hH : ContDiff ℝ ω (f*D v g) := hf.mul (dune v hg)
    rw [Dproduct v hf hg, Daddition u hZ hH,Dproduct u (dune v hf) hg,Dproduct u hf (dune v hg)]
  simp only [hm,Pi.add_apply,Pi.mul_apply,mul_add,sum_add_distrib]
  have hx : ∑ i,∑ j, M i j*(D (zpk j) f x*D (zpk i) g x)=∑ i,∑ j,M i j *D (zpk i) f x * D (zpk j) g x := by
    rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
    rw [show M j i=M i j from congr_fun (congr_fun h i) j]; ring
  rw [hx]; simp only [← mul_assoc]
  -- pull scalar products
  have he : (∑ i,∑ j, M i j*f x * D (zpk j) (D (zpk i) g) x)= f x*(∑ i,∑ j,M i j*D (zpk j) (D (zpk i) g) x) := by
    simp_rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
  simp_rw [he, ← Finset.sum_mul]; ring
@[simp] lemma lap_const (a : ℝ) : lap M (fun _=> a)=0 := by
  have he (u : X→ℝ) : D u (fun _=> (a:ℝ))=fun _=>0 := by funext x; simp [D]
  ext1 x; simp_rw [lap,he]; simp [D]
end cal
end YM.RG08
