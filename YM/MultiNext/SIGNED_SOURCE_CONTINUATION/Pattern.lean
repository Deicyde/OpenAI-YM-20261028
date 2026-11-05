import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Fuels
import YM.Pressure.Seeds
import YM.Source.ODE
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.G02



set_option warningAsError false

/-!
# Polynomial moments on log links, I: common endpoint shape

Adapt `TimeProfile` (cf `Foundations/LinkBounds`. We need an explicit
version as a map of ordinary 3-tuple including gauge values).
Thus derivatives act pointwise into the polynomial spaces. Link matches
on cover using SolvesLink uniqueness, no assertion of existence of
some other smooth holonomy scheme. Pay sign of actual Right
multiplication and derivative of `G.plog` exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Pattern
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {d n : ℕ}

abbrev Fiber (G : Gauge) (d : ℕ) := (i : Fin (d-1)) → Tensor.T (ℝ × ℝ) G.Color (i.val+1)

def field (X : Fiber G d) (t : ℝ) := ∑ i,Tensor.diagonal (X i) (1,t)
lemma field_smooth (X : Fiber G d) : ContDiff ℝ 1 (field X) := ContDiff.sum fun _ _ => (diag_smooth ..).comp (contDiff_const.prodMk contDiff_id)

def path (X : Fiber G d) := (Hol.pipes (field_smooth X)).choose
lemma launches (X : Fiber G d) : SolvesLink (path X) (field X) := (Hol.pipes (field_smooth X)).choose_spec

def run (G : Gauge) (d : ℕ) : Fiber G d → G.Mat := fun X => G.mat (path X 1)

lemma endpoint (G : Gauge) (d : ℕ) : ContDiffAt ℝ ω (run G d) 0 ∧ run G d 0=1 ∧ ∀ a : Fiber G d,
    HasDerivAt (fun t : ℝ => run G d (t • a)) (G.colorMat (∫ t in (0:ℝ)..1, field a t)) 0 := by
  let p : Fiber G d →ₗ[ℝ] ℝ → G.Mat := {
    toFun i t := G.colorMat (field i t)
    map_add' := fun x y => funext fun i => by simp [field, Tensor.diagonal, Finset.sum_add_distrib]
    map_smul' := fun s x => funext fun i => by simp [field, Tensor.diagonal, Finset.smul_sum] }
  obtain ⟨H,hA,hs⟩:= G02.endpointGerm p (fun x => G.colorMat.toContinuousLinearMap.continuous.comp (field_smooth x).continuous)
    (fun x t => G.mat (path x t)) (fun i => by rw [(launches i).1,G.mat_one]) (fun i t => (launches i).2 t)
  exact ⟨H.contDiffAt,hA,fun i => (hs i).congr_deriv (G.colorMat.toContinuousLinearMap.intervalIntegral_comp_comm
    ((field_smooth i).continuous.intervalIntegrable _ _))⟩

/-- Arguments: incoming site algebra, displacement to outgoing,
    polynomial potential. Output log gauged link. -/
abbrev Panel (G : Gauge) (d : ℕ) := G.Color × G.Color × Fiber G d

def stereo (G : Gauge) (d : ℕ) (x : Panel G d) := G.plog
    (G.mat (G.lieExp x.1)*run G d x.2.2* star (G.mat (G.lieExp (x.1+x.2.1))))

lemma scripts (G : Gauge) (d : ℕ) : ContDiffAt ℝ ω (stereo G d) 0 ∧ stereo G d 0=0 := by
  have hu := endpoint G d
  constructor
  · unfold stereo
    have ht : ContDiffAt ℝ ω (fun p : Panel G d => run G d p.2.2) 0 := hu.1.comp (f:=fun p : Panel G d => p.2.2) 0 (contDiffAt_snd.comp _ contDiffAt_snd)
    have he : ContDiff ℝ ω (fun p : Panel G d => G.mat (G.lieExp (p.1+p.2.1))) := G.exp_jet.comp (contDiff_fst.add (contDiff_fst.comp contDiff_snd))
    have hp : ContDiff ℝ ω (fun p : Panel G d => star (G.mat (G.lieExp (p.1+p.2.1)))) := ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff).comp he
    refine ((?_: ContDiffAt ℝ ω G.plog _) ).comp 0 (((G.exp_jet.comp contDiff_fst).contDiffAt.mul ht).mul hp.contDiffAt)
    change ContDiffAt ℝ ω G.plog
      (G.mat (G.lieExp 0)*run G d 0*star (G.mat (G.lieExp (0+0))))
    simpa [hu.2.1] using G.plog_diff
  simp [stereo,hu.2.1]

def line (x : E4) (i : Axis) : (ℝ × ℝ) →L[ℝ] E4 := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight x +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (basis i)
lemma line_at (x : E4) (i : Axis) (s : ℝ) : line x i (1,s)=x+s • basis i := by simp [line]

def tempo (x : E4) (i : Axis) : Snap G d →L[ℝ] Fiber G d :=
    let F : Snap G d →ₗ[ℝ] Fiber G d := {
      toFun v j := ((v j).val i).compContinuousLinearMap (fun _ => line x i)
      map_add' v w := by funext j; ext1 Z; simp
      map_smul' r v := by funext j; ext1 Z; simp }
    F.toContinuousLinearMap

def xyz (x : Cover) : E4 := WithLp.toLp 2 fun i => (x i:ℝ)
lemma xyz_step (x : Cover) (i : Axis) : xyz (x+Lattice.step i)=xyz x + basis i := by
  ext j; simp [xyz,basis]

lemma humming (A : Snap G d) (x : Cover) (i : Axis) : partConnection d (expand d A) 1 (x,i) = field (tempo (xyz x) i A) := by
  funext t
  simp only [field,partConnection,potential,one_smul]
  rw [←Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun j _ => ?_
  rw [expand,dif_pos j.isLt]
  change Tensor.diagonal ((A j).val i) (xyz x + _) = _
  rw [←line_at]; rfl

lemma stem (H : Hol G) (A : Snap G d) (x : Cover) (i : Axis) : G.mat (H.links d (expand d A) 1 (x,i))=
    run G d (tempo (xyz x) i A) := by
  have he := (H.solves d (expand d A) 1 (x,i))
  rw [humming] at he
  exact congrArg (fun f : ℝ → G.El => G.mat (f 1)) (he.unique (launches (tempo _ _ A)))

lemma physical (v : G.Color) : fderiv ℝ G.plog 1 (G.colorMat v)=v := by
  have hf : DifferentiableAt ℝ G.plog (G.mat (G.lieExp 0)) := by
    rw [G.mat_lieExp_zero, G.mat_one]; exact G.plog_diff.differentiableAt (by simp)
  have hh : (fun p : G.Color => G.plog (G.mat (G.lieExp p))) =ᶠ[𝓝 0] (fun x => x) := G.plog_left
  have ht := hh.fderiv_eq (𝕜:=ℝ)
  have hv := (hf.hasFDerivAt.comp 0 G.expDiff_zero).fderiv
  have hi := congrArg (fun t : G.Color →L[ℝ] G.Color => t v) (hv.symm.trans ht)
  simp only [G.mat_lieExp_zero,G.mat_one,ContinuousLinearMap.comp_apply,fderiv_fun_id] at hi
  exact hi

lemma first (x : Panel G d) : fderiv ℝ (stereo G d) 0 x=(∫ t in (0:ℝ)..1, field x.2.2 t) - x.2.1 := by
  let M (s : G.Color) := G.mat (G.lieExp s)
  have hf : M 0=1 := by simp [M]
  have he (v : G.Color) : HasDerivAt (fun t : ℝ => M (t • v)) (G.colorMat v) 0 := by
    exact G.expDiff_zero.comp_hasDerivAt_of_eq (0:ℝ) (show HasDerivAt (fun t : ℝ => t • v) v 0 from by
      simpa using (hasDerivAt_id' (0:ℝ)).smul_const v) (by simp)
  let p (t : ℝ) := M (t • x.1) * run G d (t • x.2.2) * star (M (t • (x.1+x.2.1)))
  have h0 : p 0=1 := by simp [p,hf,(endpoint G d).2.1]
  let y := ∫ t in (0:ℝ)..1, field x.2.2 t
  have hp : HasDerivAt p (G.colorMat (y-x.2.1)) 0 := by
    apply (((he x.1).mul ((endpoint G d).2.2 x.2.2)).mul (he (x.1+x.2.1)).star).congr_deriv
    simp only [Pi.mul_apply,zero_smul,hf,(endpoint G d).2.1,star_one,mul_one,one_mul,G.colorMat_skew,map_add,map_sub,star_add]
    unfold y; abel
  have hx := (G.plog_diff.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hp h0.symm
  have hs := ((scripts G d).1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) (show HasDerivAt
    (fun t : ℝ => t • x) x 0 from by simpa using (hasDerivAt_id' (0:ℝ)).smul_const x) (by simp)
  have hh : G.plog ∘ p= stereo G d ∘ fun t : ℝ => t • x := by
    funext v; simp [Function.comp,p,M,stereo,smul_add]
  rw [hh] at hx; exact (hs.unique hx).trans (physical _)
end YM.MultiNext.SignedSource.Pattern
