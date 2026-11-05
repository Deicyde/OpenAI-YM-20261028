import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.Tactic
import YM.Analysis.Polydisc
import YM.Bid.Fuels
import YM.Org.Theatre
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.A15
import YM.Work.B04

/-!
# EVALUATION-unpriced uniform bounds: mixing nonanalytic neighborhoods

Converts local proof of left-Pitches for vacuum factors etc in the held
variables to the *unpriced* Window needed to differentiate. ONLY on
one torus; re-centering constants NOT used for systematic budgets.
No analyticity/equality of jets with poles/log sheet boundaries or on
only one side (moving across the output flag domain). It is enough
for `f` times the patch/kernel, not f alone, to pay these costs.

Idea for `capabilities` from compactness in Next.FOUNDATIONS.TestBounds.
Here charge the norm of the whole tensor in fixed vol, at any displacement
we have to use in the chosen V neighborhood. Do **not** infer symmetry
of left derivatives. Uses finite order `Analysis.sym_Jet`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Set Lattice RG Wilson
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {G : Gauge} {n : Side}
    {U : Config G n} {k : ℕ} {f : Ω → Config G n → ℂ}
local notation "I" => Directions G n

def UnitDirs : Directions G n→Prop := fun x => ‖x‖ ≤ 1

namespace Turning
section elementary
variable {E F D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma norm_comp_at {x : E} {f : E→F} {g : F→D} (hh : ContDiffAt ℝ k g (f x)) (hf : ContDiffAt ℝ k f x)
    {a b : ℝ} (he : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ a) (hv : ∀ j, 0<j → j≤k → ‖iteratedFDeriv ℝ j f x‖ ≤ b^j) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ k.factorial*a*b^k := by
  obtain ⟨t,ht,ho,hx⟩ := mem_nhds_iff.mp (hh.eventually (by simp)); have hg : ContDiffOn ℝ k g t :=
    ho.contDiffOn_iff.mpr fun _ hz => ht hz
  obtain ⟨s,hs,hp,hy⟩ := mem_nhds_iff.mp ((hf.eventually (by simp)).and (show ∀ᶠ v in 𝓝 x,f v ∈ t from hf.continuousAt
    (ho.mem_nhds hx)))
  have hu : ContDiffOn ℝ k f s := hp.contDiffOn_iff.mpr fun _ hz => (hs hz).1
  rw [← iteratedFDerivWithin_of_isOpen k hp hy]
  refine norm_iteratedFDerivWithin_comp_le hg hu le_rfl ho.uniqueDiffOn hp.uniqueDiffOn (fun _ hz => (hs hz).2) hy ?_ ?_
  · intro j hj; rw [iteratedFDerivWithin_of_isOpen j ho hx]; exact he j hj
  intro j hj hj'; rw [iteratedFDerivWithin_of_isOpen j hp hy]; exact hv j hj hj'

lemma along_second (x y : E) (j : ℕ) (hj : 0 < j) : ‖iteratedFDeriv ℝ j (fun z : E => (x,z)) y‖ ≤ 1 := by
  let L : E→L[ℝ] E × E := ContinuousLinearMap.inr ℝ E E
  have he : fderiv ℝ (fun z : E => (x,z)) = fun _ => L := funext fun v =>
    ((hasFDerivAt_const (x:=v) x).prodMk (hasFDerivAt_id (𝕜:=ℝ) v)).fderiv
  cases j
  · omega
  case succ j =>
    rw [iteratedFDeriv_succ_eq_comp_right,he, comp_apply, LinearIsometryEquiv.norm_map]; cases j
    · rw [norm_iteratedFDeriv_zero]; exact L.opNorm_le_bound zero_le_one fun a => by simp [L,Prod.norm_def]
    case succ j =>
      rw [iteratedFDeriv_const_of_ne j.succ_ne_zero,Pi.zero_apply]; exact (@norm_zero
        (ContinuousMultilinearMap ℝ (fun _ : Fin (j+1) => E) (E →L[ℝ] E × E)) _).trans_le zero_le_one

variable [FiniteDimensional ℝ E]
-- adapt to tensors on actual volume of this chart
private def tensor (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) : Submodule ℝ (Tensor.T E ℂ k) where
  carrier := {A | Tensor.Sym A}
  zero_mem' := fun _ _ => rfl
  smul_mem' r A ha x s := by
    change Tensor.Sym A at ha
    simp only [smul_apply,ha x s]
  add_mem' := fun {A B} (ha : Tensor.Sym A) (hb : Tensor.Sym B) x s => by
    simp only [add_apply,ha x s,hb x s]

-- fixed-tensor version of Next.Foundations' budget probes


end elementary



private def unroll (p : I × I) (i) := G.plog (G.mat (G.lieExp (p.2 i)*(G.lieExp (p.1 i))⁻¹))



private lemma respects (v : I) : ContDiffAt ℝ ω (fun p : I × I => (unroll p : I)) (v,v) := by
  apply contDiffAt_pi.mpr
  intro i
  let f (p : I × I) := G.mat (G.lieExp (p.2 i)*(G.lieExp (p.1 i))⁻¹)
  have h : f (v,v)=1 := by unfold f; simp only [mul_inv_cancel,G.mat_one]
  have hf : ContDiff ℝ ω f := by
    unfold f; simp_rw [G.mat_mul,G.mat_inv]; apply ContDiff.mul
    · exact G.exp_jet.comp ((contDiff_apply ℝ G.Color i).comp contDiff_snd)
    exact (starL' ℝ (A:=G.Mat)).contDiff.comp (G.exp_jet.comp ((contDiff_apply ℝ G.Color i).comp contDiff_fst))
  exact ContDiffAt.comp (f:=f) (g:=G.plog) (v,v) (h.symm ▸ G.plog_diff) hf.contDiffAt

variable (k) in
private lemma actions : ∃ b : ℝ, 1 ≤ b ∧ ∀ᶠ v in 𝓝 (0:I),
    ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i (fun t : I => (unroll (v,t) : I)) v‖ ≤ b := by
  let F (p : I × I) := (unroll p : I)
  let L := 1+∑ j : Fin (k+1),‖iteratedFDeriv ℝ j.val F 0‖
  have hL : 1≤ L := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => norm_nonneg _)
  have H : ∀ j : Fin (k+1), ∀ᶠ v in 𝓝 (0:I), ‖iteratedFDeriv ℝ j.val F (v,v)‖ ≤ L := by
    intro j
    have hz : Tendsto (fun v : I => (v,v)) (𝓝 0) (𝓝 0) := continuous_id.continuousAt.prodMk continuousAt_id
    refine hz.eventually ((show ContDiffAt ℝ ω F 0 from respects _).continuousAt_iteratedFDeriv (by exact le_top : (j.val:WithTop ℕ∞) ≤ ω) |>.norm |>.tendsto |>.eventually (ge_mem_nhds ?_))
    exact lt_of_le_of_lt (Finset.single_le_sum (f:=fun i : Fin (k+1) => ‖iteratedFDeriv ℝ i.val F 0‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ j)) (lt_one_add _)
  refine ⟨k.factorial*L, one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos k) hL,?_⟩
  filter_upwards [eventually_all.mpr H] with v hv i hi
  let f (p : I) := (v,p)
  change ‖iteratedFDeriv ℝ i (fun p => F (v,p)) v‖ ≤ _
  refine le_trans ((norm_comp_at (k:=i) (g:=F) (f:=f) (respects v|>.of_le le_top)
    (by unfold f; fun_prop) (b:=1) (a:=L) (fun j hj => hv ⟨j,by omega⟩) (fun j hj _ => ?_))) ?_
  · rw [one_pow]; exact along_second _ _ _ hj
  rw [one_pow,mul_one]; gcongr



end Turning
end YM.Further.DenseMixedKernels
