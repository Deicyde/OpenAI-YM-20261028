import YM.Push.LOOP_COEFFICIENT.AssemblyReal
import YM.Push.LOOP_COEFFICIENT.FineLine
import YM.Push.LOOP_COEFFICIENT.GaugeAlias
import YM.Push.LOOP_COEFFICIENT.PullEstimate




/-!
# One-step vertex data and tests for the logarithmic calculation

Intermediate ports; `Uses` demands identities of the jets of THE ACTUAL
operators and all the orientation choices, not a trace or coefficient
matching rule. Shape/gap, steering, slot-action and gauge calculus still
have to PAY these vertex bills in use. Same columns and representatives in
the two kinds of tests. Shear is only on `onBase` and unit Jacobian; do not
assume it preserves the full N by off-shell congruence. Positive coarse
width before L needed for iterative use, post-L constants inside `Regular`
OK in the numerical tests except where `Comparison`/`ShellBill` (separate)
require uniform instances. Fine-scale widths must fit the input path bills
when estimating on a given coarse strip. No terminal-period data in the
normalization choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Filter Set Lattice RG Wilson Precision Tree Bloch Laurent Exterior
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {L c f : Side} {p : Clip} {W : PathData G}

abbrev JointVertex (G : Gauge) (L : Side) := Vertex (Axes G) (JointType G L) (JointType G L)

structure LoopData (G : Gauge) (L : Side) where
  column : Cross L (TypeFace 1) (TypeFace 1)
  joint : JointVertex G L
  base : JointVertex G L
  ref : JointVertex G L
  charge : JointVertex G L
  vector : VecVertex G
  ghost : SiteVertex G

namespace LoopData
variable {g : Ratio c f}

def lift (R : LoopData G g.count) := installed g R.column

def rays (R : LoopData G L) := axisProfile G R.column

def target (R : LoopData G L) (W : PathData G) := (1/2:ℂ) • logKernel R.joint + collectPair R.rays (loopSymbol W - logKernel R.ghost)

def meshCost (_R : LoopData G L) (η C : ℝ) := logError (JointType G L) η C / 2 + pullCost L (Axes G) (axisCost L C) * logError G.ColorIndex (η/L.val) C


structure Regular (R : LoopData G L) (η C : ℝ) : Prop where
  col : Row.strip R.column η C
  start : GaugeAlias R.rays
  joint : LogStrip R.joint η C
  base : LogStrip R.base η C
  ref : LogStrip R.ref η C
  charge : ∃ e A, ChargeStrip R.charge e A
  vector : LogStrip R.vector (η/L.val) C
  ghost : LogStrip R.ghost (η/L.val) C

section matrices
open scoped Matrix.Norms.Frobenius

structure Uses (R : LoopData G g.count) (S : StepData c f) (p : Clip) (W : PathData G) : Prop where
  joint (t : S.Choices) : Synced (linksGrid G c) (jointGrid G g) (jointGrid G g) (actualMatrix (onVector p W t R.lift)) R.joint
  base (t : S.Choices) : ∃ χ, Sheared χ ∧ Synced (linksGrid G c) (jointGrid G g) (jointGrid G g) (actualMatrix (onAdjusted p W t R.lift χ)) R.base
  ref : Synced (linksGrid G c) (jointGrid G g) (jointGrid G g) (actualMatrix (onLarge p W (mu S) R.lift)) R.ref
  charge (t : S.Choices) : Charged (linksGrid G c) (jointGrid G g) (observed p W t R.lift) R.charge
  vector : Synced (linksGrid G f) (linksGrid G f) (linksGrid G f) (actualMatrix (onRef p W (mu S))) R.vector
  ghost : Synced (linksGrid G f) (nodesGrid G f) (nodesGrid G f) (actualMatrix (onGhost G (mu S))) R.ghost
end matrices

section analytic
open scoped Matrix.Norms.L2Operator
variable {R : LoopData G L} {η C σ D Λ : ℝ} {z : Momentum}
lemma fits (h : η/L.val ≤ σ) (hz : z∈Tube (η/2)) (k : Site L) : aliasAt z k∈Tube (σ/2) := tube_mono (show η/2/L.val ≤ σ/2 by rw [div_right_comm]; gcongr) (alias_tube k hz)
lemma Regular.rays_diff (h : R.Regular η C) (hz : z∈Tube (η/2)) (k : Site L) : ContDiffAt ℂ ω (fun p => R.rays p k) z := axis_diff h.col h.joint.width hz k
lemma Regular.collect_diff (h : R.Regular η C) (hz : z∈Tube (η/2)) {U : Momentum → Matrix (Axes G) (Axes G) ℂ} (hu : ∀ p∈Tube (η/L.val/2), ContDiffAt ℂ ω U p) :
    ContDiffAt ℂ ω (collectPair R.rays U) z := collect_analytic (fun k => hu _ (fits le_rfl hz k)) (fun k => ⟨(h.rays_diff (tube_neg hz) k).comp z (f:=(-·)) (by fun_prop), h.rays_diff hz k⟩)
lemma Regular.target_diff (h : R.Regular η C) (hw : W.Bounds p σ D Λ) (hf : η/L.val ≤ σ) (hz : z ∈ Tube (η/2)) : ContDiffAt ℂ ω (R.target W) z := by
  exact ((logKernel_analytic h.joint hz).const_smul (1/2:ℂ)).add (h.collect_diff hz (fun _ he => ((loop_diffAt hw.width (loopRow_budget hw.width hw.two) (tube_mono (show η/L.val/2 ≤ σ/2 by gcongr) he)).sub (logKernel_analytic h.ghost he))))
lemma logKernel_period {a d : Type} [Fintype a] [DecidableEq a] [DecidableEq d] {U : Vertex d a a} (h : LogStrip U η C) (hz : z∈Tube (η/2)) (x : Cover) : logKernel U (z+reciprocal x) = logKernel U z := by
  ext i j; exact (h.log_vane i j).reset z hz x
lemma Regular.target_period (R : LoopData G L) (h : R.Regular η C) (W : PathData G) (hz : z∈Tube (η/2)) (x : Cover) : R.target W (z + reciprocal x) = R.target W z := by
  dsimp only [target,Pi.add_apply,Pi.smul_apply]
  apply congr_arg₂ (· + ·) (congr_arg ((1/2:ℂ) • ·) (logKernel_period h.joint hz x)); exact collect_periodic
    (fun k y => congr_arg₂ (· - ·) (loop_period W (aliasAt z k) y) (logKernel_period h.ghost (fits le_rfl hz k) y)) x (fun _ => ⟨axis_shift ..,axis_shift ..⟩)
end analytic
end LoopData

lemma ratio_mu (S : StepData c f) (g : Ratio c f) : mu S = (g.count.val:ℝ)⁻¹ := by rw [mu, Nat.eq_of_mul_eq_mul_left c.property (S.sizes.symm.trans g.exact_size)]
lemma ratio_exp (g : Ratio c f) (η : ℝ) : Real.exp (-(η/g.count.val/8)*f.val) = Real.exp (-(η/8)*c.val) := by rw [g.exact_size, Nat.cast_mul]; congr 1; field_simp

open LoopData
open scoped Matrix.Norms.Frobenius
namespace LoopData.Uses
variable {S : StepData c f} {g : Ratio c f} {R : LoopData G g.count} {η C : ℝ}
variable (h : Uses R S p W (g:=g)) (hr : R.Regular η C)
variable {F : Forest S.ratio} {ρ : fieldDir G c 1 → AxisChart G F} {P : ChartRatio G}
include h hr
lemma refUnit : IsUnit (reference (mu S) p W (1 : Config G f)) := by simpa only [onRef,vary_zero] using! h.vector.unit hr.vector
lemma compare_branch (ha : Admission F ρ p W (R.lift (g:=g)) P) (t : S.Choices) :
    Compares (linksGrid G c) (linksGrid G c) (Coeff (onBranch t p W (R.lift (g:=g)))) (R.target W) (R.meshCost η C * Real.exp (-(η/8)*c.val)) := by
  obtain ⟨_,_,_,hw⟩ := ha.paths
  have he := log_compares onGhost_diff h.ghost hr.ghost
  have hη := hr.joint.width
  let A := linksGrid G f
  have hh : Compares A A (Coeff (loop W ∘ vary 1)) (loopSymbol W) 0 := by rw [Coeff,(loop_jets_real hw.width hw.two).2.2]; exact loop_compares (Row.rights _ _ (loopRow_budget hw.width hw.two) hw.width.le)
  have hp := (A0_projects (G:=G) (g:=g) R.column (Row.rights _ _ hr.col hη.le)).compares (fun _ hp => axis_bound hr.col hη.le hp) (hh.sub he)
  have hj := (log_compares (onVector_diff ha.branches hw) (h.joint t) hr.joint).smul (1/2:ℂ)
  rw [branch_coeff t ha]; exact (hj.add hp).mono (by rw [norm_div,norm_one,Complex.norm_two,meshCost,add_mul,ratio_exp g,zero_add]; linarith)
end LoopData.Uses
end YM.Push.Loops
