import YM.Extra.MULTISOURCE_TRAJECTORIES.KernelReads
import YM.Extra.MULTISOURCE_TRAJECTORIES.Signals


/-!
# Adjoint transport of true supports and spectators

Advancing (i.e. coarse observable to fine field) with shared random kernel.
Output of repeated adjoints reads within iterated full pullback, also usable
with `inspected` supports via UsesFinal. Exact operator identity against joint
physical products on any of the preceding lanes. This is neither integration
of an unnormalized coefficient down on its coarse projected support alone,
nor a tree estimate. Opposite directions have different supports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories.Reverse
open Lattice Wilson RG Function Filter MeasureTheory Marker Overlay Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}

section Step
variable {c f : Side} (S : StepData c f) (β : ℝ)

def adjoint (F : Config G c → ℂ) (U : Config G f) := ∫ V, S.density β U V • F V ∂prior G c

lemma cost (hk : S.IsKernel β G) {F : Config G c → ℂ} {b : ℝ} (h : ∀ U,‖F U‖≤ b) (U : Config G f) : ‖adjoint S β F U‖ ≤ b := by
  have he V : ‖S.density β U V • F V‖ ≤ S.density β U V * b := by
    rw [norm_smul, Real.norm_of_nonneg (hk.positive ..)]; gcongr; exacts [hk.positive ..,h V]
  exact (norm_integral_le_of_norm_le ((hk.integrable _).mul_const b) (Eventually.of_forall he)).trans_eq
    ((integral_mul_const ..).trans (by rw [hk.total, one_mul]))



def lens (Q : Config G c) (F : Config G c → ℂ) := ∫ V, S.noise β Q V • F V ∂prior G c






end Step

variable {N m p : ℕ} (H : RG.History G)

def shell (D : Support (H.S.side m p)) (j : ℕ) : Support (H.S.side j p) :=
  if h : j=m then h.symm ▸ D else match j with
    | 0 => univ
    | j+1 => pullback (H.levels.clock.op j p) (shell D j)

def lift (N : ℕ) (F : Config G (H.S.side m p) → ℂ) (j : ℕ) : Config G (H.S.side j p) → ℂ :=
  if h : j=m then h.symm ▸ F else match j with
    | 0 => 0
    | j+1 => adjoint (H.levels.clock.op j p) (H.β N p (j+1)) (lift N F j)






variable {H} {V : Type} [DecidableEq V] {R : Census V} (A : Insertions H V N p)

def charge (s : R.Mode) (j : ℕ) := ∏ i∈Finset.Ico m j,Ride.bump (H.S.block i).val s A.load


end YM.Extra.Trajectories.Reverse
