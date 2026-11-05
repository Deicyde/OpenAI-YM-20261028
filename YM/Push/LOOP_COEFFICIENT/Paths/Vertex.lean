import YM.Push.LOOP_COEFFICIENT.Paths.Production
import YM.Push.LOOP_COEFFICIENT.Paths.Synced

/-!
# Analytic, routed and bounded Hessian-vertex of the signed path action
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Matrix Function Filter Set Lattice Laurent Bloch RG Precision Wilson Work.F02 Complex
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {n : Side} {σ C Λ : ℝ} {W : PathData G} {p : Clip}

def localVertex (W : PathData G) (p : Clip) : Vertex (Axes G) (Axes G) (Axes G) := splitVertex (lane false) (lane true) fun _ => source (production W p)

open scoped Matrix.Norms.Frobenius in
lemma local_synced (h : W.Bounds p σ C Λ) : Synced (linksGrid G n) (linksGrid G n) (linksGrid G n) (actualMatrix (cost (mainTerm p W) ∘ vary 1)) (localVertex W p) := by
  obtain ⟨ρ,B,hρ,H⟩ := production_damped G p h.width C
  rw [show cost (mainTerm p W) ∘ vary (1:Config G n) = bank (channel n false) (channel n true) (mainTerm p W ∘ merged) from (funext (bank_channel (mainTerm p W))).symm]
  exact (H h).synced (Work.F02.mainTerm_contDiffAt h merged_diff) (.of_forall fun x => (production_real x h).symm) (channel_routed false) (channel_routed true)


end YM.Push.Loops.Paths
