import YM.Push.STATIONARY_UNIFORM.Along

/-!
# Application to stationarity on a common continuation

Pre-select `Menu` comparing costs for ALL continuations. Can use estimates
at individual steps before continuation is completed. Does not require
selecting params after learning L. Doesn't deliver these path kernels at
output from stationarity. The application here on a Calendar still requires
PATH bounds, and size `margin` (can pay before use). Compare readouts to the
stationary_scene/Guessed and thermal blocks choosing a single one of these
branches. Share all lengths, stages, tags, PathData with them.

The alpha field in Kin is passed through, no estimates on alpha claimed or
needed. If producer has chosen *local* germs from Scene before prices,
there's also a lemma recovering the same germs by Service; does not authorize
changing path coefficients after any evaluation. This is not a `Planned`
producer!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior Bid Laurent
open Work.F03 Work.F04  Matrix
open Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

section Link
variable {G : Gauge} {c f : Side} {S : StepData c f} {B : Forest S.ratio} {R : PathData G} {p : Clip}
variable {μ C Λ : ℝ} {n j : ℕ} {Q : KernelChoices} {A : Before G μ C j Q n} {g u : In G c → AxisChart G B}

/-- Preserve a solution passed as a Critical germ. (As usual no requirement
on a dormant part of `u` outside what its germ specifies.) -/
lemma Before.Service.is_extension (hg : A.Service B p R g) (h : Critical B p R u) : u=ᶠ[𝓝 0] g := by
  let P := A.tables p S.patch
  let F (x : In G c) := (tint G _).symm x
  have hf : Tendsto F (𝓝 0) (𝓝 0) := by unfold F; simpa using (tint G (Body 1 c)).symm.continuous.tendsto 0
  let J (x : In G c) := (tint G _).symm (u x)
  have hh : Tendsto J (𝓝 0) (𝓝 0) := by
    have he := ((tint G B.Free).symm.continuousAt (x:=u 0)).comp h.2.1.continuousAt
    simpa only [J, Function.comp_def,h.1,map_zero] using he.tendsto
  let t : S.Choices := Classical.arbitrary _
  filter_upwards [hf.eventually (ball_mem_nhds _ hg.x_pos), hh.eventually (ball_mem_nhds _ hg.zone_pos), (h.2.2 t).2] with x hx hj hk
  exact ((hg.2.2.2.2.2.2 x hx).2.2 t _ (ball_subset_closedBall hj)).1 hk


end Link

section Path

variable (G : Gauge)

def Menu (P : ℕ → Stage) (Q : KernelChoices) := ∀ i : ℕ, Before G (P i).width (P i).paths i Q (P i).order



variable {G} {S : Levels G}





-- costs selected from `Menu`; coherence exposes whole plateau, not selected per period or under paths

def fare (K : Menu G S.clock.stage S.clock.kernel) (i p : ℕ) : ChartPrices :=
  (K (S.clock.J (i+1))).tables (S.params (i+1)).clip (S.clock.op i p).patch

lemma duration (K : Menu G S.clock.stage S.clock.kernel) (i j p q : ℕ) (h : S.clock.J (i+1)= S.clock.J (j+1)) : fare K i p=fare K j q := by
  unfold fare Levels.params Calendar.params
  rw [h]; have he : (S.clock.op i p).patch=(S.clock.op j q).patch := by
    have hL : (S.clock.op i p).patch.L=(S.clock.op j q).patch.L := by
      change S.S.block i=S.S.block j
      rw [← S.fits.sameFactor i, ← S.fits.sameFactor j,h]
    have hJ : (S.clock.op i p).patch.J=(S.clock.op j q).patch.J := h
    generalize (S.clock.op i p).patch=P at *; generalize (S.clock.op j q).patch=Q at *; cases P; cases Q; congr
  rw [he]


end Path
end YM.Push.Uniform
