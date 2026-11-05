import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.InRoom
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Transfer

/-!
# Non-flat Lie budgets for the actual no-hole free affine prescription

An extra strengthening (NOT an input from a selected-sector task). Arbitrary
fixed order, arbitrary full principal sets and column windows, small-field
open ball in ONE trivialization about 1, cuts even on periodic seams, includes
B variations and one common tree switch. Both fields in a subtraction in the
same volume/coordinates here. Compare Period for nonwrapping cross readings
at the Taylor point only. Rate and all prefactors below can depend on L and
the other `Limits` data, do not return them to a pre-L clock. The receipt
retains exponential gains from nozzle margin and cut where applicable, and
integrable at positive orders, or any order in tag/change clauses.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Small
open Lattice Wilson RG Precision Tree Exterior Function Filter Topology Bloch Laurent Metric Matrix FreeResolvent Affine
  TestD Mark Set Lever NoHole Window
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {P : Patch} {K : KernelChoices} {n k j : ℕ} {S : StepData c f} {p : Clip}
  {σ C M d η r x u ρ : ℝ} {t : S.Choices} {B : Vec G c 1} {W : PathData G}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → raw G f}
  {I : raw G f → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

abbrev forecast (P : Patch) (G : Gauge) (K : KernelChoices) (p : Clip) (σ : ℝ) (n : ℕ) (C M : ℝ) :=
  volumeCost G P (stage P G K p σ n C M)
def purse (P : Patch) (G : Gauge) (K : KernelChoices) (p : Clip) (σ : ℝ) (n : ℕ) (C M : ℝ) :=
  meter n n (asset P G K p σ n C M) 1 (rise (forecast P G K p σ n C M) (tariff G P K p))
def crumb (P : Patch) (G : Gauge) (K : KernelChoices) (p : Clip) (σ : ℝ) (n : ℕ) (C M ρ u : ℝ) := patchFee (stage P G K p σ n C M) ρ
    (asset P G K p σ n C M) 1 (forecast P G K p σ n C M) (purse P G K p σ n C M*drain u) n
def cutback (P : Patch) (G : Gauge) (K : KernelChoices) (p : Clip) (σ : ℝ) (n R : ℕ) (C M u : ℝ) :=
  let e := purse P G K p σ n C M * drain u
  tagPrice 1 n (tagPrice 1 n e (3*tailPrice P G σ n R C M)) e

variable (p : Clip) (hs : 0 < σ) (hM : 0 ≤ M) (t : S.Choices) (h : Limits G S.patch S.kernel p σ M n k r C)
  (hB : ‖B‖ < r) (he : Bid.Larger (G:=G) S) (hW : Sheet W σ M) (hu : 0 ≤ u) (hk : k<n)
include hs hM h hB he hW hu hk

omit hs hM h hB he hW hu hk in
private lemma two_modes (H : ℝ) (p : OrderedFinpartition j) : charges p.length 1 H (drain u) ≤ charges j 1 H (drain u) ∧
    charges (p.length+1) 1 H (drain u) ≤ H*drain u*drain u := ⟨(part_charges ..).le,by rw [charges,if_neg (by simp),mul_one]⟩



lemma near (R : Admit) (Z : Survey I) :
    let d := stage S.patch G S.kernel p σ n C M; let E := purse S.patch G S.kernel p σ n C M; let V := forecast S.patch G S.kernel p σ n C M
    Paid S (home S) k (narrow n d) d (3*(n+1:ℕ)*d) (fun j => offFee G j * (V * charges j 1 E (drain u)))
      (fun j => offFee G j * (V*(E*drain u*drain u))) (fun T => columns Z (paddedGram S t p W R T) u) (increment 1 (paint G c B)) := by
  intro d E V; have hp := afford S.patch G S.kernel p hs hM h.nonneg n
  have hy := (drain_pos hu).le; have hE := hp.meter_abs
  apply aux_pass (m:=fun j => V*charges j 1 E _) (e:=V*(E*drain u*drain u)) (B:=B) ?_ hp.pos.le hk (h.safe _ hB)
    (mul_nonneg hp.vol (mul_nonneg (mul_nonneg hE hy) hy)) (fun j _ => mul_nonneg hp.vol (charges_nn _ zero_le_one hE hy))
    (fun j _ p => ⟨mul_le_mul_of_nonneg_left (two_modes E p).1 hp.vol,mul_le_mul_of_nonneg_left (two_modes E p).2 hp.vol⟩)
  intro T U v hv
  let F := glimpse Z (model (T:=T) (U:=U) (B:=B) (p:=p) (W:=W) t R) u
  have hF (x) (hx : x∈Icc (0:ℝ) 1) := limits hs hM t h hB he hW hv hx R
  exact ⟨F,fun y => by unfold F glimpse; rw [model_left]; rfl,fun y => by unfold F glimpse; rw [model_right]; rfl,
    fun x hx => ⟨glimpse_smooth (hF x hx) _ hu hp.r0,glimpse_rates (hF x hx) hp Z hu (position_move _ _ hp.pos.le) (home_volume _ _ _ hp.pos)⟩⟩




end YM.SelectedOrderedKernels.Small
