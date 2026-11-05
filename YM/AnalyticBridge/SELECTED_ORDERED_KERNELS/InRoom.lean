import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Availability
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.NoHole

/-!
# Interpolation receipts on small open ball, uncut and cut operators

Driven by uniform nonlinear forward estimates & gap, with boundary rows
never removed and no change to the free affine model's active/frozen map.
Not a parameterization of actual continuous forest choices or path space.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Small
open Lattice Wilson RG Precision Tree Exterior Function Filter Topology Bloch Laurent Metric Matrix FreeResolvent Affine
  Lifted TestD Mark Set Lever NoHole WardBin.Lies
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {P : Patch} {K : KernelChoices} {n k : ℕ} {S : StepData c f} {p : Clip}
  {σ C M d η V r x : ℝ} {t : S.Choices} {B : Vec G c 1} {W : PathData G}

/-- Data estimator, *no-hole* case only. -/
def asset (P : Patch) (G : Gauge) (K : KernelChoices) (p : Clip) (σ : ℝ) (n : ℕ) (C M : ℝ) :=
  3*(squarePrice P G K p σ n C M + 1)
def stage (P : Patch) (G : Gauge) (K : KernelChoices) (p : Clip) (σ : ℝ) (n : ℕ) (C M : ℝ) :=
  room (tier σ n / 2) (asset P G K p σ n C M) (tariff G P K p) n

def volumeCost (G : Gauge) (P : Patch) (d : ℝ) := torusPay (Co P.L (PAC G 1)) d

lemma afford (P : Patch) (G : Gauge) (K : KernelChoices) (p : Clip) (hs : 0 < σ) (hM : 0 ≤ M) (hc : 0 ≤ C) (n : ℕ) :
    let d := stage P G K p σ n C M
    Price (tier σ n/2) (asset P G K p σ n C M) (tariff G P K p) d 1 (volumeCost G P d) 1 n := by
  intro d
  have hA : 0 ≤ asset P G K p σ n C M := mul_nonneg (by norm_num) (add_nonneg (square_nn hs hM hc K p) zero_le_one)
  have ht := half_pos (ordering hs n).1
  exact ⟨tariff_pos ..,hA,ht,rfl,le_rfl,torusPay_nn _ _ (room_grid ht hA (tariff_pos ..) n).1,zero_le_one,le_rfl⟩
lemma height {r s M d ε U V : ℝ} {k : ℕ} (p : Price (s/2) M r d U V ε k) : d ≤ s ∧ s/2 + k*d ≤ s ∧ (2*(k+1:ℕ)+1)*d ≤ s/2 := by
  have hd := p.pos; have h := p.roomEnough.trans p.roomTop; have hk : 0 ≤ k*d := by positivity
  push_cast at *; refine ⟨by linarith,by linarith, by linarith⟩

variable {T U : Forest S.ratio} {v : Site c}
variable (hs : 0 < σ) (hM : 0 ≤ M) (t : S.Choices) (h : Limits G S.patch S.kernel p σ M n k r C)
  (hB : ‖B‖ < r) (he : Bid.Larger (G:=G) S) (hW : Sheet W σ M) (hT : changed S T U v) (hx : x ∈ Icc (0:ℝ) 1)
include hs hM h hB he hW hT hx

def model (R : Admit) := mixture (around B (whole S T t p W R)) (around B (whole S U t p W R))

omit hs hM h hB he hW hT hx in
lemma model_left (R : Admit) (y : Vec G c 1) : model (T:=T) (U:=U) t (p:=p) (W:=W) (B:=B) R (y,0) = around B (over (paddedGram S t p W R T) 1) y := by
  simp [model,mixture,castLift,stir]; rfl
omit hs hM h hB he hW hT hx in
lemma model_right (R : Admit) (y : Vec G c 1) : model (T:=T) (U:=U) t (p:=p) (W:=W) (B:=B) R (y,1) = around B (over (paddedGram S t p W R U) 1) y := by
  simp [model,mixture,castLift,stir]; rfl

theorem limits (R : Admit) :
    let d := stage S.patch G S.kernel p σ n C M
    Knew (park (native c) hearth d v) (native c) (home S) (guides (ray G c)) (0,x) n
      (tier σ n/2) (asset S.patch G S.kernel p σ n C M) (tariff G S.patch S.kernel p) 1
      (model (B:=B) t (T:=T) (U:=U) (p:=p) (W:=W) R) := by
  intro d
  have hp := afford S.patch G S.kernel p hs hM h.nonneg n
  let a := squarePrice S.patch G S.kernel p σ n C M
  obtain ⟨hA,hF⟩ := (h.uniform (h:=S.sizes) hW hp.pos.le (height hp).1 he t B hB).1 R
  have hw : 0 ≤ a+1 := add_nonneg (square_nn hs hM h.nonneg ..) zero_le_one
  let Q T := around B (whole S T t p W R)
  let g := tariff G S.patch S.kernel p
  have hQ T : Bundle (ray G c) (marks G c d) (native c) (home S) (home S) (Q T) 0 n (tier σ n) (a+1) := Shell.padded _ hF
  have hg T : Gap (Q T 0) g := by unfold Q around; rw [zero_add]; exact Shell.gap (freeTo G S T) (A:=block S t p W R B) (hA T)
  have hY : Alert (home S) v (Q U-Q T) 0 := Shell.stocks _ _ (suits G _ hT) (around B (block S t p W R)) _
  have H := (Lever.buoy (hQ T) (hQ U) hw hY hp.pos.le (height hp).2.1 hx).mono le_rfl (show _ ≤ asset S.patch G S.kernel p σ n C M by
    change a+1 + (a+1+(a+1)) ≤ 3*(a+1); exact le_of_eq (by ring))
  refine ⟨H.smooth,gap_mixture (hg T) (hg U) hx.1 hx.2, ?_,fun l _ hl => ?_⟩
  · have h := H.bound [] (by simp); rw [zeroth] at h; exact h.reclaim
  rw [mul_one]; exact H.bound l hl


end YM.SelectedOrderedKernels.Small
