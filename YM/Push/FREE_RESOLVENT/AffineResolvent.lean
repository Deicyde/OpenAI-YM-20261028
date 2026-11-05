import YM.Push.FREE_RESOLVENT.AffineGap
import YM.Push.FREE_RESOLVENT.BlockRate
import YM.Push.FREE_RESOLVENT.JetShared

/-!
# Affine inverse jet outputs in actual unselected no-hole geometry

S and W inputs at the point chosen (V=1). Tree-fixed any. Works also at
all cut lengths and measures discrepancies under changes of cut length,
including the stencil-radius and true-length exponent in the same schedule
predicates. Complete Taylor-derivative costs (physical coords real).
Output includes a decay-payment for EVERY external V location.

Not presupposing Boot/running/W path choice.

Obtain q,W and Sheet
elsewhere.

This is not asking for an equality to a different period's
sector integrals nor any A root limit; no input about `V` switched across
trees.

Uses no-hole tags; no estimation of probabilities.

These stronger requests can consume these symbols and cut
estimates (see e.g., Costed.lean for tagged jet applications).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set Mark
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {k : ℕ} {W : PathData G} {A σ d : ℝ}

def footprint (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (k : ℕ) (A σ : ℝ) :=
  TestD.room (tier σ k) (stageCost G P K p k A σ) (headGap G P K p) k

def load (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (k : ℕ) (A σ : ℝ) :=
  torusPay (Co P.L (PAC G 1)) (footprint G P K p k A σ)

lemma situate (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) {k : ℕ} (h : 0 < σ) (hA : 0 ≤ A) :
    let M := stageCost G P K p k A σ; let r := headGap G P K p
    let d := footprint G P K p k A σ
    TestD.Price (tier σ k) M r d 1 (load G P K p k A σ) 1 k := by
  intro M r d
  have hp := stage_nn G P K p (k:=k) h hA
  have hx := headGap_pos G P K p
  have hm := (ordering h k).1
  exact ⟨hx,hp,hm,rfl,le_rfl,torusPay_nn _ _ (lt_of_lt_of_le ((room_grid hm hp hx k).1) le_rfl), zero_le_one,le_rfl⟩
lemma paid_size (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) {k : ℕ} (h : 0 < σ) (hA : 0 ≤ A) :
    let d := footprint G P K p k A σ
    0 < d ∧ 4*(k+1:ℕ)*d ≤ tier σ k ∧ d ≤ tier σ k := by
  intro d
  have hv := situate G P K p (k:=k) h hA
  have ht := hv.roomEnough.trans hv.roomTop
  have hd : 0 < d := hv.pos
  refine ⟨hv.pos,ht,le_trans ?_ ht⟩
  change d ≤ 4*(k+1:ℕ)*d
  push_cast; nlinarith only [hd, mul_nonneg (by positivity : 0 ≤ (k:ℝ)) hd.le]

variable (T : Forest S.ratio) (t : S.Choices) (h : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Larger (G:=G) S)
include h ha hW he

/-- Does NOT assume gap: use positive canonical contribution at identity. -/
lemma knows (p : Clip) (k : ℕ) (r : Admit) :
    let γ := footprint G S.patch S.kernel p k A σ
    Knew (marks G c γ) (native c) (theta _ T) (ray G c) 0 k (tier σ k) (stageCost G S.patch S.kernel p k A σ)
      (headGap G S.patch S.kernel p) 1 (primary S T t p W r) := by
  obtain ⟨h1,h2,h3⟩ := paid_size G S.patch S.kernel p (k:=k) h ha
  have hp := priority S he.2.2 h ha hW h1.le h3 he.1 T p r t
  intro γ
  refine ⟨hp.smooth,directGap S T t p W r he,?_ ,fun l h' hl => ?_⟩
  · simpa only [zeroth] using (Bill.reclaim (hp.bound [] (by simp)))
  rw [mul_one]; exact hp.bound l hl



/-- Exponentially small discrepancy of the whole affine inverse germ's
(real polarized) k-jet after cutting at R, including position & integrable
energy cost. -/
theorem shortening (p : Clip) (k R : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    let γ := footprint G S.patch S.kernel p k A σ; let a := headGap G S.patch S.kernel p
    let V := load G S.patch S.kernel p k A σ; let M := stageCost G S.patch S.kernel p k A σ
    let μ := phasePrice G S.patch S.kernel k A σ; let N := Real.exp (-(σ/4)*R)*(2*tagPrice 1 k μ μ)
    let C0 := meter k k M 1 (rise V a)*drain u
    Bundle (ray G c) (marks G c γ) (native c) (theta _ T) (theta _ T)
      (action (primary S T t p W (shorter R)) u-action (primary S T t p W all) u) 0 k γ
      (tagPrice 1 k (tagPrice 1 k C0 N) C0) := by
  intro γ a V M μ N C0
  have hp := knows T t h ha hW he p k all
  have hb := knows T t h ha hW he p k (shorter R)
  have hv := situate G S.patch S.kernel p (k:=k) h ha
  have hd := paid_size G S.patch S.kernel p (k:=k) h ha
  have ht : 0 ≤ N := mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) (tag_nn (phase_nn _ _ _ h ha) (phase_nn _ _ _ h ha)))
  apply hp.change hb hv hu (position_move _ _ hv.pos.le) (treeVolume _ T hv.pos) ht
  apply (tail_primary S he.2.2 h ha hW hd.1.le hd.2.2 R T p t).mono _ le_rfl
  refine le_trans ?_ hd.2.1
  have hn : 0 ≤ γ := hd.1.le
  change (2*(k+1:ℕ)+1)*γ ≤ _
  apply mul_le_mul_of_nonneg_right _ hn; push_cast; linarith [show 0 ≤ (k:ℝ) by positivity]

/-- Identical bounds when comparing to ANY principal window approximation
(Survey) with specified cover-distance cost. -/
theorem adjusting (p : Clip) (k : ℕ) (r : Admit) {u : ℝ} (hu : 0 ≤ u) {R : ℝ}
    {I : Active G T → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    (Z : Window.Survey I) (hp : Z.Near (native c) (theta _ T) R) :
    let γ := footprint G S.patch S.kernel p k A σ; let a := headGap G S.patch S.kernel p
    let V := load G S.patch S.kernel p k A σ; let M := stageCost G S.patch S.kernel p k A σ
    let C0 := meter k k M 1 (rise V a)*drain u
    Bundle (ray G c) (marks G c γ) (native c) (theta _ T) (theta _ T)
      (glimpse Z (primary S T t p W r) u-action (primary S T t p W r) u) 0 k γ
      (TestD.patchFee γ R M 1 V C0 k) := by
  intro γ a V M C0
  have hv := situate G S.patch S.kernel p (k:=k) h ha
  exact (knows T t h ha hW he p k r).discrepancy hv hu (position_move _ _ hv.pos.le) (treeVolume _ T hv.pos) hp
end YM.FreeResolvent.Affine
