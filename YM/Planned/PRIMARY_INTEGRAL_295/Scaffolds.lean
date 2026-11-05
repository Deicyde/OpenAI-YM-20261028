import YM.Planned.PRIMARY_INTEGRAL_295.Bazaars
import YM.Planned.PRIMARY_INTEGRAL_295.Catalogue


/-!
# Using bounded thermal inputs true on Torus

Proof on actual Dir G c and real gauge.

`Processing` pre-planned theta kernel
row width C/L, inherited frame.

Additional spare a phase finance for
kernel stamp.

This stage NO Bury re-fitting.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Bazaars
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Dunes Place Emits Ripple
open Precision Exterior Tree Streets Porous Carrier Bloch Next.Free Progress.StationaryScenes
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical NNReal ENNReal
variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
variable {G : Gauge} {T : Finset Cover} {k l d : ℕ} {t ξ s M δ : ℝ} {F : Labels.Frame G d} {c f : Side}
variable {S : StepData c f}

section Product
variable {Y F : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup F] [NormedSpace ℝ F]


lemma chainFee (L : Y→L[ℝ] F) (Q : E→L[ℝ] Y) (hL : ‖L‖≤1) (C : ℝ) (hQ : ‖Q‖≤C) : ‖L ∘L Q‖ ≤ C := by
  have hp:0≤C:=(norm_nonneg Q).trans hQ; apply ContinuousLinearMap.opNorm_le_of_unit_norm hp; intro x hx
  have he : ‖Q x‖≤ C := (Q.le_opNorm _).trans (by simpa [hx])
  apply (L.le_opNorm _).trans; exact (mul_le_of_le_one_left (norm_nonneg _) hL).trans he
end Product

namespace Launch
variable (h : Launch I E G S) (B : Roof T G) (W : Lines S.ratio.count)

/-- y.Mark. M = post budget across all. u sufficient for lower mean/probe b-field costs.
    g/f comparison ξ. All costs at true stencil not inferred. -/
structure Permit (T : Finset Cover) (k:ℕ) (u s : ℝ) : Prop where
  generation : ContDiffAt ℝ k h.b 0 ∧ Oval.Envelope 0 k h.b u
  scene : ContDiffAt ℝ k (h.muCut T) 0 ∧ Fuzz 0 k (h.muCut T) (h.muLin T W) (u*s)

structure Soak (ξ:ℝ) (k : ℕ) (M : ℝ) : Prop where
  size : (Fintype.card I:ℝ) ≤ M
  noiseMap : ‖h.probe‖≤M
  crown : ContDiffAt ℝ k h.variation 0 ∧ Oval.Envelope 0 k h.variation M
  invert : ∃ N:ℝ, 0≤N ∧ ∀ x:Sky I, ‖x‖ ≤ N*‖h.variation 0 x‖
  profile : ContDiff ℝ k h.gamma ∧ ∀ z, Oval.Envelope z k h.gamma M
  cover : ∀ z, h.gamma z ∈ Icc 0 1 ∧ (M * ξ * ‖z‖ ≤ 1 → h.gamma z=1) ∧ (M < ξ*‖z‖ → h.gamma z=0)

/-- Used for multiple purchases. Order and λ K harmon predecessor. -/
def stairs (G : Gauge) (j:ℕ) (σ C : ℝ) :=
    2+fee G*(Response.correction j σ C + Response.total j σ C + Real.exp σ)


section
variable {σ C : ℝ} (hσ : 0≤σ) (hT : W.strip σ (C / (S.ratio.count.val:ℝ)))
include hσ hT
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma stars : ‖wall f T G ∘L axisPhi S h.tree W‖ ≤ stairs G S.patch.J σ C - 2 := by
  apply chainFee _ _ (wall_cost ..)
  apply (surf_cost G S h.tree W hσ hT).trans
  unfold stairs; rw [add_sub_cancel_left,mul_add,mul_add];
  have hf:=fee_pos G; have hl:=Response.nonneg S.patch.J σ C
  have ht : 0 ≤ Response.total S.patch.J σ C := by unfold Response.total Response.correction; positivity
  nlinarith [mul_nonneg (zero_le_one.trans hf) ht, mul_nonneg (zero_le_one.trans hf) (Real.exp_pos σ).le]

omit hσ hT [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma counted : ‖meets T S h.tree (G:=G)‖ ≤ 1 :=
    chainFee (terrace f T G) (streamFill S h.tree) (terr_cost ..) _ (stream_cost (G:=G) S h.tree)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma total_aim : ‖meets T S h.tree ∘L crick S h.tree W (G:=G)‖ ≤ stairs G S.patch.J σ C - 2 := by
  apply chainFee (meets T S h.tree (G:=G)) (crick S h.tree W) (counted (T:=T) h)
  apply (aim_cost G S h.tree W hσ hT).trans; unfold stairs; rw [add_sub_cancel_left];
  have ht:=Response.nonneg S.patch.J σ C; have hf:=fee_pos G
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hf)
  have hh : 0 ≤ Response.correction S.patch.J σ C:=by unfold Response.correction; positivity
  linarith
end

section Permit
variable {σ C u : ℝ} (hσ : 0≤σ) (hT : W.strip σ (C / (S.ratio.count.val:ℝ)))
variable (hp : h.Permit W T k u s) {Q:E→Dev T G} (ht : t∈Ioc 0 1) (hs : s∈Icc 0 1) (hξ : ξ∈Ioc 0 1)
variable (hv : h.Soak ξ k M) (ha : t*(2*M+ M^2)≤B.radius)

include hσ hT hp hs

-- solve serve requirement. h.b includes w.r.t. t units, still need
-- b-domain normalization and meeting `Credit/Watch` before Stamp.


include ht hξ hv ha


end Permit
end Launch
end YM.Planned.PrimaryIntegral295.Bazaars
