import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Collective
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Polish
import YM.Progress.JOINT_CALENDAR.Issue
import YM.Push.PRICE_COMPILER.Post


/-!
# Uniform persistence of an implicit system: local real sup

Radius earned from displacement and contraction after reference step-inverse;
even if implicit germ for one fixed period is available, it alone would
not pay this margin. Hesitant germ statements elsewhere keep exactly these
prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Polish
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius NNReal
namespace Basin
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Y] [CompleteSpace X] [CompleteSpace Z] {r t A B C : ℝ}

section orbit
variable {f : Y→Y} (hf : ∀ x, ‖x‖ ≤ r → DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x‖ ≤ 1/2) (hr : 0<r) (h₀ : ‖f 0‖ ≤ r/4)
include hf
omit [CompleteSpace Y] in
lemma entry {x y : Y} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖f x-f y‖ ≤ (1/2:ℝ)*‖x-y‖ := by
  apply (convex_closedBall (0:Y) r).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ)
    (fun i hi=> (hf i ((dist_zero_right i) ▸ hi)).1) (fun i hi=> (hf i ((dist_zero_right i) ▸ hi)).2)
    (Metric.mem_closedBall.mpr (by rwa [dist_zero_right])) (Metric.mem_closedBall.mpr (by rwa [dist_zero_right]))
omit [CompleteSpace Y] in
lemma forms {x y : Y} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hh : f x=x) (hk : f y=y) : x=y := by
  have he := entry hf hx hy; rw [hh,hk] at he
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by linarith) (norm_nonneg _)))
include hr h₀
lemma exacts : ∃ x : Y, ‖x‖ < r ∧ f x=x := by
  have hu : ‖(0:Y)‖ ≤ r := by simp only [norm_zero]; exact hr.le
  have hd (x : Y) (he : ‖x‖ ≤ r) : ‖f x‖ < r := by
    have h := entry hf he hu
    have he' := (norm_add_le (f x-f 0) (f 0)); rw [sub_add_cancel] at he'; rw [sub_zero] at h; linarith
  let w := Metric.closedBall (0:Y) r
  have hw x : x∈w ↔ ‖x‖ ≤ r := by simp [w]
  have ht : Set.MapsTo f w w := fun y hy=> (hw _).mpr (hd _ ((hw y).mp hy)).le
  have he : ContractingWith (1/2:ℝ≥0) (ht.restrict f w w) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun ⟨x,hx⟩ ⟨y,hy⟩ => ?_⟩
    change dist (f x) (f y) ≤ (↑(1/2:ℝ≥0):ℝ)* dist x y
    simpa only [Set.restrict_apply,Subtype.dist_eq, dist_eq_norm,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one] using entry hf ((hw _).mp hx) ((hw _).mp hy)
  have hC : IsComplete w := Metric.isClosed_closedBall.isComplete
  obtain ⟨x,hx,h,-⟩ := he.exists_fixedPoint' hC ht ((hw _).mpr hu) (edist_ne_top (0:Y) _)
  exact ⟨x,h ▸ hd x ((hw _).mp hx),h⟩
end orbit
variable {g : X × Y→ Z}

structure Span (g : X × Y → Z) (q : Z→L[ℝ] Y) (t r : ℝ) : Prop where
  growth : 0<t
  ripe : 0<r
  inject : Injective q
  infty {x : X × Y} : ‖x.1‖≤t → ‖x.2‖≤ r → ContDiffAt ℝ ω g x
  inverse {x : X × Y} : ‖x.1‖≤t → ‖x.2‖≤r → (fderiv ℝ g x ∘L .inr ℝ X Y).IsInvertible
  lesser {x : X × Y} : ‖x.1‖≤t → ‖x.2‖≤r → ‖.id ℝ Y - q ∘L (fderiv ℝ g x ∘L .inr ℝ X Y)‖ ≤ 1/2
  extent {x : X} : ‖x‖ ≤ t → ‖q (g (x,0))‖ ≤ r/4

namespace Span
variable {q : Z→L[ℝ] Y} (h : Span g q t r)
include h

def target (g : X × Y→Z) (q : Z→L[ℝ] Y) (x : X) (y : Y) := y - q (g (x,y))
omit [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z] in
lemma solves (x : X) (y : Y) : target g q x y=y ↔ g (x,y)=0 := ⟨fun i=> h.inject (by simp [target] at i; rw [map_zero]; exact i),fun i=> by simp [target,i]⟩
omit [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z] in
lemma makes {x : X} (ht : ‖x‖ ≤ t) {y : Y} (hh : ‖y‖ ≤ r) :
    DifferentiableAt ℝ (target g q x) y ∧ ‖fderiv ℝ (target g q x) y‖ ≤ 1/2 := by
  let A := fderiv ℝ g (x,y) ∘L ContinuousLinearMap.inr ℝ X Y
  have he := h.infty (x:=(x,y)) ht hh
  have hb : HasFDerivAt (fun v:Y => g (x,v)) A y := (he.differentiableAt (by simp)).hasFDerivAt.comp y ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id _))
  have hp : HasFDerivAt (target g q x) (.id ℝ Y-q ∘L A) y := (hasFDerivAt_id y).sub (q.hasFDerivAt.comp y hb)
  exact ⟨hp.differentiableAt,hp.fderiv.symm ▸ h.lesser (x:=(x,y)) ht hh⟩
omit [CompleteSpace X] [CompleteSpace Z] in
lemma takes {x : X} (ht : ‖x‖ ≤ t) : ∃ y : Y, ‖y‖<r ∧ g (x,y)=0 := by
  have hp : ‖target g q x 0‖ ≤ r/4 := by simpa [target] using h.extent ht
  obtain ⟨v,hv,H⟩ := exacts (fun y hy=> h.makes ht hy) h.ripe hp
  exact ⟨v,hv,(h.solves x v).1 H⟩
omit [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z] in
lemma harmony {x : X} (ht : ‖x‖ ≤ t) {y z : Y} (hh : ‖y‖ ≤ r) (hk : ‖z‖ ≤ r) (hy : g (x,y)=0) (hz : g (x,z)=0) : y=z :=
  forms (fun _ hy=> h.makes ht hy) hh hk ((h.solves x y).mpr hy) ((h.solves x z).mpr hz)

def branch (x : X) : Y := if hx : ‖x‖ ≤ t then (h.takes hx).choose else 0
omit [CompleteSpace X] [CompleteSpace Z] in
lemma purchase {x : X} (he : ‖x‖ ≤ t) : ‖h.branch x‖<r ∧ g (x,h.branch x)=0 := by unfold branch; rw [dif_pos he]; exact (h.takes he).choose_spec

end Span
end Basin
end YM.AnalyticNext.QuarticMatch.Radius
