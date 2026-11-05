import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Lyres
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.PMOM

set_option warningAsError false

/-!
# Leading attenuation with JHs & polynomial moments ( etc)

Segment version requiring JUST k≥d+1 for projected-null degree d.
Applied to t normalized log. Uniform arities up to k.  
No hypothesis that
position arrays match degree apart from the slots Y whose PMOM price
is tested later. Need costs purchased BEFORE L, here dependence listed
as operator constants & d, k, G. This estimate isn't stepping on fake
measures: uses actual Hol and lifted positions for THIS configuration.
Still need small curl & chart input plus JsT BEFORE L and local rate
for errors – none derived here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Banjo
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open Mom Next.Foundations Lyre
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {d : ℕ} {L r C : ℝ} {P : BudgetPoint} {o : Site n} {X : Support n}

/-- Input that has passed S, for a fixed test direction (position or
sensitivity). Raw scaled, not evaluated on protected cells with
independent translations. Fee C fixed before L. Also works with
finite data that don't originate from full kernels but these are not claims
tested here.
Use indices Fin(r+1), with exponent j.val+1. Last index (=r)
has no restriction to Maps (tail T). This is JsT egress used only on
one specialized read (possibly periodic). -/
def Promise (d : ℕ) (C r : ℝ) (P : BudgetPoint) (o : Site n) (X : Support n) (v : Directions G n) :=
    ∃ w : Fin (d+1) → Directions G n,v=∑ i,w i ∧ (∀ i,Sized (C*r^(i.val+1)) (w i) P o) ∧
    ∀ i : Fin (d+1),i.val<d → screen X (w i)∈Maps o X (i.val+1)

lemma Promise.shot {v : Directions G n} (h : Promise d C r P o X v) (hr : 0 ≤ r) (ht : r ≤ 1) (hc : 0 ≤ C) :
    Sized (((d:ℝ)+1)*C*r) v P o := by
  obtain ⟨x,rfl,hx,-⟩:=h
  refine ⟨by positivity,fun j => ?_⟩
  rw [Finset.sum_apply]; let u := Lyre.width P o j; have hu : 0≤u := (width_pos ..).le
  calc
    _ ≤ ∑ i,‖x i j‖ := norm_sum_le ..
    _ ≤ ∑ _i : Fin (d+1),C*r*u := sum_le_sum fun i _ => (hx i).2 j |>.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by rw [pow_succ]; exact mul_le_of_le_one_left hr (pow_le_one₀ hr ht)) hc) hu)
    _ = _ := by simp [nsmul_eq_mul,u]; ring






end YM.MultiNext.SignedSource.Banjo
