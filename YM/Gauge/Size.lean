import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Real
import YM.Gauge.Colors



/-!
# Elementary Haar-ball cost

Non-sharp (ambient FD packing, no ratio assumptions) and no
Tree Jacobian. Can use it even without a LocalRatio. Powers/stamps depend
only on gauge image. Chord normalization includes colorScale.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Gauge

open Filter Set MeasureTheory
open scoped Matrix.Norms.Frobenius BigOperators Topology ENNReal InnerProductSpace

variable (G : Gauge)
attribute [local instance] frobInner

def shell (r : ℝ) : Set G.El := {v | G.chord v ≤ r}
lemma shell_meas (r : ℝ) : MeasurableSet (G.shell r) := (isClosed_le G.continuous_chord continuous_const).measurableSet

private theorem package {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : V → E) (r γ : ℝ) (hr : 0 < r) (hm : r ≤ 1) (hg : 0 < γ) (hy : ∀ i, ‖Y i‖=γ)
    (q : Finset V) (hz : (q:Set V).Pairwise (fun i j => r*γ<‖Y i-Y j‖)) :
    (q.card:ℝ)*(r/4)^(Module.finrank ℝ E) ≤ 1 := by
  letI : MeasurableSpace E := borel _
  letI : BorelSpace E := ⟨rfl⟩
  letI : ProperSpace E := FiniteDimensional.proper ℝ _
  let μ : Measure E := Measure.addHaar
  haveI : Measure.IsAddHaarMeasure μ := by unfold μ; infer_instance
  let d := Module.finrank ℝ E
  let D := μ.real (Metric.ball 0 1)
  have fan (i : E) (R : ℝ) : μ (Metric.ball i R)<⊤ := measure_ball_lt_top
  have hD : 0 < D := (ENNReal.toReal_pos (by
    rw [ne_eq]
    exact ((Measure.IsOpenPosMeasure.open_pos _ Metric.isOpen_ball (Metric.nonempty_ball.mpr zero_lt_one)))) (fan _ _).ne)
  have he (a : E) (r : ℝ) (hr : 0 < r) : μ.real (Metric.ball a r)=r^d*D := by
    unfold D; rw [measureReal_def,Measure.addHaar_ball_of_pos μ _ hr,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]; rfl
  let C (i : V) : Set E := Metric.ball (Y i) (r*γ/2)
  let Pack (p : Finset V) := (p:Set V).Pairwise fun i j => r*γ<‖Y i-Y j‖
  have hc (i : V) : μ.real (C i) = (r*γ/2)^d*D := he _ _ (by positivity)
  have hi (p : Finset V) (hp : Pack p) : (p.card:ℝ)*(r/4)^d≤1 := by
    have hu : (⋃ x∈p,C x) ⊆ Metric.ball 0 (2*γ) := by
      refine iUnion_subset fun i => iUnion_subset fun j => ?_
      intro a ha
      have HH := norm_sub_le_norm_sub_add_norm_sub a (Y i) 0
      have hy' : ‖a-Y i‖<r*γ/2 := by simpa only [C, Metric.mem_ball, dist_eq_norm] using! ha
      rw [sub_zero, sub_zero, hy i] at HH
      rw [Metric.mem_ball,dist_zero_right]
      change ‖a‖ ≤ _+γ at HH
      linarith [mul_le_mul_of_nonneg_right hm hg.le]
    have hJ : PairwiseDisjoint (p:Set V) C := by
      intro i hui j huj h
      apply Set.disjoint_left.mpr
      intro x Hx Hy
      have he := norm_sub_le_norm_sub_add_norm_sub (Y i) x (Y j)
      have Hx' : ‖Y i-x‖<r*γ/2 := by rw [norm_sub_rev]; simpa only [C,Metric.mem_ball,dist_eq_norm] using! Hx
      have Hy' : ‖x-Y j‖<r*γ/2 := by simpa only [C,Metric.mem_ball,dist_eq_norm] using! Hy
      have hy : r*γ<‖Y i-Y j‖ := hp hui huj h
      linarith
    have hh := measureReal_mono (μ:=μ) hu (by exact (fan _ _).ne)
    rw [measureReal_biUnion_finset hJ (fun i _ => Metric.isOpen_ball.measurableSet) (fun i _ => (fan _ _).ne),he _ _ (by positivity)] at hh
    simp_rw [hc] at hh
    simp only [Finset.sum_const,nsmul_eq_mul] at hh
    apply le_of_mul_le_mul_right (a := (2*γ)^d*D) ?_ (by positivity)
    rw [one_mul]; refine Eq.trans_le ?_ hh
    rw [mul_assoc,← mul_assoc _ ((2*γ)^d),← mul_pow,show r/4 * (2*γ)=r*γ/2 by ring]
  exact hi q hz

/-- purely real. enough to use log arm. -/
theorem shell_ge (r : ℝ) (hr : 0 < r) (hm : r ≤ 1) :
    (r/4)^(Module.finrank ℝ G.Mat) ≤ G.probHaar.real (G.shell r) := by
  classical
  let d := Module.finrank ℝ G.Mat
  let γ := G.colorScale
  have hg : 0<γ := G.colorScale_pos
  let Pack (p : Finset G.El) := (p:Set G.El).Pairwise fun i j => r*γ<‖G.mat i-G.mat j‖
  have hi (p : Finset G.El) (hp : Pack p) : (p.card:ℝ)*(r/4)^d≤1 := package G.mat r γ hr hm hg
    (fun i => unitary_frob (G.mat_mul_star i)) p hp
  have cover : ∃ p : Finset G.El, Pack p ∧ ∀ i : G.El, ∃ a∈p, ‖G.mat a-G.mat i‖≤r*γ := by
    by_contra hh
    have hb (p : Finset G.El) (h : Pack p) : ∃ i : G.El, ∀ a∈p, r*γ < ‖G.mat a-G.mat i‖ := by
      push Not at hh
      exact hh p h
    have H (v : ℕ) : ∃ p : Finset G.El,p.card=v ∧ Pack p := by
      induction v with
      | zero => exact ⟨∅, Finset.card_empty, by unfold Pack; simp⟩
      | succ n h =>
        obtain ⟨p,h,H⟩ := h
        obtain ⟨j,hj⟩ := hb p H
        have hn : j∉p := by
          intro hh; have e := hj j hh; simp at e; exact not_lt_of_ge (mul_nonneg hr.le hg.le) e
        refine ⟨insert j p,by rw [Finset.card_insert_of_notMem hn,h],?_⟩
        intro x hx y hy h
        simp only [Finset.coe_insert, mem_insert_iff] at hx hy
        rcases hx with h₁|h₁ <;> rcases hy with h₂|h₂
        · exact False.elim (h (h₁.trans h₂.symm))
        · rw [h₁,norm_sub_rev]; exact hj y h₂
        · rw [h₂]; exact hj x h₁
        exact H h₁ h₂ h
    obtain ⟨N,hN⟩ := exists_nat_gt (1/(r/4)^d)
    obtain ⟨p,hp,hJ⟩ := H N
    exact (not_lt_of_ge (hp ▸ hi p hJ)) ((div_lt_iff₀ (by positivity)).1 hN)
  obtain ⟨p,hp,h⟩ := cover
  let x (i : G.El) := (fun x : G.El => i⁻¹*x) ⁻¹' G.shell r
  have H : (⋃ i∈p, x i) = univ := Set.eq_univ_of_forall fun j => by
    obtain ⟨i,hk,hℓ⟩ := h j
    refine mem_iUnion₂.mpr ⟨i,hk,?_⟩
    change G.chord (i⁻¹*j)≤_
    unfold chord
    apply (div_le_iff₀ hg).2
    rw [G.mat_mul, ← G.mat_one,← inv_mul_cancel i, G.mat_mul,← mul_sub, mul_frob_eq _ _ (G.mat_star_mul _),norm_sub_rev]; exact hℓ
  have hv (i) : G.probHaar.real (x i)=G.probHaar.real (G.shell r) := by
    have he := (measurePreserving_mul_left G.probHaar i⁻¹).measure_preimage (G.shell_meas r).nullMeasurableSet
    rw [measureReal_def, measureReal_def]; exact congr_arg ENNReal.toReal he
  have hx := measureReal_biUnion_finset_le (μ:=G.probHaar) p x
  rw [H] at hx; simp_rw [hv] at hx
  simp only [probReal_univ,Finset.sum_const,nsmul_eq_mul] at hx
  calc
    (r/4)^d ≤ ((r/4)^d)*((p.card:ℝ)*G.probHaar.real (G.shell r)) := le_mul_of_one_le_right (by positivity) hx
    _ ≤ G.probHaar.real (G.shell r) := by rw [← mul_assoc,mul_comm _ (p.card:ℝ)]; exact mul_le_of_le_one_left (by positivity) (hi p hp)
end YM.Gauge
