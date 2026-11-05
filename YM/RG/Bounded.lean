import YM.RG.PathActions

/-! The action evaluators and density are bounded at each step (*not* uniformly over
periods with these statements). Guards uses of tsum and output integrals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG

open Wilson Lattice Set MeasureTheory Filter
open scoped Matrix.Norms.Frobenius Topology BigOperators

structure Envelope {V X : Type*} [MeasurableSpace V] [MeasurableSpace X] [Norm X] (F : V → X) : Prop where
  meas : Measurable F
  cost : ∃ C : ℝ, ∀ v, ‖F v‖ ≤ C

namespace Envelope
variable {V : Type*} [MeasurableSpace V] {f g : V → ℝ}

theorem const (c : ℝ) : Envelope fun _ : V => c := ⟨measurable_const, ‖c‖, fun _ ↦ le_rfl⟩

theorem add (hf : Envelope f) (hg : Envelope g) : Envelope fun x => f x + g x := by
  obtain ⟨C,H⟩ := hf.cost
  obtain ⟨D,Dh⟩ := hg.cost
  exact ⟨hf.meas.add hg.meas, C+D, fun x ↦ (norm_add_le ..).trans (add_le_add (H _) (Dh _))⟩

theorem neg (hf : Envelope f) : Envelope fun x => - f x := by
  obtain ⟨C,H⟩ := hf.cost
  exact ⟨hf.meas.neg, C, fun x ↦ by rw [norm_neg]; exact H _⟩

theorem mul (hf : Envelope f) (hg : Envelope g) : Envelope fun x => f x * g x := by
  obtain ⟨C,H⟩ := hf.cost
  obtain ⟨D,Dh⟩ := hg.cost
  exact ⟨hf.meas.mul hg.meas, C*D, fun x ↦ by
    rw [norm_mul]
    exact mul_le_mul (H _) (Dh x) (norm_nonneg _) ((norm_nonneg _).trans (H x))⟩

theorem sum {ι : Type*} (s : Finset ι) (F : ι → V → ℝ) (h : ∀ i, Envelope (F i)) :
    Envelope fun v => ∑ i ∈ s, F i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (V := V) 0)
  | insert i s hi ih => simp only [Finset.sum_insert hi]; exact (h i).add ih

theorem piece {p : V → Prop} [DecidablePred p] (hp : MeasurableSet {x | p x})
    (hf : Envelope f) (hg : Envelope g) : Envelope fun x => if p x then f x else g x := by
  obtain ⟨C,H⟩ := hf.cost
  obtain ⟨D,Dh⟩ := hg.cost
  refine ⟨hf.meas.ite hp hg.meas, max C D, fun v ↦ ?_⟩
  split
  · exact (H v).trans (le_max_left _ _)
  exact (Dh v).trans (le_max_right _ _)

theorem exp (hf : Envelope f) : Envelope fun x => Real.exp (f x) := by
  obtain ⟨C,H⟩ := hf.cost
  refine ⟨Real.continuous_exp.measurable.comp hf.meas, Real.exp C, fun x ↦ ?_⟩
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr ((le_abs_self (f x)).trans (H x))

theorem integrable (hf : Envelope f) (μ : Measure V) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨C,H⟩ := hf.cost
  exact Integrable.of_bound hf.meas.aestronglyMeasurable C (Eventually.of_forall H)
end Envelope

namespace PathData

variable {G : Gauge} {n : Side} {R : PathData G} {σ C Λ : ℝ} {c : Clip}

theorem clip_env (p : BudgetPoint) (x : Face (Per n)) : Envelope fun U : Config G n =>
    clipped c p.threshold (G.chord (faceValue U x)) := by
  have hd : Continuous fun U : Config G n => G.chord (faceValue U x) := by unfold faceValue; fun_prop
  have he : Envelope fun U : Config G n => G.chord (faceValue U x) :=
    ⟨hd.measurable, 2, fun _ ↦ (Real.norm_of_nonneg (G.chord_nonneg _)).trans_le (G.chord_le_two _)⟩
  unfold clipped
  simp only [sq, div_eq_mul_inv]
  refine Envelope.piece ((isClosed_le hd continuous_const).measurableSet) ?_ ?_
  · exact ((Envelope.const c.direct).mul (he.mul he)).mul (Envelope.const _)
  exact (Envelope.const _).mul he

theorem base_env (H : R.Bounds c σ C Λ) (p : BudgetPoint) (x : Face (Per n)) :
    Envelope fun U => R.baseTerm c p U x := by
  classical
  obtain ⟨C₀,HC⟩ := (R.ell_dominated H x).bound
  have hn : Envelope fun U => ‖R.ell U x‖ := by
    refine ⟨(R.ell_meas _ _ _ _ _ H).norm, C₀, fun U ↦ ?_⟩
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact HC _
  simp only [baseTerm, sq, div_eq_mul_inv]
  refine (clip_env p x).add (Envelope.piece ?_ ((hn.mul hn).mul (Envelope.const _))
    (Envelope.const _))
  exact (kept_closed ..).measurableSet

theorem atom_env (k : ℕ) (F : ℕ → Atom G k) (p : BudgetPoint) (x : Site n) (hσ : 0 < σ)
    (h : SumBudget (fun i ↦ (F i).budget σ) C) :
    Envelope fun U => atomSeries F p U x := by
  refine ⟨Measurable.tsum ?_, (atom_dominated F p x hσ h).bound⟩
  intro i
  exact (masked_measurable _ _ _ ((F i).unmasked_cont x).measurable)

theorem principal_env (H : R.Bounds c σ C Λ) (p : BudgetPoint) (β : ℝ) :
    Envelope (R.principal c p β (n := n)) := by
  have h₁ := Envelope.sum Finset.univ _ fun x : Face (Per n) => base_env H p x
  have h₂ := Envelope.sum Finset.univ _ fun x : Site n => (atom_env _ R.cubic p x H.width H.three).add
    (atom_env _ R.quartic p x H.width H.four)
  have h₃ := Envelope.sum Finset.univ _ fun x : Site n => atom_env _ R.loop p x H.width H.two
  exact ((Envelope.const β).mul (h₁.add h₂)).add h₃

theorem channels_env (H : R.Bounds c σ C Λ) (p : BudgetPoint) (β : ℝ) :
    Envelope (R.inChannels c p β (n := n)) := by
  unfold inChannels
  have hi := principal_env (n := n) H p β
  refine (Envelope.const _).mul (Envelope.sum _ _ fun s ↦ ?_)
  obtain ⟨C,H⟩ := hi.cost
  exact ⟨hi.meas.comp (continuous_pull ..).measurable, C, fun x ↦ H _⟩
end PathData
end YM.RG
