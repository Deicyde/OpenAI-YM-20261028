import YM.Push.SECTOR_MEASURE.Presented

/-!
# Through intact incoming K occurrences

This part *before* enlarging overlaps or moving
indicators. One finite torus but the K lists may already be infinite;
use summability on this torus. Per tag and V (thus also usable under
all the finite sum operations), integrating profiles with the actual
K labels still kept. No claims of post-expansion summability nor of
rewriting into components yet. Use evaluation identities involving
`tsum` together with summability (Lawful here), not `tsum`
on non-summables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure.LabelSum

open Filter Function MeasureTheory Wilson Pressure Pressure.Stores RG Lattice Tree Oriented Presented
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Teller G} {T : Tube G S} {x W : ℝ}





-- General integration mechanism
private lemma local_integral_sum {ι α : Type*} [Countable ι] [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {g : ι → α → ℝ} (h : Dominated g) (l : ∀ i, Measurable (g i)) :
    (∀ i, Integrable (g i) μ) ∧ Integrable (fun a => ∑' i, g i a) μ ∧
    Summable (fun i => ∫ a, ‖g i a‖ ∂μ) ∧ HasSum (fun i => ∫ a, g i a ∂μ) (∫ a, ∑' i, g i a ∂μ) := by
  have hx : Envelope (fun a => ∑' i, g i a) := ⟨Measurable.tsum l,h.bound⟩
  obtain ⟨C,H,hC⟩ := h
  have he (i : ι) : Envelope (g i) := ⟨l i, C i, hC i⟩
  have hi (i : ι) : Integrable (g i) μ := (he i).integrable μ
  have hn (i : ι) : 0 ≤ ∫ a, ‖g i a‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have hl : Summable (fun i => ∫ a, ‖g i a‖ ∂μ) := by
    refine H.of_nonneg_of_le hn fun i => ?_
    calc
      _ ≤ ∫ _, C i ∂μ := integral_mono (hi i).norm (integrable_const _) (fun a => hC i a)
      _ = _ := by simp
  exact ⟨hi,hx.integrable _,hl,hasSum_integral_of_summable_integral_norm hi hl⟩

/-- At pre-Gaussian exponent, per set of K occurrences; still
relative to the cut crown, including the exact `reduced` leftover. -/
def separate (R : Rep G f) (n : ℕ) (b : Finset ℕ) (U : Config G f) :=
  (Real.exp (R.beta * cutR R n U) * Real.exp (R.exponent U)) * R.activities.gasOccurrence R.p b U

theorem separate_sum (R : Rep G f) (n : ℕ) (U : Config G f) : ∑' b, separate R n b U = exposed R n U := by
  unfold separate
  rw [tsum_mul_left, expel]; unfold Rep.eval Activities.gas; ring

variable {σ C Λ δ w : ℝ} {R : Rep G f}

/-- Term under the sector integral; allows using either the charged
column factors or other legitimate Envelopes as weights. -/
def atomTerm (D : Allocation G S x W) (A : Stores S) (F : Forest S.ratio) (R : Rep G f)
    (V : Config G c) (k : S.Choices) (e : F.Slice G → ℝ) (b : Finset ℕ) (a : F.Slice G) :=
  D.bill A k (F.drape a) V * (separate R (till x) b (F.drape a) * e a)

lemma atom_series (hR : R.Lawful σ C Λ δ w) (hm : S.patch.Branches S.kernel G) (D : Allocation G S x W)
    (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices) (e : F.Slice G → ℝ)
    (he : Envelope e) :
    let L := atomTerm D A F R V k e
    (∀ i, Integrable (L i) (F.order G)) ∧ Integrable
      (fun a => D.bill A k (F.drape a) V * (exposed R (till x) (F.drape a) * e a)) (F.order G) ∧
    Summable (fun i => ∫ a, ‖L i a‖ ∂F.order G) ∧ HasSum (fun i => ∫ a, L i a ∂F.order G)
      (∫ a, D.bill A k (F.drape a) V * (exposed R (till x) (F.drape a) * e a) ∂F.order G) := by
  intro L
  let q U := Real.exp (R.beta * cutR R (till x) U) * Real.exp (R.exponent U)
  have qenv : Envelope q := by
    have h : ∀ s : Signed, Envelope (fun U : Config G f => ∑ i,
      crown R.path R.clip (till x) 1 R.p.threshold (pull s 0 U) i) := by
      intro s
      exact Envelope.sum _ _ fun _ => Env.along (env_crown hR.paths ..) (continuous_pull s 0).measurable
    have hi : Envelope (cutR R (till x)) := env_mean h
    exact (((Envelope.const _).mul hi).exp).mul (R.exponentEnv hR).exp
  let H a := (D.bill A k (F.drape a) V * q (F.drape a)) * e a
  have hd : Envelope H :=
    ((D.envelope hm F.continuous_drape.measurable (V:=fun _ => V) measurable_const A k).mul
      (Env.along qenv F.continuous_drape.measurable)).mul he
  have hh : L = fun i a => H a * R.activities.gasOccurrence R.p i (F.drape a) := by
    funext i a; unfold L atomTerm H separate q; ring
  have hg i : Measurable (L i) := by
    rw [hh]
    have hv : Measurable (R.activities.gasOccurrence R.p i) :=
      Measurable.ite (R.activities.admissible_borel R.p i)
        (Finset.measurable_fun_prod _ fun i _ => hR.labels.forced.meas i) measurable_const
    exact hd.meas.mul (hv.comp F.continuous_drape.measurable)
  have hL : Dominated L := by
    rw [hh]; obtain ⟨C,hC⟩ := hd.cost
    obtain ⟨b,hb,h⟩ := Activities.gasSeries hR.labels
    refine ⟨_, hb.mul_left C, fun i a => ?_⟩
    rw [norm_mul]; exact mul_le_mul (hC a) (h i (F.drape a)) (norm_nonneg _) ((norm_nonneg _).trans (hC a))
  have hl := local_integral_sum (F.order G) hL hg
  have hx a : ∑' i, L i a = D.bill A k (F.drape a) V * (exposed R (till x) (F.drape a) * e a) := by
    unfold L atomTerm; rw [tsum_mul_left,tsum_mul_right,separate_sum]
  simp_rw [hx] at hl
  exact hl



end YM.Push.SectorMeasure.LabelSum
