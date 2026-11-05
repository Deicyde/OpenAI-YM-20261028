import YM.Laurent.Rune
import YM.Push.SECTOR_MEASURE.Bounds
import YM.Push.SECTOR_MEASURE.Profile
import YM.Work.A15

/-!
# Exact finite-forest-slice sector sums

Vector/scalar/signed multipliers allowed. , cut column
`incoming`/`outgoing` of Sector . Keep the probability
Haar slice through all integrals. All set decompositions at fixed k:
outer finite counting sum uses those SAME tag arrays. Does not assign
multiplicity to overlapping Plots. Use integral identities as statements
about actual integrals with **complete** codomain (e.g. ℝ or ℂ). Some
algebraic library lemmas here, as in mathlib, are stated also in
incomplete spaces; then `∫` has mathlib's default-zero convention. And
use definitions of integral expressions only with Integrable proved.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure

open Filter Function Lattice RG Wilson Pressure Pressure.Stores Tree MeasureTheory
open Next.Fluctuations.Sector
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Teller G} {T : Tube G S} {x W : ℝ}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace Env
variable {α : Type*} [MeasurableSpace α] {H : α → ℝ} {f : α → X} {μ : Measure α}

lemma smul_L1 (h : Envelope H) (l : Integrable f μ) : Integrable (fun a => H a • f a) μ := by
  obtain ⟨C,A⟩ := h.cost
  exact l.bdd_smul C h.meas.aestronglyMeasurable (Eventually.of_forall A)

section borel
variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

lemma scale (h : Envelope H) (l : Envelope f) : Envelope (fun a => H a • f a) := by
  obtain ⟨C,A⟩ := h.cost; obtain ⟨D,B⟩ := l.cost
  refine ⟨h.meas.smul l.meas,C*D,fun a => ?_⟩
  rw [norm_smul]; exact mul_le_mul (A a) (B a) (norm_nonneg _) ((norm_nonneg _).trans (A a))

omit [NormedSpace ℝ X] in
lemma integrableX (h : Envelope f) (μ : Measure α) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨C,H⟩ := h.cost
  exact Integrable.of_bound h.meas.aestronglyMeasurable C (Eventually.of_forall H)

lemma marginal {β : Type*} [MeasurableSpace β] {g : α × β → X} (h : Envelope g)
    (μ : Measure α) [IsProbabilityMeasure μ] : Envelope fun b => ∫ a, g (a,b) ∂μ := by
  obtain ⟨C,H⟩ := h.cost
  refine ⟨h.meas.stronglyMeasurable.integral_prod_left'.measurable,C,fun b => ?_⟩
  apply (norm_integral_le_of_norm_le_const (Eventually.of_forall fun a => H (a,b))).trans
  simp

omit [NormedSpace ℝ X] in
lemma total {ι : Type*} (s : Finset ι) {g : ι → α → X} (h : ∀ i, Envelope (g i)) :
    Envelope (fun a => ∑ i ∈ s, g i a) := by
  choose C H using fun i => (h i).cost
  refine ⟨Finset.measurable_fun_sum _ fun i _ => (h i).meas, ∑ i ∈ s, C i, fun a => ?_⟩
  exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => H i a)
end borel
end Env

/-- Entries vanish where their particular physical likelihood vanishes. -/
def Ticketed (F : Forest S.ratio) (g : S.Choices → F.Slice G → X) :=
  ∀ k a, ¬ Alive S (F.drape a) k → g k a = 0

/-- Counts (and does not normalize again) all tag choices. -/
def tagTotal (F : Forest S.ratio) (g : S.Choices → F.Slice G → X) :=
  ∑ k, ∫ a, g k a ∂F.order G



namespace Allocation
variable (D : Allocation G S x W)

/-- Portion of a tagged integrand; tag argument unchanged. -/
def portion (A : Stores S) (F : Forest S.ratio) (V : Config G c) (g : S.Choices → F.Slice G → X) :
    S.Choices → F.Slice G → X :=
  fun k a => D.bill A k (F.drape a) V • g k a

/-- Column in the push problem, at fixed output field and seed records. -/
def column (A : Stores S) (F : Forest S.ratio) (V : Config G c) (g : S.Choices → F.Slice G → X) :=
  tagTotal F (D.portion A F V g)

lemma portion_integrable (h : S.patch.Branches S.kernel G) (A : Stores S) (F : Forest S.ratio)
    (V : Config G c) (g : S.Choices → F.Slice G → X) (k : S.Choices) (he : Integrable (g k) (F.order G)) :
    Integrable (D.portion A F V g k) (F.order G) :=
  Env.smul_L1 (D.envelope h F.continuous_drape.measurable measurable_const A k) he

/-- Exact full partition of the integral. Needs even the unused parts
integrable; _doesn't_ need strict positivity of each tag's likelihood. -/
theorem partitions (h : S.patch.Branches S.kernel G) (F : Forest S.ratio) (V : Config G c)
    (g : S.Choices → F.Slice G → X) (he : ∀ k, Integrable (g k) (F.order G)) :
    (∑ A, D.column A F V g) = tagTotal F g := by
  unfold column tagTotal
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← integral_finsetSum Finset.univ (fun A _ => D.portion_integrable h A F V g k (he k))]
  unfold portion; simp_rw [← Finset.sum_smul, D.sums, one_smul]

lemma plot_indicator (A : Stores S) (F : Forest S.ratio) (V : Config G c)
    (g : S.Choices → F.Slice G → X) (h : Ticketed F g) (k) :
    Set.indicator (onSector A F x W k V) (D.portion A F V g k) = D.portion A F V g k := by
  funext a
  by_cases he : a ∈ onSector A F x W k V
  · exact Set.indicator_of_mem he _
  rw [Set.indicator_of_notMem he _]
  unfold portion
  by_cases ht : Alive S (F.drape a) k
  · have ho : D.bill A k (F.drape a) V = 0 := not_not.mp (fun hn => he (D.plots hn ht))
    rw [ho, zero_smul]
  rw [h k a ht, smul_zero]

/-- Equivalence to the terms restricted to *their own* Plots, i.e.
what the per-Plot grants see. Still with the portion weights. -/
theorem plots_column (hm : S.patch.Branches S.kernel G) (A : Stores S) (F : Forest S.ratio) (V : Config G c)
    (g : S.Choices → F.Slice G → X) (he : Ticketed F g) (_l : ∀ k, Integrable (g k) (F.order G)) :
    (∑ k, ∫ a in onSector A F x W k V, D.portion A F V g k a ∂F.order G) = D.column A F V g := by
  unfold column tagTotal
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_indicator (show MeasurableSet (onSector A F x W i V) from plot_meas A i x W hm F.continuous_drape.measurable measurable_const),
    D.plot_indicator A F V g he i]





section variableOutput
variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

/-- Joint Borel and fixed-volume envelopes for the individual sector
terms with variable V. Useful also to commute the decompositions through
the coarse integral. -/
lemma portion_env (hm : S.patch.Branches S.kernel G) (A : Stores S) (F : Forest S.ratio)
    (g : S.Choices → F.Slice G × Config G c → X) (k : S.Choices) (he : Envelope (g k)) :
    Envelope (fun a : F.Slice G × Config G c => D.portion A F a.2 (fun k u => g k (u,a.2)) k a.1) := by
  have h : Measurable (fun a : F.Slice G × Config G c => F.drape a.1) :=
    F.continuous_drape.measurable.comp measurable_fst
  have l : Measurable (fun a : F.Slice G × Config G c => a.2) := measurable_snd
  exact Env.scale (D.envelope hm h l A k) he

lemma column_env (hm : S.patch.Branches S.kernel G) (A : Stores S) (F : Forest S.ratio)
    (g : S.Choices → F.Slice G × Config G c → X) (he : ∀ k, Envelope (g k)) :
    Envelope (fun V => D.column A F V (fun k u => g k (u,V))) := by
  have h k : Envelope fun V => ∫ a, D.portion A F V (fun i u => g i (u,V)) k a ∂F.order G :=
    Env.marginal (D.portion_env hm A F g k (he k)) _
  unfold column tagTotal
  exact Env.total (g:=fun k V => ∫ a, D.portion A F V (fun i u => g i (u,V)) k a ∂F.order G) _ h

end variableOutput
end Allocation

section dress

/-- Common dressing operations, one k taken throughout. -/
def inside (F : Forest S.ratio) (T : Tube G S) (β x : ℝ) (V : Config G c)
    (g : S.Choices → F.Slice G → X) : S.Choices → F.Slice G → X :=
  fun k a => incoming T β x k V (F.drape a) • g k a

def remainder (F : Forest S.ratio) (A : Stores S) (T : Tube G S) (β x : ℝ) (V : Config G c)
    (g : S.Choices → F.Slice G → X) : S.Choices → F.Slice G → X :=
  fun k a => outgoing A T β x k V (F.drape a) • g k a

def through (S : StepData c f) (F : Forest S.ratio) (β : ℝ) (V : Config G c)
    (g : S.Choices → F.Slice G → X) : S.Choices → F.Slice G → X :=
  fun k a => taggedKernel S β k (F.drape a) V • g k a

variable (F : Forest S.ratio) (β x : ℝ) (V : Config G c) (g : S.Choices → F.Slice G → X)

lemma inside_integrable (h : P.Funds S T) (k : S.Choices) (he : Integrable (g k) (F.order G)) :
    Integrable (inside F T β x V g k) (F.order G) :=
  Env.smul_L1 (env_incoming h β x k F.continuous_drape.measurable measurable_const) he

lemma remainder_integrable (h : P.Funds S T) (A : Stores S) (k : S.Choices)
    (he : Integrable (g k) (F.order G)) : Integrable (remainder F A T β x V g k) (F.order G) :=
  Env.smul_L1 (env_outgoing h β x k F.continuous_drape.measurable measurable_const A) he

lemma through_integrable (h : S.patch.Branches S.kernel G) (k : S.Choices)
    (he : Integrable (g k) (F.order G)) : Integrable (through S F β V g k) (F.order G) :=
  Env.smul_L1 (env_tagged β k h F.continuous_drape.measurable measurable_const) he

lemma ticket_in : Ticketed F (inside F T β x V g) := by
  intro k a h
  simp [inside,incoming,dead h]

lemma ticket_out (A : Stores S) : Ticketed F (remainder F A T β x V g) := by
  intro k a h
  simp [remainder,outgoing,dead h]



end dress
end YM.Push.SectorMeasure
