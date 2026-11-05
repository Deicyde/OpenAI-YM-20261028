import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Org.Theatre
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06

/-!
# Spending a grant in a cut-column integral

Within *one* oriented sector, on the true tree slice and the normalized
block kernel of the price question. Shows how to spend the price as an
inequality in an actual (finite-volume) integral; in particular no
change of estimate when integrating each tag's own Plot. Reads on fine
scale with slice Haar and counting sums on Choices. V is fixed (costs
pertain to the output-density problem; would still be relative to
probability Haar prior on V; one `penaltyZ` per output bond).

This consumer handles precisely the peeled factor: after bringing the
cut crown difference into the exponent with the kernel term. Permits
multipliers, including on shared tags, wherever the same currency
holds; NO claim of size, integrability or construction of any further
reweighting actually needed for vStep (one must get to this stage,
including putting any other factors such as long tails and normalization
coefficients into a multiplier separately). Doesn't multiply in a
second instance of the noise. We use `Plot` as the tested region;
any actual sector profiles constraining further can go in a multiplier.
No replacing a sector by an expectation in the final continuum theory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations.Sector
open Filter Function Lattice RG RG.Supply Wilson Pressure Pressure.Tube Pressure.Stores Precision Input Tree MeasureTheory
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators ENNReal Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

def crownGap (T : Tube G S) (x : ℝ) (U : Config G f) (V : Config G c) : ℝ :=
  (∑ i, crown T.up T.high (till x) 1 (fiery G x S.patch.L) U i) -
    (∑ i, crown T.down T.low (till x) S.patch.L.val (temp x) V i)

def unassigned (A : Stores S) (T : Tube G S) (x : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) : ℝ :=
  let Q := S.prediction U k
  let s := temp x; let t := fiery G x S.patch.L; let R := till x
  ((∑ i, T.workF R U V t s i)+(∑ i,T.workI R Q V s i)+(∑ i,T.workC R V s i)+
    (∑ i,T.workN R V s i)+(∑ i,T.workL R U Q V s i)+(∑ i,T.workD R V s i)) - A.assessed T x U Q V

/-- Multiply the kernel term (still has **its** Haar normalization) by the
relative cut crown exponential. -/
def incoming (T : Tube G S) (β x : ℝ) (k : S.Choices) (V : Config G c) (U : Config G f) :=
  S.likelihood U k * S.noise β (S.prediction U k) V * Real.exp (-β*crownGap T x U V)

/-- Remainder term (common Haar-noise prefactor kept separately). -/
def outgoing (A : Stores S) (T : Tube G S) (β x : ℝ) (k : S.Choices) (V : Config G c) (U : Config G f) :=
  S.likelihood U k * Real.exp (-β*unassigned A T x U k V)

def prefactor (S : StepData c f) (G : Gauge) (β : ℝ) :=
  (S.penaltyZ β G)⁻¹ ^ Fintype.card (Bond c)

def onSector (A : Stores S) (F : Forest S.ratio) (x W : ℝ) (k : S.Choices) (V : Config G c) : Set (F.Slice G) :=
  {a | Plot A (F.drape a) k V x W}

lemma prefactor_pos (β : ℝ) : 0 < prefactor S G β := pow_pos (inv_pos.mpr (S.penaltyZ_pos β)) _

lemma peel_eq (A : Stores S) (T : Tube G S) (β x : ℝ) (k : S.Choices) (U : Config G f) (V : Config G c) :
    incoming T β x k V U = prefactor S G β * Real.exp (-β*A.assessed T x U (S.prediction U k) V) *
      outgoing A T β x k V U := by
  let Q := S.prediction U k
  let m := ∑ i, monetary S Q V i
  have he : S.noise β Q V = prefactor S G β * Real.exp (-β*m) := by
    unfold StepData.noise m prefactor
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,Finset.mul_sum,Real.exp_sum]; congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold StepData.penaltyWeight monetary wire; rw [G.chord_price]; ring_nf
  have hv : m+crownGap T x U V = A.assessed T x U Q V + unassigned A T x U k V := by
    dsimp only [m,crownGap,unassigned,Q]
    rw [T.locates]; abel
  unfold incoming outgoing; rw [he]
  calc
    _ = prefactor S G β*S.likelihood U k * Real.exp (-β * (m+crownGap T x U V)) := by rw [mul_add,Real.exp_add]; ring
    _ = _ := by rw [hv,mul_add,Real.exp_add]; ring

section measures
-- Measurability and boundedness at given T, **no across-volume** assertion
-- for these envelopes.
variable {P : Teller G} {T : Tube G S}
private lemma env_cont {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [CompactSpace α] {f : α → ℝ} (h : Continuous f) : Envelope f := by
  obtain ⟨C,H⟩ := (isCompact_range h.norm).bddAbove
  exact ⟨h.measurable,C,fun x => H ⟨x,rfl⟩⟩

private lemma env_pull {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {g : α → γ} (hg : Measurable g) {f : γ → ℝ} (hf : Envelope f) : Envelope (fun x => f (g x)) := by
  obtain ⟨C,hC⟩ := hf.cost
  exact ⟨hf.meas.comp hg,C,fun x => hC _⟩

private lemma env_sub {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (h : Envelope f) (k : Envelope g) :
    Envelope fun x => f x - g x := by
  simp only [sub_eq_add_neg]; exact h.add k.neg

private lemma sector_meas {A : Stores S} {F : Forest S.ratio} {x W : ℝ} {k : S.Choices} {V : Config G c}
    (hb : S.patch.Branches S.kernel G) : MeasurableSet (onSector A F x W k V) := by
  let X := A.dome (5*radiusB x)
  let t := fiery G x S.patch.L
  have he i : Measurable (fun u : F.Slice G => toll (F.drape u) i) :=
    (show Continuous _ by unfold toll faceValue; fun_prop).measurable
  have hf i : Measurable (fun u : F.Slice G => wire (S.prediction (F.drape u) k) V i) :=
    ((show Continuous (fun Y => wire Y V i) by unfold wire; fun_prop).measurable.comp
      ((S.prediction_meas hb k).comp F.continuous_drape.measurable))
  have hg i : Measurable (fun u : F.Slice G => S.patch.frameMass S.kernel
        (expandAt (S.ratio.embed i) (F.drape u)) (k.1 i)) := (S.patch.frameMass_meas _).comp
    (show Continuous (fun u : F.Slice G => expandAt (S.ratio.embed i) (F.drape u)) by
      unfold expandAt; fun_prop).measurable
  let M p (u : F.Slice G) := ¬ Disjoint X (startPos S p) →
    ((p∈A.costs → t/4 ≤ toll (F.drape u) p) ∧ (p∉A.costs → toll (F.drape u) p ≤ t/2))
  let N b (u : F.Slice G) := ¬ Disjoint X (pinPos b) →
    ((b∈A.aisles → W*t ≤ wire (S.prediction (F.drape u) k) V b) ∧
      (b∉A.aisles → wire (S.prediction (F.drape u) k) V b ≤ 2*W*t))
  let H : Prop := ∀ i, i ∈ X → (i ∈ A.flags ↔ i ∈ RG.flags (temp x) V)
  let E i (u : F.Slice G) := i∈X → 0 < S.patch.frameMass S.kernel (expandAt (S.ratio.embed i)
    (F.drape u)) (k.1 i)
  have hs : onSector A F x W k V = {u | (∀ i, M i u) ∧ (∀ i,N i u) ∧ H ∧ (∀ i, E i u)} := by
    ext u; exact ⟨fun h => ⟨h.consumes,h.drive,h.precise,h.list⟩,
      fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩⟩
  have hi (B : Prop) : MeasurableSet {u : F.Slice G | B} := by by_cases h : B <;> simp [h]
  rw [hs,Set.setOf_and,Set.setOf_and,Set.setOf_and]
  simp only [Set.setOf_forall]
  refine (MeasurableSet.iInter fun i => ?_).inter ((MeasurableSet.iInter fun i => ?_).inter
    ((hi H).inter (MeasurableSet.iInter fun i => ?_)))
  · by_cases h : Disjoint X (startPos S i)
    · simp [M,h]
    by_cases ht : i∈A.costs
    · simp only [M,h,not_false_eq_true,ht, not_true_eq_false,false_implies,and_true,true_implies]
      exact measurableSet_le measurable_const (he i)
    simp only [M,h,not_false_eq_true,ht,false_implies,true_and,true_implies]; exact measurableSet_le (he i) measurable_const
  · by_cases h : Disjoint X (pinPos i)
    · simp [N,h]
    by_cases ht : i∈A.aisles
    · simp only [N,h,not_false_eq_true,ht,not_true_eq_false,false_implies,and_true,true_implies]
      exact measurableSet_le measurable_const (hf i)
    simp only [N,h,not_false_eq_true,ht,false_implies,true_and,true_implies]; exact measurableSet_le (hf i) measurable_const
  · by_cases h : i∈X
    · simp only [E,h,true_implies]; exact measurableSet_lt measurable_const (hg i)
    simp [E,h]

private lemma env_crown (hT : P.Funds S T) (R : ℕ) : ∀ (s : ℝ) (i : Cell f),
    Envelope (fun U => crown T.up T.high R 1 s U i) ∧
      (∀ j : Bool, Continuous (fun U => T.Xf R U (i,j))) := by
  intro s i
  obtain ⟨a,b,ha,hb⟩ := hT.feeds
  obtain ⟨C,hs,he⟩ := T.up.ell_dominated ha i
  have hd : Continuous fun U : Config G f => shorten T.up R 1 U i := by
    unfold shorten
    refine continuous_tsum ?_ hs ?_
    · intro j
      unfold shortenTerm PathData.ellTerms Slot.atSite expandAt; split <;> fun_prop
    intro j u; unfold shortenTerm; split
    next h => exact he j u
    next h => rw [norm_zero]; exact (norm_nonneg _).trans (he j u)
  constructor
  · have hx := show Continuous (fun U : Config G f => G.chord (faceValue U i)) by unfold faceValue; fun_prop
    unfold crown trunk PathData.clipped
    refine Envelope.add (Envelope.piece (PathData.kept_closed ..).measurableSet
      (env_cont ?_) (Envelope.const _)) (Envelope.piece
      ((isClosed_le hx continuous_const).measurableSet) (env_cont ?_) (env_cont ?_)) <;> fun_prop
  intro j
  unfold Tube.Xf plotted; split
  next h => exact hd
  next h => unfold shoot faceValue; fun_prop

private lemma terms_pay (A : Stores S) (hT : P.Funds S T) (β x : ℝ) (k : S.Choices) (V : Config G c) :
    Envelope (incoming T β x k V) ∧ Envelope (outgoing A T β x k V) := by
  have hb : S.patch.Branches S.kernel G := hT.knobs.symm ▸ hT.kernel
  let t := fiery G x S.patch.L; let s := temp x; let R := till x
  let Q := fun U : Config G f => S.prediction U k
  have he : Measurable Q := S.prediction_meas hb k
  have h1 (i : Cell f) := env_crown hT R t i
  have hf (i : Cell f) : Envelope (fun U => T.workF R U V t s i) := by
    unfold Tube.workF
    apply Envelope.add (h1 i).1
    refine Envelope.sum _ (fun j U => ‖T.Mv R s V (i,j)‖^2/2 - inner ℝ (T.Mv R s V (i,j)) (T.Xf R U (i,j))) ?_
    intro j
    have ht := (h1 i).2 j
    apply env_cont; fun_prop
  have hp (i : Bond c) : Envelope fun U => T.workI R (Q U) V s i := env_pull he (f:=fun Y => T.workI R Y V s i)
    (env_cont (by unfold Tube.workI monetary wire Z; fun_prop))
  have hL (i : Cell c) : Envelope fun U => T.workL R U (Q U) V s i := by
    apply env_pull (g:=fun U => (U,Q U)) (measurable_id.prodMk he)
      (f:=fun y => T.workL R y.1 y.2 V s i) (env_cont _)
    unfold Tube.workL unzip Z
    have ht (j : Twin f) := (h1 j.1).2 j.2
    fun_prop
  have ha : Envelope fun U => A.assessed T x U (Q U) V := by
    unfold assessed tally talli talll
    refine ((((Envelope.sum _ _ hf).add (Envelope.sum _ _ hp)).add (Envelope.const _)).add (Envelope.const _)).add ?_
    exact Envelope.sum _ (fun i U => T.workL R U (Q U) V s i + T.workD R V s i)
      (fun i => (hL i).add (Envelope.const _))
  have hB : Envelope fun U => unassigned A T x U k V := by
    unfold unassigned
    apply env_sub _ ha
    exact ((((((Envelope.sum _ _ hf).add (Envelope.sum _ _ hp)).add (Envelope.const _)).add (Envelope.const _)).add
      (Envelope.sum _ _ hL)).add (Envelope.const _))
  have hX : Envelope fun U => crownGap T x U V := by
    unfold crownGap
    exact env_sub (Envelope.sum _ _ fun i => (h1 i).1) (Envelope.const _)
  have hu : Envelope (fun U : Config G f => S.likelihood U k) := by
    refine ⟨S.likelihood_meas hb k,1,fun U => ?_⟩
    rw [Real.norm_of_nonneg (S.likelihood_pos U k), ← S.chosen hb U]
    exact Finset.single_le_sum (fun i _ => S.likelihood_pos U i) (Finset.mem_univ k)
  have hz : Envelope fun U => S.noise β (Q U) V := env_pull he (env_cont
    ((S.noise_cont β).comp (continuous_id.prodMk continuous_const)))
  exact ⟨(hu.mul hz).mul ((Envelope.const (-β)).mul hX).exp,hu.mul ((Envelope.const (-β)).mul hB).exp⟩
end measures

lemma peel {P : Teller G} {T : Tube G S} (hT : P.Funds S T) (A : Stores S) (F : Forest S.ratio) (x W κ : ℝ)
    (β : ℝ) (hp : 0≤β) (V : Config G c)
    (h : ∀ (a : F.Slice G) k, a∈onSector A F x W k V →
      κ*(fiery G x S.patch.L)^2*A.shares ≤ A.assessed T x (F.drape a) (S.prediction (F.drape a) k) V)
    (g : S.Choices → F.Slice G → ℝ) (hg : ∀ k, Integrable (g k) (F.order G)) (hz : ∀ k a, 0≤g k a) :
    let I := fun k a => g k a * incoming T β x k V (F.drape a)
    let O := fun k a => g k a * outgoing A T β x k V (F.drape a)
    let X k := onSector A F x W k V
    (∀ k, MeasurableSet (X k) ∧ Integrable (I k) (F.order G) ∧ Integrable (O k) (F.order G)) ∧
      (∑ k, ∫ a in X k, I k a ∂F.order G) ≤ prefactor S G β *
        Real.exp (-β*(κ*(fiery G x S.patch.L)^2*A.shares)) * ∑ k, ∫ a in X k, O k a ∂F.order G := by
  intro I O X
  have he (k) (f : Config G f → ℝ) (hf : Envelope f) : Integrable
      (fun a => g k a * f (F.drape a)) (F.order G) := by
    obtain ⟨C,H⟩ := hf.cost
    exact (hg k).mul_bdd (hf.meas.comp F.continuous_drape.measurable).aestronglyMeasurable (Eventually.of_forall fun _ => H _)
  have hm k := terms_pay A hT β x k V
  have hb k : MeasurableSet (X k) ∧ Integrable (I k) (F.order G) ∧ Integrable (O k) (F.order G) :=
    ⟨sector_meas (hT.knobs.symm ▸ hT.kernel),he k _ (hm k).1,he k _ (hm k).2⟩
  refine ⟨hb,?_⟩
  rw [Finset.mul_sum]; apply Finset.sum_le_sum
  intro k _
  rw [← integral_const_mul]
  refine setIntegral_mono_on (hb k).2.1.integrableOn ((hb k).2.2.const_mul _).integrableOn (hb k).1 fun a ha => ?_
  have hz' : 0≤outgoing A T β x k V (F.drape a) := mul_nonneg (S.likelihood_pos _ _) (Real.exp_pos _).le
  unfold I O; rw [peel_eq]
  calc
    _ = prefactor S G β * Real.exp (-β*(A.assessed T x (F.drape a) (S.prediction (F.drape a) k) V)) *
        (g k a * outgoing A T β x k V (F.drape a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_monotone
      (mul_le_mul_of_nonpos_left (h a k ha) (by linarith))) (prefactor_pos β).le) (mul_nonneg (hz k a) hz')


end YM.Next.Fluctuations.Sector
