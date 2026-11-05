import YM.Push.SECTOR_MEASURE.Oriented
import YM.Push.SECTOR_MEASURE.Output
import YM.Work.F05.Actions

/-!
# A compatible representation (input to one step)

At the ACTUAL densities, cut out the one budget's short columns
(`wholeGap`,  etc.). Keep the rest including channel averages,
literal true `cuff` tails, loop, additive, gas and v. Then exact
push/price formula applies. No bound on those remainder costs except
integrability at this T. No assuming the existence of an input/output
representation pair linked by the step.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure.Presented

open Filter Function Lattice RG Wilson Pressure Pressure.Stores Tree MeasureTheory Oriented
open Next.Fluctuations.Sector
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Teller G} {T : Tube G S} {x W κ : ℝ}

/-- Replace `baseTerm` by true fine tail difference in `principal`.
All terms evaluate exactly as before, including masks. -/
def reduced (R : Rep G f) (n : ℕ) (U : Config G f) : ℝ :=
  R.beta * ((∑ i, cuff R.path R.clip R.p 1 n U i) + ∑ i : Site f,
    (PathData.atomSeries R.path.cubic R.p U i + PathData.atomSeries R.path.quartic R.p U i)) +
    ∑ i, PathData.atomSeries R.path.loop R.p U i

def exposed (R : Rep G f) (n : ℕ) (U : Config G f) :=
  Real.exp (R.v * Fintype.card (Site f) - (averaged fun s => reduced R n (pull s 0 U)) -
    R.activities.additive R.p U) * R.activities.gas R.p U

def cutR (R : Rep G f) (n : ℕ) (U : Config G f) :=
  averaged fun s => ∑ i, crown R.path R.clip n 1 R.p.threshold (pull s 0 U) i

theorem expel (R : Rep G f) (n : ℕ) (U : Config G f) :
    exposed R n U = Real.exp (R.beta * cutR R n U) * R.eval U := by
  let r := R.path
  have he : r.inChannels R.clip R.p R.beta U =
      averaged (fun s => reduced R n (pull s 0 U)) + R.beta * cutR R n U := by
    let q (s : Signed) := ∑ i, crown R.path R.clip n 1 R.p.threshold (pull s 0 U) i
    have hk (s : Signed) : r.principal R.clip R.p R.beta (pull s 0 U) =
        reduced R n (pull s 0 U) + R.beta * q s := by
      simp only [PathData.principal,q,reduced,cuff,Finset.sum_sub_distrib,mul_sub,mul_add,r]; abel
    have hx : r.inChannels R.clip R.p R.beta U = averaged fun s => reduced R n (pull s 0 U) + R.beta * q s := by
      simp only [PathData.inChannels,hk,averaged]
    rw [hx, av_add]
    unfold q cutR averaged; rw [← Finset.mul_sum]; ring
  unfold exposed Rep.eval Rep.exponent
  rw [← mul_assoc, ← Real.exp_add]
  dsimp only [r] at he
  rw [he]; ring_nf

structure Fits (T : Tube G S) (R : Rep G f) (x : ℝ) : Prop where
  path : R.path = T.up
  clip : R.clip = T.high
  temp : R.p.threshold = fiery G x S.patch.L

def sieve (T : Tube G S) (β x : ℝ) (V : Config G c) : ℝ := Real.exp (-β * (averaged fun s =>
  ∑ i, crown T.down T.low (till x) S.patch.L.val (temp x) (pull s 0 V) i))

lemma use_gap {R : Rep G f} (h : Fits T R x) (U : Config G f) (k : S.Choices) (V : Config G c) :
    taggedKernel S R.beta k U V * R.eval U = sieve T R.beta x V *
      (exposed R (till x) U * enters T R.beta x k V U) := by
  let F := cutR R (till x) U
  let C := averaged fun s => ∑ i, crown T.down T.low (till x) S.patch.L.val (temp x) (pull s 0 V) i
  rw [expel, enters]
  have hl : wholeGap T x U V = F-C := by
    unfold wholeGap crownGap F cutR C; rw [h.clip, h.path, h.temp]; exact av_sub ..
  rw [hl]
  change _ = Real.exp (-R.beta*C) * ((Real.exp (R.beta*F)*_) * (_*_))
  have he : Real.exp (-R.beta*C)*Real.exp (R.beta*F)*Real.exp (-R.beta*(F-C)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf; rw [Real.exp_zero]
  nth_rw 1 [← one_mul (taggedKernel ..), ← he]; ring

section producers
variable {R : Rep G f} {σ C Λ δ w : ℝ} (hR : R.Lawful σ C Λ δ w)

lemma env_exposed (R : Rep G f) (hR : R.Lawful σ C Λ δ w) (n : ℕ) : Envelope (exposed R n) := by
  have h : ∀ s : Signed, Envelope (fun U : Config G f => ∑ i, crown R.path R.clip n 1 R.p.threshold (pull s 0 U) i) := by
    intro s
    exact Envelope.sum _ _ fun i => Env.along (env_crown hR.paths ..) (continuous_pull s 0).measurable
  have hi : Envelope (cutR R n) := env_mean h
  rw [show exposed R n = fun U => _ from funext (expel R n)]
  exact (((Envelope.const _).mul hi).exp).mul (R.envelope hR)

lemma sieve_env (β x : ℝ) (hT : P.Funds S T) : Envelope (sieve T β x) := by
  obtain ⟨a,b,ha,hb⟩ := hT.feeds
  rw [← hT.low] at hb
  have h : ∀ s : Signed, Envelope (fun V : Config G c =>
      ∑ i, crown T.down T.low (till x) S.patch.L.val (temp x) (pull s 0 V) i) := by
    intro s
    exact Envelope.sum _ _ fun i => Env.along (env_crown hb ..) (continuous_pull s 0).measurable
  exact ((Envelope.const _).mul (env_mean h)).exp

open Work.F05

private lemma maskgi (Y : Support f) (g : Config G f → ℝ) (u : GaugeInvariant g) (x : ℝ) :
    GaugeInvariant (masked x Y g) := by
  intro t V
  unfold masked
  simp only [Set.indicator, Set.mem_setOf_eq, Healthy,gauge_flags,u t V]
  congr!

lemma lawful_gi {R : Rep G f} (hR : R.Lawful σ C Λ δ w) : GaugeInvariant R.eval := by
  have hm {k} (h : ℕ → Atom G k) (m : ∀ i, (h i).Invariant)
      (x : Site f) (t : Site f → G.El) (U : Config G f) :
      PathData.atomSeries h R.p (gauge t U) x = PathData.atomSeries h R.p U x := by
    apply tsum_congr
    intro i
    refine maskgi ((h i).footprint x) _ ?_ _ t U
    intro t U; unfold Atom.unmasked; simp_rw [slot_gauge]; exact m i ..
  let q := hR.paths
  have hp (U : Config G f) (s : Site f → G.El) (i : Cell f) :
      R.path.baseTerm R.clip R.p (gauge s U) i = R.path.baseTerm R.clip R.p U i := by
    simp only [PathData.baseTerm, PathData.kept, face_gauge,G.chord_conj,ell_gauge q, G.norm_adjoint]
    congr!
  intro t U
  have he : R.exponent (gauge t U)=R.exponent U := by
    have hh i := (hR.labels.regular.smooth i).symmetry
    have hs i : R.activities.regularOccurrence R.p i (gauge t U)=R.activities.regularOccurrence R.p i U :=
      maskgi _ _ (hh i) _ _ _
    simp only [Rep.exponent, PathData.inChannels, Activities.additive, hs, PathData.principal, pull_gauge_zero,
      hp, hm R.path.cubic (fun i => (q.invariant i).2.1), hm R.path.quartic (fun i => (q.invariant i).2.2),
      hm R.path.loop (fun i => (q.invariant i).1)]
  have hk i : R.activities.gasOccurrence R.p i (gauge t U) = R.activities.gasOccurrence R.p i U := by
    simp only [Activities.gasOccurrence, Activities.admissible,gauge_flags,hR.labels.forced.sym _ t U]
    congr!
  unfold Rep.eval; rw [he]; simp only [Activities.gas,hk]

end producers

/-- The rest of the integral RHS under charge (using absolute values
before any assumption on signs on an interval of represented inputs).
Volume dependent. No scalar divisions introduced here. -/
def leftOver (D : Allocation G S x W) (F : Forest S.ratio) (T : Tube G S)
    (R : Rep G f) (A : Stores S) (V : Config G c) : ℝ :=
  sieve T R.beta x V * D.column A F V (fun k a =>
    ‖exposed R (till x) (F.drape a)‖ * leaves A T R.beta x k V (F.drape a))

def cutEntry (D : Allocation G S x W) (F : Forest S.ratio) (T : Tube G S)
    (R : Rep G f) (A : Stores S) (V : Config G c) : ℝ :=
  sieve T R.beta x V * D.column A F V (fun k a =>
    exposed R (till x) (F.drape a) * enters T R.beta x k V (F.drape a))

/-- The precise fixed-volume statements bought by the receipts. -/
structure PortionCost (D : Allocation G S x W) (F : Forest S.ratio) (T : Tube G S) (κ : ℝ) (R : Rep G f) : Prop where
  envelopes A : Envelope (cutEntry D F T R A) ∧ Envelope (leftOver D F T R A)
  total V : S.push R.beta R.eval V = ∑ A, cutEntry D F T R A V
  each A V : output D F R.beta R.eval A V = cutEntry D F T R A V
  cost A V : ‖cutEntry D F T R A V‖ ≤ earn S G x κ R.beta A.shares * leftOver D F T R A V

theorem portionCost {σ C Λ δ w : ℝ} {R : Rep G f} (h : PointCharge T x W κ) (hT : P.Funds S T)
    (hR : R.Lawful σ C Λ δ w) (hl : 0 ≤ R.beta) (ht : Fits T R x) (F : Forest S.ratio)
    (D : Allocation G S x W) : PortionCost D F T κ R := by
  let hb := funds_branch hT
  let b := R.beta
  have he := R.envelope hR
  let E := exposed R (till x)
  have hE : Envelope E := env_exposed R hR _
  have hw (A : Stores S) (V : Config G c) : output D F R.beta R.eval A V = cutEntry D F T R A V := by
    unfold output cutEntry Allocation.column tagTotal
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with a
    unfold Allocation.portion through
    simp only [smul_eq_mul, use_gap ht]
    ring
  constructor
  · intro A; constructor
    · rw [show cutEntry D F T R A = output D F R.beta R.eval A from (funext (hw A)).symm]
      exact output_env D F b R.eval hb he A
    unfold leftOver
    let L := fun (k : S.Choices) (p : F.Slice G × Config G c) =>
      ‖E (F.drape p.1)‖ * leaves A T R.beta x k p.2 (F.drape p.1)
    apply (sieve_env b x hT).mul (D.column_env hb A F L ?_)
    have eh : Envelope (fun u => ‖E u‖) := by
      obtain ⟨C,H⟩ := hE.cost
      exact ⟨hE.meas.norm,C,fun a => (Real.norm_of_nonneg (norm_nonneg _)).trans_le (H a)⟩
    intro k
    have h1 : Measurable (fun a : F.Slice G × Config G c => F.drape a.1) :=
      F.continuous_drape.measurable.comp measurable_fst
    have h2 : Measurable (fun a : F.Slice G × Config G c => a.2) := measurable_snd
    exact (Env.along eh h1).mul (env_leaves hT A b x k h1 h2)
  · intro V; simp_rw [← hw]
    exact (push_columns D F b R.eval hb (he.integrable _) (lawful_gi hR) V).symm
  · exact hw
  intro A V
  let L := fun (_ : S.Choices) (a : F.Slice G) => ‖E (F.drape a)‖
  have hD := turn_charge D F b V L A hT h hl
    (fun k => ((Env.along hE F.continuous_drape.measurable).integrable _).norm) (fun _ _ => norm_nonneg _)
  have hh : 0 ≤ sieve T b x V := (Real.exp_pos _).le
  unfold cutEntry leftOver
  rw [norm_mul,Real.norm_of_nonneg hh,mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ hh
  apply le_trans ?_ hD
  unfold Allocation.column tagTotal
  apply (norm_sum_le ..).trans
  refine Finset.sum_le_sum fun k _ => ?_
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  unfold Allocation.portion
  have hy a : 0 ≤ enters T b x k V (F.drape a) := mul_nonneg (kernel_nonneg ..) (Real.exp_pos _).le
  change (∫ a, ‖_ * (E (F.drape a) * enters T b x k V (F.drape a))‖ ∂F.order G) = _
  simp only [L, norm_mul, Real.norm_of_nonneg (D.nonneg ..), Real.norm_of_nonneg (hy _), smul_eq_mul, E]

end YM.Push.SectorMeasure.Presented
