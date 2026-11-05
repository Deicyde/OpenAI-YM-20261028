import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Change

set_option warningAsError false

/-!
# Exact multiplier for marked sector change, pointwise

Work on the *intact* sectors,
`Allocation` (not summing unweighted overlapping Plots). Counting convention
for k. Insertions may modify gas entries *inside* the summands, so their
physical densities need not be supplied as a vacuum times a probe. Instead undo
only the short part of the fine action (`recut`, as in `Presented.expel`). No
division by R.eval or by any of its terms. All marks will be evaluated on the
same slice and the same physical group elements built from Y and z. This is
before any isolation of first-system components or moving masks to V. As in
`Change`, we work relative to the **cut** output base `sieve`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Marked
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open Gaussian Rows YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid
open YM.Push.SectorMeasure YM.Next.Fluctuations.Sector
open YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {x w : ℝ}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def recut (R : Rep G f) (n : ℕ) (u : Config G f → X) (U : Config G f) : X :=
  Real.exp (R.beta * cutR R n U) • u U



theorem recut_envelope [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {σ n Λ δ l : ℝ} {R : Rep G f} (h : R.Lawful σ n Λ δ l)
    (r : ℕ) {u : Config G f → X} (he : Envelope u) : Envelope (recut R r u) := by
  have hw : ∀ s : Signed, Envelope (fun U : Config G f =>
      ∑ i, crown R.path R.clip r 1 R.p.threshold (pull s 0 U) i) := by
    intro s
    exact Envelope.sum _ _ fun i => Env.along (env_crown h.paths ..) (continuous_pull s 0).measurable
  exact Env.scale (((Envelope.const R.beta).mul (show Envelope (cutR R r) from env_mean hw)).exp) he

lemma uncover {R : Rep G f} {T : Tube G S} (h : Fits T R x)
    (u : Config G f → X) (V : Config G c) (k : S.Choices) (U : Config G f) :
    taggedKernel S R.beta k U V • u U = sieve T R.beta x V •
      (enters T R.beta x k V U • recut R (till x) u U) := by
  let F := cutR R (till x) U
  let C := averaged fun s => ∑ i, crown T.down T.low (till x) S.patch.L.val (temp x) (pull s 0 V) i
  have hl : wholeGap T x U V = F-C := by
    unfold wholeGap crownGap F cutR C
    rw [h.clip, h.path, h.temp]
    exact av_sub ..
  rw [enters, hl]; unfold recut
  change _ = Real.exp (-R.beta * C) • ((taggedKernel S R.beta k U V * _) • (Real.exp (R.beta * F) • u U))
  simp only [smul_smul]
  congr 1
  have he : Real.exp (-R.beta * C) * Real.exp (-R.beta * (F-C)) * Real.exp (R.beta * F) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf; rw [Real.exp_zero]
  nth_rw 1 [← one_mul (taggedKernel ..), ← he]; ring

variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (A : Stores S) (R : Rep G f)

def dress (u : Config G f → X) (U : Config G f) :=
  (prefactor S G R.beta * Real.exp (-R.beta * fee T x V k A U)) • recut R (till x) u U

lemma dress_envelope [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {σ n Λ δ l : ℝ} {P : Teller G} (h : R.Lawful σ n Λ δ l) (hT : P.Funds S T)
    {u : Config G f → X} (he : Envelope u) : Envelope (dress T x V k A R u) :=
  Env.scale ((Envelope.const _).mul (((Envelope.const _).mul (fee_envelope T x V k A hT)).exp))
    (recut_envelope h _ he)

lemma dress_eq (h : S.patch.Branches S.kernel G) (u : Config G f → X) (U : Config G f) :
    S.likelihood U k • dress T x V k A R u U = enters T R.beta x k V U • recut R (till x) u U := by
  rw [enters_eq h A, leaves, dress, fee, mul_add, Real.exp_add, smul_smul]
  ac_rfl

variable (W : Stencils S) (F : Forest S.ratio) (D : Allocation G S x w) (q : Chi) (J : ChartRatio G) (d : ℝ)
  (C : Gaussian.Table (Rows.In x A F (G:=G))) (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))

/-- Unchanged, nonnegative part of the multiplier in `dyed`. Does not
include the `exposed` input. In particular the likelihood and its
fallback branches still evaluated on this one U (other terms like affine
corrections with their V/Y conventions unchanged too). -/
def backdrop (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F)) : ℝ :=
  let g := coupling R.beta; let a := m Y + g • z; let y := tape a
  let U := physical A F V Y y
  reserve q J d y * doors q d y * D.bill A k U V * S.likelihood U k *
    Real.exp (-R.beta * averaged (Rows.residual T x V k W A F q d Y U a) +
        adjustment T x V k W A F q d Y C (m Y) g z)

lemma backdrop_nonneg (Y z) : 0 ≤ backdrop T x V k A R W F D q J d C m Y z := by
  have hh {y : LogArray G (Active A x F)} : 0 ≤ doors q d y :=
    Finset.prod_nonneg fun i _ => (broad_range q (y i) _).1
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (reserve_pos ..).le hh) (D.nonneg ..))
    (S.likelihood_pos ..)) (Real.exp_pos _).le

/-- The marked extension of `dyed`, determinant/J.scale/prefactor/sieve
still outside. u is a *density*, not a log coefficient. -/
def ink (u : Config G f → X) (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F)) : X :=
  backdrop T x V k A R W F D q J d C m Y z •
    recut R (till x) u (physical A F V Y (displaced (m Y) (coupling R.beta) z))





lemma ink_norm (u : Config G f → X) (Y z) :
    ink T x V k A R W F D q J d C m (fun U => ‖u U‖) Y z = ‖ink T x V k A R W F D q J d C m u Y z‖ := by
  unfold ink recut
  simp only [smul_eq_mul, norm_smul, Real.norm_of_nonneg (backdrop_nonneg ..),
    Real.norm_of_nonneg (Real.exp_pos _).le]

lemma ink_regularized {o σ Λ E} (h : T.up.Bounds o σ E Λ) (hh : 0<R.beta)
    (u : Config G f → X) (Y z) :
    prefactor S G R.beta • ink T x V k A R W F D q J d C m u Y z = Real.exp (force C z/2) •
      regularized D A F V k q J d (dress T x V k A R u) Y (displaced (m Y) (coupling R.beta) z) := by
  let g := coupling R.beta
  let a := m Y + g • z
  let y := tape a
  let U := physical A F V Y y
  let e := guide T x V k W A F q d Y a
  have he : fee T x V k A U = averaged (Rows.residual T x V k W A F q d Y U a) + e := by
    rw [exact_fee, compose_residual _ _ _ _ _ _ _ _ _ _ h]
  have ht := adjusted T x V k W A F q d Y C (m Y) z (coupling_pos hh)
  change adjustment T x V k W A F q d Y C (m Y) g z = force C z / 2 - e/g^2 at ht
  have hb : e/g^2 = R.beta*e := by rw [div_eq_mul_inv, by_coupling hh]; ring
  change prefactor S G R.beta • ((reserve q J d y*doors q d y*D.bill A k U V*S.likelihood U k *
      Real.exp (-R.beta * averaged (Rows.residual T x V k W A F q d Y U a) + _)) • recut R (till x) u U) =
    Real.exp _ • ((reserve q J d y*doors q d y) • ((D.bill A k U V*S.likelihood U k) • dress T x V k A R u U))
  rw [ht,hb, show -R.beta * averaged (Rows.residual T x V k W A F q d Y U a) + (force C z/2-R.beta*e) =
    force C z/2-R.beta*fee T x V k A U by rw [he]; ring, sub_eq_add_neg, Real.exp_add, ← neg_mul, dress]
  simp only [smul_smul]; ac_rfl
end YM.Next.SectorChange.Marked
