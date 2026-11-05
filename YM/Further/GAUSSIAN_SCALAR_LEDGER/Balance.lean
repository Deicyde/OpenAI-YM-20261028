import YM.Further.GAUSSIAN_SCALAR_LEDGER.Affine
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Correction
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Opening

set_option warningAsError false

/-!
# Surface on the true columns

From the exact Haar opening and a named Gram/covariance system. Here
Gram rows, affine constants, choice of any centering (window caller
may supply $-Π₀^* b$) and output base value to extract are *parameters*,
not identifying any truncation with the full Hessian. All arbitrary
because we actually ADD AND SUBTRACT the rows with the given numerical
data before doing any integration. Proves value identities; pricing
those very same rows uniformly, or cancelling them in interactions,
requires more. `Rates` an input about real matrices (see Local for
producing in some settings), not beta running bounds. B0 denotes the
caller's flat comparator table to EXTRACT. In E application supply the
real truncated comparator in the actual channels (`no_hole` etc useful
if then averaging forests). Not charging it from an untruncated Hessian.
All lengths/dimensions native here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Function MeasureTheory Filter Set Matrix
open Lattice RG Wilson Tree Precision SectorNext.Vacuum Pressure Push.SectorMeasure
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {c f : Side} {S : StepData c f} {G : Gauge} {x W : ℝ} {O : ChartRatio G}
  {F : Forest S.ratio}

/-- Per physical, **whole** tag record. No iid mixture over rows.
Rooms (real finite labels) can just use zero rows when reserving space
but need to retain all channel weights within rows and b0 to use those
very D rows as in the source. Compare/sample within each Y before outer
integration. -/
structure Fiber (F : Forest S.ratio) (O : ChartRatio G) (rooms : Type*) where
  H : Finset F.Free
  veil : Curtain O H
  D : Frozen H G → Matrix rooms (Bits G H) ℝ
  b0 : Frozen H G → VV rooms
  C : Frozen H G → Wall (Bits G H)
  μ : Frozen H G → VV (Bits G H)

variable {rooms : Type*} [Fintype rooms]
namespace Fiber

variable (d : Allocation G S x W) (P : Stores S) (k : S.Choices) (V : Config G c)
    (R : Rep G f) (u : Fiber F O rooms) (U : ℝ)

def sigma (Y : Frozen u.H G) : Wall (Key F G) := filled u.H (precision (u.D Y))
def complete (Y : Frozen u.H G) : Wall (Key F G) := filled u.H (u.C Y)
def eps (Y : Frozen u.H G) := u.sigma Y * u.complete Y - 1

/-- Full numeric receipts. Require absolute row rate on S, *not* symmetry
of S. Can equivalently check it on regular-only (`rates_filled`). See
`Local` for production of these costs from the principal-window rules. -/
structure Rates (η L q : ℝ) : Prop where
  pos : 0 < η
  mind : η ≤ L
  low : 0 ≤ q
  high : q < 1
  gap Y : Numeric (u.sigma Y) η L
  rate Y : Round.rowRate q (u.eps Y)
  symm Y : (u.C Y).IsHermitian

variable {η L q : ℝ}

lemma real_precision (Y : Frozen u.H G) : (u.sigma Y).IsHermitian :=
  hermitian_filled _ _ (hermitian_precision (u.D Y))
lemma rates_gap (h : u.Rates η L q) (Y : Frozen u.H G) : (u.sigma Y).PosDef :=
  numeric_positive _ (u.real_precision Y) η L (h.gap Y) h.pos
lemma rates_cov (h : u.Rates η L q) (Y : Frozen u.H G) : (u.complete Y).PosDef :=
  covariance_from_rate (u.rates_gap h Y) (hermitian_filled _ _ (h.symm Y)) (h.rate Y) h.high
lemma rates_core (h : u.Rates η L q) (Y : Frozen u.H G) : (u.C Y).PosDef := by
  have he := blank_positive u.H (u.complete Y) (u.rates_cov h Y)
  unfold complete filled at he; rwa [blank_meets] at he

/-- Matrix identities for density ratio bookkeeping. Finite
real Gram/cov matrices. -/
lemma rates_trace (h : u.Rates η L q) (Y : Frozen u.H G) :
    0 < (1+u.eps Y).det ∧ Round.traceLog (u.eps Y)=Real.log (1+u.eps Y).det ∧
    Real.log (u.C Y).det= -Real.log (precision (u.D Y)).det + Round.traceLog (u.eps Y) ∧
    ∀ i j, HasSum (fun n : ℕ => ((-u.eps Y)^(n+1) * u.sigma Y) i j)
      (((u.complete Y)⁻¹-u.sigma Y) i j) := by
  obtain ⟨_,_,_,hp,_,he,hh,hM⟩ := split_costs (S:=u.eps Y) (u.rates_gap h Y)
    (u.rates_cov h Y).1 rfl (h.rate Y) h.low h.high
  unfold complete sigma at hh
  rw [paid_filled, paid_filled] at hh
  exact ⟨hp,he,hh,hM⟩

def spread (β : ℝ) := (Real.sqrt β)⁻¹
omit [Fintype rooms] in
lemma spread_beta (Y : ℝ) (h : 0 < Y) : 0 < spread Y ∧ spread Y ^ 2=Y⁻¹ :=
  ⟨inv_pos.mpr (Real.sqrt_pos.mpr h), by rw [spread,inv_pow,Real.sq_sqrt h.le]⟩

def material (β : ℝ) (L : F.Slice G → ℝ) (Y : Frozen u.H G) (a : VV (Bits G u.H)) :=
  Real.exp U * Real.exp (charge (u.D Y) (u.b0 Y) (spread β) a) *
    (leafRatio O u.veil a * (raw d P k V (included V Y a) * L (included V Y a)))

def visit (β : ℝ) (L : F.Slice G → ℝ) (Y : Frozen u.H G) (z : VV (Bits G u.H)) :=
  sample (u.D Y) (u.C Y) (u.b0 Y) (u.μ Y) (spread β) (u.material d P k V U β L Y) z

def chargeOut (B0 : Wall (Key F G)) (β : ℝ) (Y : Frozen u.H G) :=
  residualLog F O β u.H B0 (u.sigma Y) (u.complete Y)

private lemma fibre_cost (Y : Frozen u.H G) (β : ℝ) (L : F.Slice G → ℝ)
    (a : VV (Bits G u.H)) :
    coupon O u.veil d P k V L Y a =
      (Real.exp (-U) * O.scale ^ (nt F-u.H.card)) *
        (Real.exp (-charge (u.D Y) (u.b0 Y) (spread β) a) * u.material d P k V U β L Y a) := by
  rw [coupon,material, leaf_order]
  dsimp only
  rw [Real.exp_neg, Real.exp_neg]; field_simp

/-- Expose every `surface` with its Y-dependent exponent. No determinant
signed square roots presumed silently. -/
lemma pricing (hO : LocalRatio O) (hm : S.patch.Branches S.kernel G) (h : u.Rates η L q)
    (β : ℝ) (hp : 0 < β) (J : F.Slice G → ℝ) (he : Envelope J) (Y : Frozen u.H G) :
    Integrable (u.visit d P k V U β J Y) (fieldLaw (u.C Y)) ∧
    (∫ a, coupon O u.veil d P k V J Y a) = Real.exp (-U) * surface F O β u.H (u.complete Y) *
      ∫ z, u.visit d P k V U β J Y z ∂fieldLaw (u.C Y) := by
  let ψ := u.material d P k V U β J Y
  let g := spread β
  let f := fun a => Real.exp (-charge (u.D Y) (u.b0 Y) g a) * ψ a
  let x := Real.exp (-U) * O.scale^(nt F-u.H.card)
  have hx : 0 < x := mul_pos (Real.exp_pos _) (pow_pos hO.scale _)
  have hv : coupon O u.veil d P k V J Y = fun a => x * f a := funext (fun _ => u.fibre_cost ..)
  have hz := (coupon_cost O u.veil d P k V hm hO J he).2.2 Y
  have hf : Integrable f := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hx.ne') f).mp (hv ▸ hz)
  have ha := u.rates_core h Y
  have hg : 0 < g := (spread_beta β hp).1
  obtain ⟨hN,hU⟩ := charge_integral _ _ ha (u.μ Y) g hg ψ hf
  change (∫ a,f a) = _ * _ * _ at hU
  refine ⟨hN,?_⟩
  unfold surface complete
  rw [hv, integral_const_mul, hU,count_bits,paid_filled]
  rw [show 2*Real.pi*g^2= 2*Real.pi/β by rw [show g^2=_ from (spread_beta β hp).2]; ring]
  unfold visit ψ x g; ring

lemma free_line (F : Forest S.ratio) (O : ChartRatio G) (β : ℝ) (B0 : Wall (Key F G))
    (hO : LocalRatio O) (hp : 0 < β) (hb : 0 < B0.det) : 0 < flatLine F O β B0 :=
  mul_pos (pow_pos (link_factor_pos O hO β hp) _) (inv_pos.mpr (Real.sqrt_pos.mpr hb))

def till (B0 : Wall (Key F G)) := ∫ Y,
  Real.exp (u.chargeOut B0 R.beta Y) * (∫ z, u.visit d P k V U R.beta (pressureRows k V R) Y z
    ∂fieldLaw (u.C Y)) ∂bins u.H G

lemma drop_surface (B0 : Wall (Key F G)) (hO : LocalRatio O) (β : ℝ) (hp : 0 < β) (hb : 0 < B0.det)
    (h : u.Rates η L q) (Y : Frozen u.H G) :
    surface F O β u.H (u.complete Y) = flatLine F O β B0 * Real.exp (u.chargeOut B0 β Y) :=
  (unloads F O hO β hp u.H B0 _ _ hb (u.rates_gap h Y) (u.rates_cov h Y).1 h.low h.high (h.rate Y)).2.symm

/-- `Fsct` part track inside the same Y-integral. Thus no need for
pulling a seed-independent factor across a change in precision without
charging its field-dependent ratio. -/
lemma assembled (hO : LocalRatio O) (hm : S.patch.Branches S.kernel G) (h : u.Rates η L q)
    (β : ℝ) (hp : 0 < β) (J : F.Slice G → ℝ) (he : Envelope J) (B0 : Wall (Key F G))
    (hb : 0 < B0.det) :
    let I := fun Y => Real.exp (u.chargeOut B0 β Y) * (∫ z, u.visit d P k V U β J Y z ∂fieldLaw (u.C Y))
    (∀ Y, (∫ a, coupon O u.veil d P k V J Y a) = flatLine F O β B0 * Real.exp (-U) * I Y) ∧
    Integrable I (bins u.H G) := by
  intro I
  have hx : 0 < flatLine F O β B0 * Real.exp (-U) := mul_pos
    (free_line F O β B0 hO hp hb) (Real.exp_pos _)
  have hg Y : (∫ a, coupon O u.veil d P k V J Y a) = flatLine F O β B0 * Real.exp (-U) * I Y := by
    rw [(u.pricing d P k V U hO hm h β hp J he Y).2, u.drop_surface _ hO β hp hb h]
    unfold I; ring
  refine ⟨hg, (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hx.ne') I).mp ?_⟩
  have h' := (coupon_cost O u.veil d P k V hm hO J he).2.1.integral_prod_left
  simp_rw [← hg]; exact h'

/-- `balance` of this *exact* store/tag on the stripped interacting
input. Assumes only the Opened law and the named finite-table estimates
here (plus positive beta, base determinant and R.Lawful).
Proves pointwise value; log at identity handled separately. -/
theorem supplies (hO : LocalRatio O) (hm : S.patch.Branches S.kernel G) (h : u.Rates η L q)
    (A : Opened O u.veil d P k V) {σ C Λ δ w : ℝ} (hR : R.Lawful σ C Λ δ w) (hr : 0 < R.beta)
    (B0 : Wall (Key F G)) (hb : 0 < B0.det) :
    balance d F R.beta (stripped R) P k V =
      flatLine F O R.beta B0 * Real.exp (-U) * u.till d P k V R U B0 := by
  rw [press _ _ d P k V hm hR A, till,← integral_const_mul]
  have hi := pressure_env (F:=F) k V hm hR
  apply integral_congr_ae; filter_upwards with Y
  exact (u.assembled d P k V U hO hm h R.beta hr _ hi B0 hb).1 Y

omit [Fintype rooms] in
private lemma veil_nonneg (hO : LocalRatio O) (w : VV (Bits G u.H)) : 0 ≤ leafRatio O u.veil w := by
  refine Finset.prod_nonneg (fun i _ => ?_)
  by_cases he : u.veil.size < ‖hue i w‖
  · rw [u.veil.off i _ he,zero_mul]
  apply mul_nonneg (u.veil.nonneg ..)
  exact (hO.pos _ (Metric.mem_ball.mpr (by rw [dist_zero_right]; exact lt_of_le_of_lt (le_of_not_gt he) u.veil.small))).le





end Fiber
end YM.Further.GaussianScalar
