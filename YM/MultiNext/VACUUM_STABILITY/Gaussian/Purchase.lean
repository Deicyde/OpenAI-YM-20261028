import YM.MultiNext.VACUUM_STABILITY.Component.FirstEst
import YM.MultiNext.VACUUM_STABILITY.Gaussian.Tail


set_option warningAsError false

/-!
# Uniform ProductCost from chart/hard score formulas

For the analytic gate . Uses per-letter product majorants earlier in the
integrals themselves. Actual producer to give score integral on THAT conditional law; after
proving the open-neighborhood domination, taking held kernels and identity/change of variables,
report the equality *back* on the standard marginal generated with q, every hard U argument and
tag respected. Even if an identity is convenient by first randomizing extra Gaussian variables,
no C^volume estimate licensed. k fixed after-L. Requires gifts to pay the per-occurrence
integrand weights and used trigger/location invariants, not just `Z[A]` normalized vStep.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Gauss
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Desk Component
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

-- A polynomial N growth cost in score with H*(1+d) sizes

def coat (K H : ℝ) (k : ℕ) := k.factorial * (H/coin K)^k * Real.exp (coin K+2*K*coin K)

lemma covered {K H d W b : ℝ} (k : ℕ) {I : Type} [Fintype I] (s : ℕ)
    (hK : 0 ≤ K) (hH : 1 ≤ H) (_hd : 0 ≤ d) (he : 1+(Fintype.card I : ℝ) ≤ H*(1+d)) :
    quota K (rim I K) (Fintype.card I) k W s b ≤ coat K H k * (1+d)^k * Real.exp (-coin K*b + 2*K*(W+s*coin K)) := by
  let t:=coin K; let r:=rim I K
  have hu : 0<r := (rim_ok hK).1; have ht : 0<t := (coin_ok hK).1
  have hp : (Fintype.card I:ℝ)*r ≤ t := by
    apply le_trans _ (show (1+Fintype.card I)*r=t from (rim_ok hK).2).le
    apply mul_le_mul_of_nonneg_right _ hu.le; simp
  have hz : r ≤ t := rim_le hK
  have hQ : 0 ≤ H := zero_le_one.trans hH
  let a := -t*b + 2*K*(W+s*t)
  unfold quota coat
  calc
    _ ≤ (k.factorial/r^k)*Real.exp (t+2*K*t+a) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_monotone; unfold a
      change r-t*b+_ ≤ _
      have hs := mul_le_mul_of_nonneg_left hp hK; linarith
    _ ≤ (k.factorial*((H/t)*(1+d))^k)*Real.exp (t+2*K*t+a) := by
      rw [div_eq_mul_inv, ← inv_pow]; gcongr
      unfold r rim
      rw [inv_div, div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right he ht.le
    _ = _ := by rw [mul_pow,Real.exp_add]; ring

/- One coefficient (or one term of its marked or actual derivative). p powers after-L.
Charge `pay` before doing the integration, on this effect. -/
structure Pays (K H : ℝ) (k : ℕ) (d payment : ℝ) (value : ℂ) where
  -- these are data, attached to this single computation. integrand should
  -- always describe same conditional evaluation/gauge change.
  fiber : Type
  [ms : MeasurableSpace fiber]
  binder : @Measure fiber ms
  [normalized : @IsProbabilityMeasure fiber ms binder]
  -- lengths; finite counts, may include redundant inactive Z arguments
  I : ℕ
  J : ℕ
  chart : fiber → Row (Fin J) → ℂ
  -- may use a varying construction under the binder. inner measurable and score pointwise.
  earns (e : fiber) : AEStronglyMeasurable (chart e) (standard (Fin J)) ∧
    ∃ (q : Fin I → Row (Fin J)) (w : Row (Fin I)) (W c b : ℝ) (T : Finset (Fin I)),
      adjBound q K ∧ (∀ i,0≤w i ∧ K*w i ≤ 1/8) ∧ ∑ i,w i ≤ W ∧ 0 ≤ c ∧
      c * Real.exp (-coin K*b + 2*K*(W+T.card*coin K)) ≤ payment ∧
      ∀ᵐ y ∂standard (Fin J), chart e y≠0 →
        let z := mapRows q y
        ‖chart e y‖ ≤ c*(1+squares z)^k * Real.exp (pay w z) ∧ b ≤ ∑ i∈T,z i ^2
  body : 1+(I:ℝ) ≤ H*(1+d)
  writes : AEStronglyMeasurable (fun e => ∫ y, chart e y ∂standard (Fin J)) binder
  line : value = ∫ e, ∫ y, chart e y ∂standard (Fin J) ∂binder

lemma countPays {K H d payment : ℝ} {k : ℕ} {value : ℂ} (t : Pays K H k d payment value) (h : 0 ≤ K) (hH : 1 ≤ H) (hd : 0≤d) :
    ‖value‖ ≤ coat K H k * (1+d)^k * payment := by
  letI := t.ms; letI := t.normalized
  let D := coat K H k * (1+d)^k * payment
  let f := fun e => ∫ y, t.chart e y ∂standard (Fin t.J)
  have hc : 0 ≤ coat K H k := by
    unfold coat; have he : 0<coin K := (coin_ok h).1; have hg := zero_le_one.trans hH; positivity
  have he (e) : ‖f e‖ ≤ D := by
    obtain ⟨he,q,w,W,c,b,T,hq,hW,hp,hc',hv,hi⟩:=t.earns e
    obtain ⟨hf,hF⟩:=score q hq h w (fun i => (hW i).1) (fun i => (hW i).2) k T c b W (t.chart e) he hc' hp hi
    have ht : 1+(Fintype.card (Fin t.I):ℝ) ≤ H*(1+d) := by simpa using t.body
    have hw := covered (I:=Fin t.I) (b:=b) (W:=W) k T.card h hH hd ht
    refine ((norm_integral_le_integral_norm _).trans hF).trans <| (mul_le_mul_of_nonneg_left hw hc').trans ?_
    calc
      _ = coat K H k*(1+d)^k * (c*Real.exp (-coin K*b+2*K*(W+T.card*coin K))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
  have hf : Integrable f t.binder := Integrable.of_bound t.writes D (Eventually.of_forall he)
  rw [t.line]
  exact ((norm_integral_le_integral_norm _).trans (integral_mono (μ:=t.binder) hf.norm (integrable_const D) he)).trans_eq (by simp [D])

/-!
One precise earlier route to per-component tests. Field and halo indexing in `Pays` consumed
at output `P.p`. In quantum RG and standalone histories need also stamp format,
locality and equality hypotheses; this is for the ANALYTIC estimate only. Can pay here with
ζ-dependent integrand bounds and any extra exponent after-L, all explicitly selected. Use e.g.
one additional amount of cover power per hard flag test or volume polynomial per USED support,
not per ambient volume. With true normalized kernel score rewrites even in a large patch.
-/

namespace Live
open Component.Pasture
variable {V I : Type} {G : Gauge} {n : Side} {B : Brush V G n} [Fintype V]
variable (A : Pasture I B)

def bill (M : ℕ) (i : Fruit) : ℝ := ∑ j∈A.bud i,((coverNumber M (A.sites j):ℕ):ℝ)

omit [Fintype V] in
private lemma extentBill (M l k : ℕ) (i : Fruit) (f : I→ℝ) : (1+bill A M i)^l * A.feast f k M i = A.feast f (l+k) M i := by
  unfold feast bill; push_cast; rw [pow_add,mul_assoc]

/-- Has every integrand formula, product size conditions *before* doing the joint Z, orders,
mask tests. This does not assume a final pack activity cost, not even weighted sums over
raw components. h arbitrary checked derivative list. -/
structure Form (P : BudgetPoint) (z : V→ℂ) (K H C κ : ℝ) (k l : ℕ) (f : I→ℝ) : Prop where
  lanes i U : Healthy P.threshold (B.u i).zone U → ∀ h : List (Directions G n), h.length ≤ P.order → (∀ A∈h,P.dirBound (B.u i).anchor A) →
      Nonempty (Pays K H l (bill A P.B (.inl i)) (C*A.feast f k P.B (.inl i))
        (leftDerivs ((B.u i).stamp.tell z) h U))
  track i U : Nonempty (Pays K H l (bill A P.B (.inr i)) (κ*(C*A.feast f k P.B (.inr i))) ((B.d i).tell z U))

/-- One-component uniform integral price feeds the actual earlier ticket. -/
theorem open_for (P : BudgetPoint) (z : V→ℂ) {K H C κ : ℝ} (hh : 0 ≤ K) (hH : 1 ≤ H) (hC : 0 ≤ C) {k l}
    {f : I→ℝ} (h : Form A P z K H C κ k l f) {c r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hx : Cluster.siteUnit P.B*t ≤ 1) (hf : Ac.Hit A.sites P.B f (r+2) t)
    (hd : coat K H l*C*(sizeTax (l+k)*(Real.exp t-1)) ≤ c) : A.ProductCost P z c r κ := by
  have hu : 0 ≤ coat K H l := by unfold coat; have := (coin_ok hh).1; have h := zero_le_one.trans hH; positivity
  have hF := (Absolute.burden A.origin hf).1
  have hz i : 0 ≤ bill A P.B i := Finset.sum_nonneg fun i _ => by positivity
  have he := mul_nonneg hu hC
  refine ⟨hr, l+k,coat K H l*C,t,f,he,ht,hx,hd,hf,fun i => ⟨mul_nonneg he (A.feast_nn hF ..),?_⟩,fun i U => ?_⟩
  · intro U hh' v hv ht
    obtain ⟨x⟩ := h.lanes i U hh' _ hv ht
    refine (countPays x hh hH (hz _)).trans_eq ?_; rw [← extentBill]; ring
  obtain ⟨x⟩:=h.track i U
  refine (countPays x hh hH (hz _)).trans_eq ?_; rw [←extentBill]; ring
end Live
end YM.Multi.Vacuum.Gauss
