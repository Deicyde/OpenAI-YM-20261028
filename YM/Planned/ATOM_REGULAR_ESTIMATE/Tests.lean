import YM.Planned.ATOM_REGULAR_ESTIMATE.Pass
import YM.Planned.ATOM_REGULAR_ESTIMATE.Sampled

/-!
Derive the quantitative regular-atom income estimates for each
component of a kernel expansion. In particular these do NOT assume
bounds on any normalized spatial derivatives of the *outputs*, nor
smoothness of any conditional expectation built independently of the
vacuum integral. No truncation of sums of paths. Constants set before L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Filter Lattice Wilson RG MeasureTheory Push.Local WardBin.Lies Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {G : Gauge} {n m L : Side} {B P : BudgetPoint} {X : Support n} {Y : Support m} {d k : ℕ}
    {o : Site n} {x : Site m} {a w c : ℝ} {V : Config G m} {f : Config G n → ℂ}

namespace Sample

variable {S : Sample G m n} {C : Feed G m n} {l : ℕ} {U : Slab G m l}

/-- Numerical-only on samples, density and link charts. Specializations for
principal and other kernels below. The order `k` passes a fixed joint score
through *one* integral, including movement of a packet with its density; no
product law substitution. -/
def Built (S : Sample G m n) (V : Config G m) (U : Slab G m l) (k : ℕ) (w : ℝ) (H : S.Z → ℝ → Prop) :=
  ∃ a v : S.Z → ℝ, Integrable (fun z => a z * v z ^ k) S.μ ∧ (∫ z, a z * v z ^ k ∂ S.μ) ≤ w ∧
    ∀ᵐ z ∂ S.μ, 0 ≤ a z ∧ 1 ≤ v z ∧ (S.Quiet z V U ∨ S.Tariff z V U (a z) ∧ H z (v z))

lemma Built.price {H : S.Z → ℝ → Prop} (h : S.Built V U k w H) (hm : Measures S B o X V k C)
    (hC : ∀ᵐ z ∂ S.μ, ∀ a v, 0 ≤ a → 1 ≤ v → S.Tariff z V U a → H z v →
      ‖iteratedFDeriv ℝ l (S.inChart f z ∘ journey V l U) 0 cart‖ ≤ c * (a*v^k))
    (hp : Permitted B o X f) (hl : l≤k) (hc : 0 ≤ c) :
    Chart k (C f) V ∧ ‖leftDerivs (C f) (List.ofFn U) V‖ ≤ c*w := by
  obtain ⟨hh,hf,hu⟩ := left_integral V U hl (hm.covered f hp) (hm.read f hp)
  obtain ⟨a,b,h₀,h₁,h₂⟩ := h
  refine ⟨hh,?_⟩
  rw [hu]; refine (norm_integral_le_of_norm_le (h₀.const_mul c) ?_).trans ?_
  · filter_upwards [h₂,hC] with z hz ht
    obtain ⟨ha,hb,ht'|hq⟩ := hz
    · rw [quiet_test ht', zero_apply, norm_zero]; positivity
    exact ht _ _ ha hb hq.1 hq.2
  rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left h₁ hc



lemma journey_origin (V : Config G m) (U : Slab G m k) : journey V k U 0 = V := by
  rw [journey_photon, Function.comp_apply, map_zero,chug_zero]






end Sample

/-- Kernel bulk-cylinder support. B70 permitted test on X for locality
measure conventions. Actions include gauge invariance of its weak unmasked
germ/representative. No normalization demands implicit in this condition. -/
structure Shelled (C : Feed G m n) (B : BudgetPoint) (o : Site n) (X : Support n) (Y : Support m) : Prop where
  support : ∀ f, Permitted B o X f → LocalOn Y (C f)
  sym : ∀ f, Permitted B o X f → GaugeInvariant (C f)
  borel : ∀ f, Permitted B o X f → Measurable (C f)

def regularCharge (k : ℕ) := (2:ℝ)^k * (patterns k * diagonals k)
def centralCharge (G : Gauge) (k d : ℕ) := (2:ℝ)^k * Sample.slopeCost G k d
lemma regular_nonneg (k : ℕ) : 0 ≤ regularCharge k := by unfold regularCharge; positivity [patterns_nonneg k, diagonals_nonneg k]
lemma central_nonneg (G : Gauge) (k d : ℕ) : 0 ≤ centralCharge G k d := by
  unfold centralCharge; positivity [Sample.slopeCost_nonneg G k d]

namespace Sample
open Next.Foundations
variable {S : Sample G m n} {C : Feed G m n}

protected lemma _root_.YM.Planned.AtomRegular.Shelled.charts
    (h : Shelled C B o X Y) (hp : Permitted B o X f) (hc : 0 ≤ c)
    (he : ∀ V, Healthy P.threshold Y V → ∀ l, l≤P.order → ∀ A : Slab G m l,
      (∀ i : Fin l, P.dirBound x (A i)) →
       Chart P.order (C f) V ∧ ‖leftDerivs (C f) (List.ofFn A) V‖ ≤ c) :
    P.Regular Y (C f) ∧ P.supBounds x Y (C f) c := by
  have ht V (hi : Healthy P.threshold Y V) : Chart P.order (C f) V :=
    (he V hi 0 (Nat.zero_le _) 0 (by simp)).1
  refine ⟨⟨h.support f hp,h.borel f hp,h.sym f hp,ht,fun _ hv A l hl => left_has A hl (ht _ hv)⟩, hc,fun V hv l hl H => ?_⟩
  simpa [List.ofFn_get] using! (he V hv _ hl l.get (fun i => H _ (List.get_mem l i))).2

def Eased (C : Feed G m n) (B P : BudgetPoint) (o : Site n) (x : Site m) (X : Support n) (Y : Support m)
    (w : ℝ) := ∀ V, Healthy P.threshold Y V → ∀ l, l≤P.order → ∀ A : Slab G m l, (∀ i, P.dirBound x (A i)) →
      ∃ S : Sample G m n, S.Measures B o X V P.order C ∧ S.Built V A P.order w (fun z a => S.Coasting z B o X V A a)

def Rolling (C : Feed G m n) (B P : BudgetPoint) (o : Site n) (x : Site m) (X : Support n) (Y : Support m)
    (w : ℝ) (d : ℕ) (L : Side) := ∀ V, Healthy P.threshold Y V → ∀ l, l ≤ P.order →
      ∀ A : Slab G m l, (∀ i,P.dirBound x (A i)) → ∃ S : Sample G m n, S.Measures B o X V P.order C ∧
        S.Built V A P.order w (fun z a => S.Shoots z B o X V A a d L)

lemma Eased.test (h : Eased C B P o x X Y w) (hr : Shelled C B o X Y) (hf : B.Regular X f)
    (hp : B.supBounds o X f c) (hw : 0 ≤ w) (hk : P.order ≤ B.order) :
    P.Regular Y (C f) ∧ P.supBounds x Y (C f) (regularCharge P.order*c*w) := by
  let k := P.order
  have hc := hp.1
  have hC := mul_nonneg (regular_nonneg P.order) hc
  have he : Permitted B o X f := ⟨hf,c,hp⟩
  refine hr.charts he (mul_nonneg hC hw) (fun V hv l hl A ha => ?_)
  obtain ⟨S,hM,hN⟩ := h V hv l hl A ha
  apply hN.price hM _ he hl hC
  refine .of_forall fun z a v ha hv ht hZ => ?_
  obtain ⟨hQ,hh⟩ := coast_test hZ hf hp hv hl hk
  exact (tariff_bill ht hl ha (by positivity [patterns_nonneg P.order,diagonals_nonneg P.order]) hQ hh).trans_eq
    (by unfold regularCharge; ring)

/-- `C` gets its pre-mask propagation regularity from the tested *kernel*
and income receipts. Exact support and old-family budgets. This is a
single branch. The gain for `x`-lead & rem in PaidAtom will need the
*scaled* and summed densities and all flags restored. -/
theorem Rolling.test {R : Source.Hol G} (h : Rolling C B P o x X Y w d L) (hr : Shelled C B o X Y) (hw : 0 ≤ w)
    (hf : B.Regular X f) (hp : B.supBounds o X f c) (he : R.PiVanish d o f) (hx : Nonwrapping X o)
    (hn : 2 ≤ n.val) (hi : ∀ i∈screens X, weight B o i ≤ 1) (hd : d+1 ≤ P.order) (hk : P.order ≤ B.order) :
    P.Regular Y (C f) ∧ P.supBounds x Y (C f) (centralCharge G P.order d * (c*((L.val:ℝ)⁻¹)^(d+1))*w) := by
  let k := P.order
  have hc := hp.1
  have hC := mul_nonneg (central_nonneg G P.order d) (mul_nonneg hc
    (show 0 ≤ ((L.val:ℝ)⁻¹)^(d+1) by positivity))
  have hD : Permitted B o X f := ⟨hf,c,hp⟩
  refine hr.charts hD (mul_nonneg hC hw) (fun V hv l hl A ha => ?_)
  obtain ⟨S,hM,hN⟩ := h V hv l hl A ha
  apply hN.price hM _ hD hl hC
  refine .of_forall fun z a v ha hv ht hZ => ?_
  obtain ⟨hQ,hh⟩ := principal_test hZ hf hp he hx hn hi hv hl hd hk
  exact (tariff_bill ht hl ha (by positivity [slopeCost_nonneg G P.order d]) hQ hh).trans_eq (by unfold centralCharge; ring)
end Sample
end YM.Planned.AtomRegular
