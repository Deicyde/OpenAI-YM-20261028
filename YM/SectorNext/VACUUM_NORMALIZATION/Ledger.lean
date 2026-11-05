import YM.Push.SECTOR_MEASURE.Presented
import YM.SectorNext.VACUUM_NORMALIZATION.Clinic
import YM.SectorNext.VACUUM_NORMALIZATION.Factors
import YM.SectorNext.VACUUM_NORMALIZATION.Relative



/-!
# Scalar office for an actual proposed step

Assembly is not in the cache. This module exposes an upstream **term**
interface on the same R, F, D and b,E,d. Balances use support resolution
before dropping any profiles (and keep the likelihood). Prices on emitted
atoms go through cover hits at *this* b. No assumption on existence,
summability, Hessian or other jets of localized/log output arrays. Derive
true log, scalar and absolute bills in the indicated norms. In particular
no circular hypothesis that unforced gas or the interpreted determinant
in Fsct is already the exponential of a legitimately paid label family.
No assertion of closeness of the interacting result to the free prefactor.

One sufficient identity interface: BEFORE arguing legality of any logs,
issue the opened `balance` (where old scalar and penaltyZ already factored)
by terms indexed by the eventual unforced and forced addresses (not the
new logarithm occurrences!).

Factors in `work` have to
validate at the physical fields and tags displayed here.

In particular
use broad likelihood reference of `balance` with its counting factor on
right step.

If e.g., working relative to normalized Gaussian, the masses
must really be converted from the probability Haar measures here; see also
`unloads` for scalar part of such a proof.

Can reindex more elaborate sums to
these common addresses e.g. once absolute bounds are known.

Allows frozen
sector integrals and ratios to stay INSIDE those terms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open RG Lattice Wilson Tree Filter Precision MeasureTheory Pressure Pressure.Stores Push.SectorMeasure Presented Next.Fluctuations.Sector Finset
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology
variable {G : Gauge} {c f : Side} {S : StepData c f} {x W : ℝ}

/-- `work` prices & equality asked on the FULL finite-volume Haar
integrals of sector parts, issued one per column (no raw Plot sums).
`compiled` then requires the **coefficientwise** first-integrated-gas
identification, not equality to the normalized density nor a log split,
for these common component addresses after shared-tag integration. Need
absolute bounds on the work issued to justify trading order.
α=ℕ, duplicate supports may have different integration histories.
G0 is the positive-orientation averaged output *base COST*, with sign
convention exp(-G0); includes the beta callers allocate there. `B0`
must be the same *flat* gram used in all work. Inactive fields do not
multiply it each time. -/
structure Counter (D : Allocation G S x W) (F : Forest S.ratio) (A : ChartRatio G)
    (B0 : Round.Wall (Key F G)) (G0 : Config G c→ℝ) (R : Rep G f)
    (X : ℕ→Support c) (b : BudgetPoint) (E : ℕ→ Config G c→ℝ) (d : Activities G c) where
  work : Stores S→S.Choices→Finset ℕ→Finset ℕ→Config G c→ℝ
  settle (a k V) : Summable fun i : Finset ℕ × Finset ℕ => work a k i.2 i.1 V
  scanned (a k V) : balance D F R.beta (stripped R) a k V = ∑' i : Finset ℕ × Finset ℕ, work a k i.2 i.1 V
  compiled (P Q V) : (∑ a,∑ k,tagRef k*work a k P Q V) = flatLine F A R.beta B0 * Real.exp (-G0 V) *
    (d.gasOccurrence b Q V * ReLog.note X (ReLog.herald X b E V) (Finset.univ \ ReLog.pad d Q) P)

variable {D : Allocation G S x W} {F : Forest S.ratio} {A : ChartRatio G} {B0 : Round.Wall (Key F G)} {G0 : Config G c→ℝ}
  {R : Rep G f} {X : ℕ→Support c} {b : BudgetPoint} {E : ℕ→Config G c→ℝ} {d : Activities G c}
  (h : Counter D F A B0 G0 R X b E d)
include h

lemma scan_all (V : Config G c) :
    ∑ a,∑ k,tagRef k*balance D F R.beta (stripped R) a k V = flatLine F A R.beta B0 * Real.exp (-G0 V) * ReLog.first X b E d V := by
  let M (i : Finset ℕ × Finset ℕ) := ∑ a,∑ k,tagRef k*h.work a k i.2 i.1 V
  have H (a : Stores S) (k : S.Choices) := (h.settle a k V).mul_left (tagRef k)
  have Hk a := summable_sum (fun k (_ : k∈ Finset.univ)=> H a k)
  have hM : Summable M := summable_sum (fun a (_ : a∈Finset.univ)=> Hk a)
  calc
    _ = ∑' i,M i := by simp_rw [h.scanned,← tsum_mul_left,← Summable.tsum_finsetSum (fun k _=> H _ k),← Summable.tsum_finsetSum (fun a _=> Hk a)]; rfl
    _ = ∑' Q, ∑' P : Finset ℕ,M (Q,P) := hM.tsum_prod
    _ = _ := by unfold M; simp_rw [h.compiled,tsum_mul_left]; rfl

/-- Apply on REAL densities. Includes all choices, one F (for a mixture
average with same parameters/tag-invariant B price verify determinant
& coefficients before invoking forest_mass). -/
theorem issues {σ C Λ δ w : ℝ} (hK : S.patch.Branches S.kernel G) (hR : R.Lawful σ C Λ δ w)
    (V : Config G c) :
    S.push R.beta R.eval V = Real.exp R.scalar * prefactor S G R.beta * flatLine F A R.beta B0 *
      Real.exp (-G0 V)*ReLog.first X b E d V := by
  rw [← push_columns D F R.beta _ hK ((R.envelope hR).integrable _) (lawful_gi hR) V]
  simp_rw [output_factors,← Finset.mul_sum, balanced_column D F R.beta hK,smul_eq_mul,← Finset.mul_sum]
  rw [scan_all h]; ring

/-- Scalar equality & log legality, per-site. Doesn't need continuity
or output E normalization, so can even use this v formula TO set E'
scalar during shot. When h'Lawful & H are available they're only used to
read/fix v; result for the true push also independent. The sum of raw
costs here is volume bounded from `Fund`. Works on flags by retaining
corrections (formula also exported); p-M splices chosen elsewhere. -/
theorem office {σ C Λ e w : ℝ} (hK : S.patch.Branches S.kernel G) (hR : R.Lawful σ C Λ e w)
    (hA : LocalRatio A) (hb : 0<R.beta) (hM : 0<B0.det) (hk : G0 1=0)
    {v : ℕ→ℝ} (t : ReLog.Tags X b E v) (M : ℕ) {l a δ : ℝ} (hF : ReLog.Fund X M l a δ v) :
    let z := ∑ i : Support c,ReLog.raw X E i 1
    let bill := R.scalar + (-wires c*Real.log (S.penaltyZ R.beta G) +
        nt F * Real.log (gaussLink A R.beta) - Real.log B0.det/2)-z
    |z| ≤ sites c*a ∧
      S.push R.beta R.eval 1 = Real.exp bill ∧
      Real.log (S.push R.beta R.eval 1) = bill ∧
      (∀ y, S.push R.beta R.eval y = Real.exp bill *
        Real.exp (-G0 y - ∑ i : Support c, ReLog.devalue X b E i y) * ∑' Q, ReLog.remains X b E d Q y) ∧
      ∀ {σ' C' Λ' δ' w' : ℝ} (R' : Rep G c), R'.Lawful σ' C' Λ' δ' w' → R'.eval=S.push R.beta R.eval →
        R'.v = (S.patch.L.val:ℝ)^4*R.v - 4*Real.log (S.penaltyZ R.beta G) +
          (nt F*Real.log (gaussLink A R.beta) - Real.log B0.det/2-z)/sites c := by
  intro z bill
  have he : |z| ≤ sites c*a := by
    have hr := ReLog.extensive X t M hF 1
    simp_rw [ReLog.at_zero] at hr; exact (Finset.abs_sum_le_sum_abs ..).trans hr
  have hi := (S.penaltyZ_pos (G:=G) R.beta)
  have hg := link_factor_pos A hA R.beta hb
  have hh : 0<Real.sqrt B0.det := Real.sqrt_pos.mpr hM
  have ht : Real.exp bill= Real.exp R.scalar*prefactor S G R.beta*flatLine F A R.beta B0*Real.exp (-z) := by
    have hx : Real.log B0.det/2=Real.log (Real.sqrt B0.det) := (Real.log_sqrt hM.le).symm
    unfold flatLine prefactor bill
    simp_rw [sub_eq_add_neg,neg_mul,Real.exp_add,Real.exp_neg,hx]
    unfold wires; rw [Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log hg,Real.exp_log hh,Real.exp_log hi]; rw [inv_pow]; ring
  have hw := issues h hK hR 1
  rw [hk,neg_zero,Real.exp_zero,mul_one,ReLog.first_flat X b E d t M hF] at hw
  change _ = _*Real.exp (-z) at hw; rw [←ht] at hw
  refine ⟨he,hw,by rw [hw,Real.log_exp],fun V=> ?_,fun R' hh' hm=>?_⟩
  · rw [issues h hK hR,ReLog.total_reassemble X b E d t M hF,ht]; simp_rw [sub_eq_add_neg,Real.exp_add]; unfold z; ring
  rw [←hm,flat_density _ hh'] at hw
  have H := Real.exp_injective hw
  unfold Rep.scalar bill at H; change R'.v*sites c= R.v*sites f+ (-wires c*_ + _-_) -z at H
  rw [wires_sites, sites_ratio S] at H
  have hh := site_pos c
  field_simp; linarith




end YM.SectorNext.Vacuum
