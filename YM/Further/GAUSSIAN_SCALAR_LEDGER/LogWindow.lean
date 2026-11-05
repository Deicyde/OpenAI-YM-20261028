import YM.Further.GAUSSIAN_SCALAR_LEDGER.Correction
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Resolvent
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Threshold
import YM.Next.SCHEDULE.Postal

set_option warningAsError false

/-!
# Real scalar logdet ledger by local windows

Echs. For each coordinate i evaluate `Panel.priceLine`, via this *exact*
principal-window resolver. Value and tail legitimate on every finite
volume, uniform errors (value not V derivatives). Entries still need
locality w.r.t physical parameters etc., Bounds are per slot.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Matrix Function Filter Precision SectorNext.Vacuum Lattice Unitary
open Round (rowRate)
open MeasureTheory Set
open YM.Progress.StationaryScenes.Green
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Lens

variable (Z : Lens ι)

def localLine (A : Wall ι) (L : ℝ) (i : ι) := Panel.priceLine (Z.glass A i) L (Z.center i)

omit [DecidableEq ι] in
lemma numerate (A : Wall ι) (a b : ℝ) (h : Numeric A a b) (i : ι) : Numeric (Z.glass A i) a b := by
  let f : Z.eye i ↪ ι := Function.Embedding.subtype _
  have ht : Bottom A a := fun x => (h x).1
  have hl : Bottom (-A) (-b) := fun v => by
    rw [neg_mul,Matrix.neg_mulVec,dotProduct_neg]; exact neg_le_neg (h v).2
  intro v; refine ⟨ht.restrict f v,?_⟩
  have he := hl.restrict f v
  rw [show (-A).submatrix f f= -(Z.glass A i) from rfl,neg_mul,neg_mulVec,dotProduct_neg] at he
  exact le_of_neg_le_neg he

lemma locally_paid (A : Wall ι) (a b : ℝ) (h : Numeric A a b) (hp : A.PosDef) (ha : 0 < a) (hb : a ≤ b) (i : ι) :
    let f := fun u : ℝ => (1+u)⁻¹-Z.visit A u i i
    IntegrableOn f (Ioi 0) ∧ (∫ u in Ioi (0:ℝ), f u)=Z.localLine A b i := by
  intro f
  have hh : f = pulse (Z.glass A i) (Z.center i) := by
    funext u
    unfold f pulse full
    rw [show Z.visit A u i i = _ from Z.visit_here A u i (Z.center i)]
  rw [hh]; exact settled (hp.submatrix Subtype.val_injective) (Z.numerate A a b h i) ha hb _

def beadPulse (A : Wall ι) (n : ℕ) (i j : ι) (u : ℝ) := -(Z.visit A u*(-Z.missed A u)^(n+1)) i j

omit [Fintype ι] in
lemma visit_continuous {A : Wall ι} (h : A.PosDef) : ContinuousOn (Z.visit A) (Ioi 0) := by
  refine continuousOn_pi.mpr (fun i => continuousOn_pi.mpr fun j => ?_)
  change ContinuousOn (fun u : ℝ => Z.visit A u i j) _
  unfold visit; simp only [Matrix.of_apply]; split
  · next he => exact full_stable (show (Z.glass A j).PosDef from h.submatrix Subtype.val_injective) _ _
  exact continuousOn_const

lemma bead_continuous {A : Wall ι} (h : A.PosDef) (n : ℕ) (i j : ι) : ContinuousOn (Z.beadPulse A n i j) (Ioi 0) := by
  have hp : ContinuousOn (fun u => plus A u) (Ioi 0) := continuousOn_const.add (continuousOn_id.smul continuousOn_const)
  have ht := Z.visit_continuous h
  have he : ContinuousOn (fun u => Z.missed A u) (Ioi 0) := (hp.mul ht).sub continuousOn_const
  exact ((continuousOn_pi.mp (continuousOn_pi.mp (ht.mul (he.neg.pow (n+1))) i) j).neg)

end Lens

namespace RawPrice
variable {c : Side} (Z : Lens ι) (p : Expense) {y : ι → Site c} {A : Wall ι} {r : ℝ}
    (h : RawPrice p y A) (hr : Z.Outside y r)
include h hr

lemma bead_cost {u : ℝ} (hu : 0 ≤ u) (n : ℕ) (i j : ι) :
    |Z.beadPulse A n i j u| ≤ p.payment*p.windowCost r ^ (n+1) * ((1+u)⁻¹)^2 := by
  have he := Double.into_rate (h.ticket Z p hu hr) p.margin_pos.le
  have hf := Double.into_rate (h.lens Z p hu) (show 0≤p.halfRate from (half_pos p.tilt_pos).le)
  have hp := p.payment_pos
  have hP := p.window_pos r
  unfold Lens.beadPulse; rw [abs_neg]
  apply (row_entry _ (Round.ride _ _ hf.1 (row_pow _ he.1 (by positivity) (n+1)) (by positivity)) i j).trans
  let d := p.windowCost r
  have hA : d/(1+u) ≤ d := div_le_self hP.le (by linarith)
  calc
    _ = p.payment/(1+u) * ((d/(1+u))^n * (d/(1+u))) := by rw [← pow_succ]
    _ ≤ p.payment/(1+u) * (d^n * (d/(1+u))) := by gcongr
    _ = p.payment * d^(n+1) * ((1+u)⁻¹)^2 := by rw [pow_succ]; unfold d; ring

lemma beads_integral {n : ℕ} (i j : ι) :
    IntegrableOn (Z.beadPulse A n i j) (Ioi 0) ∧
      (∫ u in Ioi (0:ℝ), |Z.beadPulse A n i j u|) ≤ p.payment * p.windowCost r^(n+1) := by
  let M (x : ℝ) := (p.payment*p.windowCost r^(n+1))*((1+x)⁻¹^2)
  have he : IntegrableOn M (Ioi (0:ℝ)) := kernel_budget.1.const_mul _
  have ht : IntegrableOn (Z.beadPulse A n i j) (Ioi 0) := by
    apply he.mono' ((Z.bead_continuous (h.paid p) n i j).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact h.bead_cost Z p hr hu.out.le n i j
  refine ⟨ht, (setIntegral_mono_on (μ:=volume) ht.norm he measurableSet_Ioi (fun u hu => h.bead_cost Z p hr hu.out.le n i j)).trans_eq ?_⟩
  unfold M; rw [integral_const_mul,kernel_budget.2,mul_one]

/-- The sign includes the subtraction in Echs. Sum over n all finite
positions; absolute (ω relative matrix S ordered separately). -/
lemma chains (ht : Timing p r) (i : ι) :
    HasSum (fun n : ℕ => ∫ u in Ioi (0:ℝ), Z.beadPulse A n i i u)
        (Panel.priceLine A p.high i - Z.localLine A p.high i) := by
  let B := Z.beadPulse A
  let F := fun n u => B n i i u
  have hv (j : ℕ) := h.beads_integral Z p hr (n:=j) i i
  let E := p.windowCost r
  have hm := ht.misses
  have hl : E<1 := lt_trans hm (by norm_num)
  have hw := (((summable_geometric_of_lt_one (show 0≤E from (p.window_pos r).le) hl).mul_right E).mul_left p.payment)
  simp_rw [← pow_succ] at hw
  have he := hasSum_integral_of_summable_integral_norm (F:=F) (μ:=volume.restrict (Ioi 0))
    (fun n => (hv n).1) (hw.of_nonneg_of_le (fun n => integral_nonneg (fun i => norm_nonneg _))
      (fun n => (hv n).2))
  have hh : p.low ≤ p.high := le_trans (Panel.bill_quad h.hermitian h.positive i).1
    (Panel.bill_quad h.hermitian h.positive i).2
  have hx := settled (h.paid p) h.positive p.low_pos hh i
  let f := fun u : ℝ => (1+u)⁻¹-Z.visit A u i i
  have hz : IntegrableOn f (Ioi 0) ∧ (∫ u in Ioi (0:ℝ), f u)=Z.localLine A p.high i :=
    Z.locally_paid A p.low p.high h.positive (h.paid p) p.low_pos hh _
  rw [← hx.2,← hz.2,←integral_sub hx.1 hz.1]
  suffices Hg : (∫ u in Ioi (0:ℝ), (∑' n, F n u)) = ∫ u in Ioi (0:ℝ), (pulse A i u - f u) by rwa [← Hg]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_); dsimp only [f,pulse]
  let M := Z.missed A u; let V := Z.visit A u; let L := Lens.full A u
  have hy := (mem_Ioi.mp hu).le
  have hr' := Double.into_rate (h.ticket Z p hy hr) p.margin_pos.le
  have hp := Z.rebuilds (h.paid p) hy
  have hn : L*(1+M)=V := by rw [mul_add, mul_one]; exact hp
  have hc := hasSum_nat_add_iff' 1 |>.mpr (build_right _ _ hn hr'.1 (by have h₁ := p.window_pos r; positivity) (lt_of_le_of_lt (div_le_self (p.window_pos _).le (by linarith)) hl) i i)
  change (∑' n : ℕ, - (V*(-M)^(n+1)) i i) = _ - L i i-(_ - V i i)
  simpa using hc.neg.tsum_eq

lemma anchored (ht : Timing p r) (i : ι) :
    Panel.priceLine A p.high i = Z.localLine A p.high i +
      ∑' n, ∫ u in Ioi (0:ℝ), Z.beadPulse A n i i u := by rw [(h.chains Z p hr ht i).tsum_eq]; abel

/-- Absolute truncation error AFTER the listed local costs, in u-integral
norms. Holds even on all off-diagonal entries (not only their traces). -/
lemma tails (ht : Timing p r) (i j : ι) (b : ℕ) :
    let f := fun n : ℕ => ∫ u in Ioi (0:ℝ), |Z.beadPulse A (n+b) i j u|
    Summable f ∧ ∑' n,f n ≤ p.payment * p.windowCost r ^ (b+1) / (1-p.windowCost r) := by
  intro f; let r' := p.windowCost r
  have he := (((hasSum_geometric_of_lt_one (p.window_pos r).le (lt_trans ht.misses (by norm_num))).mul_right
    (r' ^ (b+1))).mul_left p.payment)
  have hv (n : ℕ) : f n ≤ p.payment * (r'^n * r'^(b+1)) := by
    rw [← pow_add,← Nat.add_assoc]; exact (h.beads_integral Z p hr _ _).2
  have hx := he.summable.of_nonneg_of_le (fun n => integral_nonneg (fun u => abs_nonneg _)) hv
  refine ⟨hx,(hx.tsum_le_tsum hv he.summable).trans_eq (he.tsum_eq.trans ?_)⟩; unfold r'; ring

lemma first_bound (ht : Timing p r) (i : ι) :
    |Panel.priceLine A p.high i-Z.localLine A p.high i| ≤
      p.payment * p.windowCost r/(1-p.windowCost r) := by
  rw [← (h.chains Z p hr ht i).tsum_eq]; let D := fun n : ℕ => ∫ u in Ioi (0:ℝ), Z.beadPulse A n i i u
  obtain ⟨hs,hz⟩ := h.tails Z p hr ht i i 0
  simp only [Nat.add_zero, Nat.zero_add,pow_one] at hs hz
  have he (n : ℕ) : ‖D n‖ ≤ ∫ u in Ioi (0:ℝ), |Z.beadPulse A n i i u| := norm_integral_le_integral_norm _
  have hg := hs.of_nonneg_of_le (fun n => norm_nonneg _) he
  exact (norm_tsum_le_tsum_norm hg).trans ((hg.tsum_le_tsum he hs).trans hz)

end RawPrice
end YM.Further.GaussianScalar
