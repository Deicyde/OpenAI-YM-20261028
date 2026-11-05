import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Neumann
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pulse

/-!
# Local + exponential chain sums of both log-determinants

Integral convention (Jacobi fixed interpolation). Write `log|det(...)|`
also on F defects, justified invertible throughout. `first=0` arm count
includes actual S. For use in product branches h label attendance split
the raw summed powers into ordered BOND components; note no volume prefactor
estimated as though per hit. Defect/determinant letters keep all color indices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Pulse
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c : Side} {ι : Type*} {a : ι→Site c} {B m : ℕ} (D : Window a B) [DecidableEq ι] [Fintype ι]
variable (A : Matrix ι ι ℝ) {η Q r : ℝ} (hp : Torch η r Q) (h : Allow A a m η r Q)

/-- Full vs principal. Summed at one color index, to combine later. -/
def intensity (x : ℝ) (s : ℕ) := (A-1)*(D.pad (glide A x)*(-D.error (glide A x))^s)
def lact (i : ι) (n : ℕ) := ∫ x in (0:ℝ)..1, intensity D A x n i i
def localBase (i : ι) := lact D A i 0

def coil (i : ι) := ∫ x in (0:ℝ)..1, ((A-1)*(glide A x)⁻¹) i i

section
include hp h
lemma energy_all (i : ι) (hd : scraps η r Q m B < 1) : HasSum (lact D A i) (coil A i) := by
  let K := retain η r Q; let R := scraps η r Q m B
  let S := payE η r Q m; let U := Set.uIcc (0:ℝ) 1
  have hE : 0≤R := h.heap B
  let X : ℕ→ℝ := fun n => (Q+1)*(S*R^n)
  have hk : Summable X := ((summable_geometric_of_lt_one hE hd).mul_left S).mul_left _
  have he := vibrate D A h hp
  have hQ := h.weather.1
  refine up_integral X hk (fun n t => intensity D A t n i i) ?_ ?_ (fun x => ((A-1)*(glide A x)⁻¹) i i) ?_
  · have ht : ContinuousOn (fun s => D.error (glide A s)) U := ContinuousOn.sub
      ((strung A).continuousOn.mul he) continuousOn_const
    intro n; exact continuousOn_pi.mp (continuousOn_pi.mp (show ContinuousOn
      (fun x=>intensity D A x n) U from ContinuousOn.mul continuousOn_const (he.mul (ht.neg.pow n))) i) i
  · intro x t ht
    have hl := h.glide hp.hv hp.hQ t ht
    have hZ := hl.discrepancy D
    have hv : Price a a (A-1) K (Q+1) := by rw [sub_eq_add_neg]; exact paid_add h.relented (spent_neg (one_pay ..))
    have hy := h.disc
    have hs : Price a a (D.pad (glide A t)*(-D.error (glide A t))^x) K (S*R^x) :=
      paid_mul (increase (hl.primal D) (by unfold K; linarith) le_rfl) (raising (spent_neg hZ) hE hQ.le x) hQ.le hy (by positivity)
    exact only_price ((paid_mul hv hs hQ.le (by have h:=hp.hQ; linarith) (by unfold S; positivity)).1) hQ.le i i
  intro s hs
  have h₁ := (h.glide hp.hv hp.hQ s hs).discrepancy D
  have hx := stitch h₁ hE hQ.le hd (show glide A s*D.pad (glide A s)-1=D.error _ from rfl)
  exact Pi.hasSum.mp ((Pi.hasSum.mp (hx.mul_left (A-1))) i) i

lemma nofirst (i : ι) (hd : scraps η r Q m B<1) :
    HasSum (fun n : ℕ => lact D A i (n+1)) (coil A i-localBase D A i) := by
  have he := energy_all D A hp h i hd
  have hv : coil A i-localBase D A i=∑' n : ℕ, lact D A i (n+1) := by
    have hh := (he.summable.sum_add_tsum_nat_add 1).trans he.tsum_eq
    rw [sum_range_one] at hh; rw [← hh]; unfold localBase; abel
  rw [hv]; exact ((summable_nat_add_iff 1).2 he.summable).hasSum

lemma clustered : Real.log A.det = ∑ i, coil A i := by
  let M s := glide A s
  let U := Set.uIcc (0:ℝ) 1
  have hf (s) (hs : s∈Set.Icc (0:ℝ) 1) := Matrix.isUnit_det_of_right_inverse ((h.glide hp.hv hp.hQ s hs).initial.1)
  have ht : ContinuousOn (fun s => (A-1)*(M s)⁻¹) U := ContinuousOn.mul continuousOn_const (flowing U
    (strung A) (fun s hs => hf s (by unfold U at hs; rwa [Set.uIcc_of_le zero_le_one] at hs)))
  rw [total A hf]; unfold coil
  change (∫ s in (0:ℝ)..1, ∑ i : ι, ((A-1)*(M s)⁻¹) i i ) = _
  exact intervalIntegral.integral_finsetSum (f:=fun i s => ((A-1)*(M s)⁻¹) i i) fun i _ =>
    (continuousOn_pi.mp (continuousOn_pi.mp ht i) i).intervalIntegrable
end

section corr

def note (E : Matrix ι ι ℝ) (s : ℝ) (n : ℕ) := E*(-(s • E))^n

def tick (E : Matrix ι ι ℝ) (i : ι) (n : ℕ) := ∫ x in (0:ℝ)..1, note E x n i i

lemma defect {E : Matrix ι ι ℝ} (h : Price a a E η Q) (hr : 0 ≤ Q) (he : 0≤η) (hg : Q<1) :
    HasSum (fun n => ∑ i, tick E i n) (Real.log (1+E).det) := by
  let P := 1+E
  have hp : P-1=E := by unfold P; abel
  have hz s : glide P s=1- -(s • E) := by rw [glide,hp]; abel
  have hs (s : ℝ) (hh : s∈Set.Icc (0:ℝ) 1) : Price a a (-(s • E)) η Q := by
    refine spent_neg (increase (weighted_by h s) le_rfl ?_); rw [abs_of_nonneg hh.1]; exact mul_le_of_le_one_left hr hh.2
  have hu s (hh : s ∈ Set.Icc (0:ℝ) 1) : IsUnit (glide P s).det := by rw [hz]; exact (involves (hs s hh) hr he hg).1
  let f s := E*(glide P s)⁻¹
  have he' : ContinuousOn f (Set.uIcc (0:ℝ) 1) := ContinuousOn.mul continuousOn_const (flowing _ (strung P)
    (fun s h => hu s (Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num) ▸ h)))
  let F (i : ι) := ∫ s in (0:ℝ)..1, f s i i
  rw [total P hu,hp,show (∫ s in (0:ℝ)..1, trace (E*(glide P s)⁻¹))=∑ i, F i from
    intervalIntegral.integral_finsetSum (f:=fun i s => f s i i)
      fun i _ => (continuousOn_pi.mp (continuousOn_pi.mp he' i) i).intervalIntegrable]
  refine hasSum_sum (fun i _ => ?_); let K (n : ℕ) := Q*Q^n
  refine up_integral K ((summable_geometric_of_lt_one hr hg).mul_left Q)
    (fun n s => note E s n i i) ?_ ?_ (fun s => f s i i) ?_
  · intro n
    have h : Continuous (fun s => note E s n) := by unfold note; fun_prop
    exact continuousOn_pi.mp (continuousOn_pi.mp h.continuousOn i) i
  · intro x y hy
    have hv := paid_mul h (raising (hs y hy) hr he x) he hr (pow_nonneg hr _)
    exact only_price hv.1 he i i
  intro y hy
  have hv := ((involves (hs y hy) hr he hg).2).mul_left E
  rw [← hz] at hv; exact Pi.hasSum.mp (Pi.hasSum.mp hv i) i

include hp h in
lemma records_C (hs : Q*distPay η r Q m B<1) (H : PosDef (D.frameMean A)) :
    HasSum (fun n => ∑ i, tick (D.flawed A) i n) (Real.log A.det + Real.log (D.frameMean A).det) := by
  have h' := defect (h.flank D) (mul_nonneg h.fuel.le (mul_nonneg h.disc (h.heap B))) hp.prices.le hs
  have hx := (Control.definite h.symmetry h.ground hp.spans).det_pos
  rw [show 1+D.flawed A=A*D.frameMean A by unfold flawed; abel, Matrix.det_mul,Real.log_mul hx.ne' H.det_pos.ne'] at h'
  exact h'
end corr
end YM.ConnectedActivityE6.Pulse
