import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Walls
import YM.Next.FREE_KERNELS.Lifts
import YM.SectorNext.VACUUM_NORMALIZATION.Round


/-!
# E log determinant chain identities (trace before unwinding into labels)
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Filter Function Set Matrix Unitary MeasureTheory
open Next.SectorChange FreeResolvent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {ι : Type} {X : Type*} [Fintype ι] [DecidableEq ι] {W : ι → Set ι} {u : ℝ} {A : Square ι}

lemma resolve_cont (hA : A.PosDef) (hu : 0 ≤ u) : ContinuousAt (resolve A) u := by
  refine ContinuousAt.comp (f:=fun v => A+v • 1) (g:=Inv.inv) ?_ (continuousAt_const.add (continuousAt_id.smul continuousAt_const))
  apply continuousAt_matrix_inv; rw [show Ring.inverse = fun x : ℝ => x⁻¹ from funext Ring.inverse_eq_inv]
  exact continuousAt_inv₀ (shift_posDef hA hu).det_pos.ne'
lemma pie_entry_cont (hA : A.PosDef) (h : ∀ i, i∈W i) (hu : 0 ≤ u) (i j) : ContinuousAt (fun x => pie W A x i j) u := by
  by_cases he : i∈W j
  · simp_rw [pie_read W _ _ _ _ he (h j)]
    exact ((continuous_id (X:=Square ↑(W j))).matrix_elem _ _).continuousAt.comp (resolve_cont
      (hA.submatrix Subtype.val_injective) hu)
  simp_rw [pie_miss W _ _ _ _ he]; exact continuousAt_const
lemma pie_cont (hA : A.PosDef) (h : ∀ i, i∈W i) (hu : 0 ≤ u) : ContinuousAt (pie W A) u := by
  apply continuousAt_pi.mpr; intro i; exact continuousAt_pi.mpr fun j => pie_entry_cont hA h hu i j
lemma defect_cont (hA : A.PosDef) (h : ∀ i, i∈W i) (hu : 0 ≤ u) : ContinuousAt (defect W A) u :=
  ((continuousAt_const.add (continuousAt_id.smul continuousAt_const)).mul (pie_cont hA h hu)).sub continuousAt_const

lemma integral_price {C : ℝ} {f : ℝ → ℝ}
    (h : ContinuousOn f (Ioi 0)) (hp : ∀ u ∈ Ioi 0, |f u| ≤ C * attenuation u ^ 2) :
    IntegrableOn f (Ioi 0) ∧ (∫ u in Ioi 0, |f u|) ≤ C ∧ |∫ u in Ioi 0, f u| ≤ C := by
  have hh : ∀ᵐ u ∂(Measure.restrict volume (Ioi 0)), ‖f u‖ ≤ C*attenuation u ^ 2 :=
    (ae_restrict_mem measurableSet_Ioi).mono fun u hu => hp u hu
  have hx := attenuation_square.1.const_mul C
  have he : IntegrableOn f (Ioi 0) := hx.mono' (h.aestronglyMeasurable measurableSet_Ioi) hh
  have ht : (∫ u in Ioi 0, |f u|) ≤ C := (integral_mono_ae he.norm hx hh).trans_eq (by
    rw [integral_const_mul, attenuation_square.2, mul_one])
  exact ⟨he,ht,abs_integral_le_integral_abs.trans ht⟩

/-- Genuine single-window log entry. -/
def letterBase (W : ι → Set ι) (A : Square ι) (i : ι) :=
  ∫ u in Ioi 0, attenuation u-pie W A u i i

lemma base_log (hw : ∀ i, i ∈ W i) (A : Square ι) (i : ι) :
    let j : W i:= ⟨i,hw i⟩
    letterBase W A i=logKernel (Schur.principal A (W i)) j j := by
  intro j
  unfold letterBase logKernel density
  simp_rw [pie_read W A _ _ _ (hw i) (hw i),of_apply,Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  -- definitional
  rfl

lemma density_base (hu : ℝ) (i : ι) (W : ι → Set ι) (A : Square ι) :
    density A hu i i=(attenuation hu-pie W A hu i i)+(pie W A hu-resolve A hu) i i := by
  unfold density
  rw [Matrix.sub_apply, Matrix.sub_apply,Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,mul_one]; ring

/-- begins at n+1 E factors, n=0 first nonlocal contribution. Includes sign
for `log A`. -/
def term (W : ι → Set ι) (A : Square ι) (i : ι) (n : ℕ) (u : ℝ) :=
  - ((pie W A u)*(-defect W A u)^(n+1)) i i

section bounds
variable {D : Cost X} {p : ι → X} {σ C q : ℝ}

namespace Priced

variable (b : Priced D p W A σ C q)
include b
lemma regular_price (i : ι) :
    IntegrableOn (fun u => attenuation u - pie W A u i i) (Ioi 0) ∧ |letterBase W A i| ≤ (C+1)*C := by
  suffices he : ∀ u ∈ Ioi 0, |attenuation u-pie W A u i i| ≤ ((C+1)*C)*attenuation u^2 by
    have h u (hu : u∈Ioi (0:ℝ)) : ContinuousAt (fun u => attenuation u - pie W A u i i) u :=
      ((continuousAt_const.add continuousAt_id).inv₀ (ne_of_gt (by have := hu.out; change 0<1+u; linarith))).sub
        (pie_entry_cont b.gram b.root hu.out.le i i)
    obtain ⟨ht,-,hx⟩ := integral_price (fun x hx => (h x hx).continuousWithinAt) he
    exact ⟨ht,hx⟩
  intro u hu
  have he := defect_zero W u b.root (A:=A) (fun i => IsUnit.mk0 _ (shift_posDef (b.gram.submatrix Subtype.val_injective) hu.out.le).det_pos.ne') (b.root i)
  let P:=pie W A u
  have hh : (A*P) i i + u*P i i = 1 := by
    apply sub_eq_zero.mp
    unfold defect at he
    simpa only [Matrix.add_mul, Matrix.sub_apply,Matrix.add_apply,Matrix.smul_mul,Matrix.smul_apply, Matrix.one_mul, Matrix.one_apply_eq, smul_eq_mul, P] using he
  have hp : 0 < 1+u := by have := hu.out; linarith
  have hx := attenuation_pos hu.out.le
  have hm : 0 ≤ C := zero_le_one.trans b.paid
  have hv := (((b.kernel.sub Cost.Schur.one).mul (b.columns u hu.out.le) b.rate (by linarith) (by positivity)).rows.weighted i i)
  rw [D.weight_self, one_mul] at hv
  rw [show attenuation u - pie W A u i i=attenuation u * ((A-1)*pie W A u) i i from ?_, abs_mul, abs_of_pos hx]
  · exact (mul_le_mul_of_nonneg_left hv hx.le).trans_eq (by ring)
  unfold attenuation
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply]
  field_simp
  unfold P at hh
  linarith only [hh]

lemma pie_schur_distance (hu : 0 ≤ u) : D.Schur p p σ (C*q*attenuation u^2) (pie W A u-resolve A u) := by
  have hg : pie W A u-resolve A u=resolve A u*defect W A u := by
    rw [defect_survey _ _ _ b.root, pie_inspects W _ _ b.root]
    exact (study W b.root).replacement _ _ (IsUnit.mk0 _ (shift_posDef b.gram hu).det_pos.ne')
  have hv := b.shift u hu
  have he := attenuation_pos hu
  have hm : 0 ≤ C := zero_le_one.trans b.paid
  rw [hg]; exact ((b.inverse u hu).mul hv b.rate (by positivity) (mul_nonneg b.coupon he.le)).mono le_rfl (Eq.le (by ring))

lemma pie_log_distance (i : ι) :
    let f u := (pie W A u-resolve A u) i i
    IntegrableOn f (Ioi 0) ∧ (∫ u in Ioi 0, f u)= logKernel A i i - letterBase W A i ∧
      |logKernel A i i - letterBase W A i| ≤ C*q := by
  intro f
  have hf u (hu : u∈Ioi (0:ℝ)) := ((b.pie_schur_distance hu.out.le).rows.weighted i i)
  simp_rw [Cost.weight_self, one_mul] at hf
  obtain ⟨he,-,hh⟩ := integral_price (f:=f) (fun u hu =>
    (((continuous_id (X:=Square ι)).matrix_elem i i).continuousAt.comp
      ((pie_cont b.gram b.root hu.out.le).sub (resolve_cont b.gram hu.out.le))).continuousWithinAt) hf
  have hs : logKernel A i i = letterBase W A i + ∫ u in Ioi 0,f u := by
    rw [logKernel, of_apply]
    simp_rw [density_base _ _ W A]; exact integral_add (b.regular_price i).1 he
  rw [hs,add_sub_cancel_left]; exact ⟨he,rfl,hh⟩

omit b in
lemma schur_power {T : Square ι} (h : D.Schur p p σ q T) (hs : 0 ≤ σ) (hq : 0 ≤ q) (k : ℕ) :
    D.Schur p p σ (q^k) (T^k) := by
  induction k with
  | zero => simp only [pow_zero]; exact Cost.Schur.one
  | succ k ih => rw [pow_succ,pow_succ]; exact ih.mul h hs (by positivity) hq

lemma inverse_series (hq : q<1) (hu : 0≤u) :
    HasSum (fun n : ℕ => (pie W A u)*(-defect W A u)^n) (resolve A u) := by
  let E := -defect W A u; let P:=pie W A u
  have hp : D.Schur p p 0 q E := (b.shift u hu).neg.mono b.rate (mul_le_of_le_one_right b.coupon (attenuation_le hu))
  have he (n : ℕ) := schur_power hp le_rfl b.coupon n
  have hv : Summable (fun n : ℕ => E^n) := by
    apply Pi.summable.mpr
    intro i; apply Pi.summable.mpr; intro j
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one b.coupon hq) fun n => ?_
    have ht := (he n).rows.weighted i j
    rw [D.weight_zero, one_mul] at ht
    exact ht
  let H := ∑' n : ℕ, E^n
  have hg : (A+u • 1)*P=1-E := by unfold P E defect; abel
  have hh : resolve A u = P*H := Matrix.inv_eq_right_inv (by
    rw [← Matrix.mul_assoc,hg]; exact hv.one_sub_mul_tsum_pow)
  rw [hh]
  exact hv.hasSum.mul_left P

lemma term_cont (i : ι) (n : ℕ) (hu : 0 ≤ u) : ContinuousAt (term W A i n) u :=
  (((continuous_id (X:=Square ι)).matrix_elem _ _).continuousAt.comp
    ((pie_cont b.gram b.root hu).mul ((defect_cont b.gram b.root hu).neg.pow (n+1)))).neg

lemma term_cost (i : ι) (n : ℕ) :
    IntegrableOn (term W A i n) (Ioi 0) ∧ (∫ u in Ioi 0, |term W A i n u|) ≤ C*q^(n+1) := by
  suffices hp : ∀ u ∈ Ioi 0, |term W A i n u| ≤ C*q^(n+1)*attenuation u^2 by
    obtain ⟨hr,h,-⟩ := integral_price (fun u hu => (b.term_cont i n hu.out.le).continuousWithinAt) hp
    exact ⟨hr,h⟩
  intro u hu
  have ht := b.shift u hu.out.le
  have hq := b.coupon
  have hv := attenuation_pos hu.out.le
  have hC : 0<C := lt_of_lt_of_le zero_lt_one b.paid
  have hp := schur_power ht.neg b.rate (by positivity) (n+1)
  have h := ((b.columns u hu.out.le).mul hp b.rate (by positivity) (by positivity)).rows.weighted i i
  rw [D.weight_self,one_mul] at h
  unfold term; rw [abs_neg]; apply h.trans
  have hL : (attenuation u)^(n+1) ≤ attenuation u := by
    rw [pow_succ]
    exact mul_le_of_le_one_left hv.le (pow_le_one₀ hv.le (attenuation_le hu.out.le))
  calc
    C*attenuation u*(q*attenuation u)^(n+1) ≤ C*attenuation u*(q^(n+1)*attenuation u) := by rw [mul_pow]; gcongr
    _ = _ := by ring

lemma resolvent_tail (hq : q<1) (hu : 0 ≤ u) (i : ι) :
    HasSum (fun n => term W A i n u) ((pie W A u-resolve A u) i i) := by
  let P:=pie W A u
  have he : HasSum (fun n : ℕ => P*(-defect W A u)^(n+1)) (resolve A u-P) := by
    have he := (hasSum_nat_add_iff' 1).mpr (b.inverse_series hq hu)
    simpa [P] using he
  have hh := he.neg
  rw [neg_sub] at hh
  -- take entries
  exact Pi.hasSum.mp (Pi.hasSum.mp hh i) i

lemma log_tail (hq : q<1) (i : ι) :
    HasSum (fun n : ℕ => ∫ u in Ioi 0, term W A i n u) (logKernel A i i-letterBase W A i) := by
  let f := term W A i
  have he := b.term_cost i
  have hp : Summable fun n : ℕ => ∫ u in Ioi 0, ‖f n u‖ := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun u => norm_nonneg _) (fun n => (he n).2)
    have ht := (((summable_geometric_of_lt_one b.coupon hq).mul_right q).mul_left C)
    simpa only [pow_succ] using ht
  have hh := hasSum_integral_of_summable_integral_norm (fun n => (he n).1) hp
  have hr := b.pie_log_distance i
  rw [← hr.2.1]
  have hf : (∫ u in Ioi 0, (pie W A u-resolve A u) i i)= ∫ u in Ioi 0, ∑' n, f n u := setIntegral_congr_fun measurableSet_Ioi fun u hu =>
    (b.resolvent_tail hq hu.out.le i).tsum_eq.symm
  rw [hf]; exact hh

open SectorNext.Vacuum in
/-- All terms with true PosDef Gram, using assembled (different
window each column!) approximation. `A*C` needn't be symmetric.
Note no missing j=0 for S: starts at 1, sign built into `ripple`.
Symmetric C's *use as covariance* requires also its positivity. -/
theorem chains (hq : q < 1) (hC : (Schur.clouded W A).PosDef) :
    let S := excess W A
    let r (i : ι) := (fun n : ℕ => ∫ u in Ioi 0, term W A i n u)
    Real.log A.det = ∑ i, (letterBase W A i + ∑' n,r i n) ∧
      Real.log (Schur.clouded W A).det = -Real.log A.det + ∑ i, (∑' n,Round.ripple S n i i) ∧
      Real.log (1+S).det = ∑ i, (∑' n,Round.ripple S n i i) ∧
      ∀ i, Summable (r i) ∧ Summable (fun n=>Round.ripple S n i i) := by
  intro S r
  have he : Round.rowRate q S := fun i => by simpa only [Cost.weight_zero,one_mul] using ((b.mix.mono b.rate le_rfl).rows.bound i)
  have ht := (Round.exact_trace b.gram hC.1 S rfl he b.coupon hq).2.2.2
  rw [Round.lines S he b.coupon hq] at ht
  have hv : Real.log (1+S).det=Real.log A.det+Real.log (Schur.clouded W A).det := by
    rw [show 1+S=A*Schur.clouded W A by unfold S excess; abel,Matrix.det_mul,
      Real.log_mul b.gram.det_pos.ne' hC.det_pos.ne']
  refine ⟨?_,?_,ht.symm,fun i => ⟨(b.log_tail hq i).summable,Round.lineSummable S he b.coupon hq i i⟩⟩
  · rw [log_trace b.gram]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(show (∑' n,r i n)=_ from (b.log_tail hq i).tsum_eq)]; abel
  change _ = -Real.log A.det + ∑ i, Round.onLine S i
  rw [ht, hv]; abel
end Priced
end bounds
end YM.AnalyticBridge.RelativeLogdet
