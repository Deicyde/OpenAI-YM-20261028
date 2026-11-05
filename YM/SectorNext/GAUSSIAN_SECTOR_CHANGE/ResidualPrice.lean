import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Signal
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Post
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Quantitative window determinant and quadratic corrections

Stay on real prices.

Log determinant
bound of A*C (doesn't compare determinant of A to A-flat or certify
trace-log series).

Per-site exponentially small also INCLUDING all active
(or zero completed) positions.

From both row and column prices. z quadratic
correction bound in actual counting coords; no probe power cost here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.ResidualPrice
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian Rows Finset
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented 
open Wisps Tier Schur LocalJet 
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section numeric
variable {n : Type} [Fintype n] [DecidableEq n]

def flared (C : ℝ) (A : Gaussian.Table n) := ∀ j, ∑ i, |A i j| ≤ C

lemma det_pay {C : ℝ} {Q : Gaussian.Table n} (h : flared C Q) : |det Q| ≤ C ^ Fintype.card n := by
  let f (p : n → n) := ∏ i, |Q (p i) i|
  have he (p : Equiv.Perm n) : |Equiv.Perm.sign p • ∏ i, Q (p i) i| = f p := by
    rw [Units.smul_def]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hi|hi <;> simp [hi,f,Finset.abs_prod]
  calc
    _ ≤ ∑ p : Equiv.Perm n,f p := by rw [det_apply]; exact (abs_sum_le_sum_abs ..).trans_eq (sum_congr rfl fun i _ => he i)
    _ ≤ ∑ p : n → n,f p := by
      have hs : Injective ((↑) : Equiv.Perm n → (n→n)) := fun _ _ e => Equiv.ext (congr_fun e)
      rw [← sum_image (g:=((↑) : Equiv.Perm n→_)) (f:=f) hs.injOn]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => prod_nonneg fun _ _ => abs_nonneg _
    _ = ∏ i, ∑ j, |Q j i| := (Fintype.prod_sum (fun i j=>|Q j i|)).symm
    _ ≤ _ := by
      have ht : C ^ Fintype.card n = ∏ _i : n, C := by simp
      rw [ht]; exact prod_le_prod (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (fun i _ => h i)

private def width (a : Vec n) := ∑ i, |a i|
private lemma moves {A : Gaussian.Table n} {C : ℝ} (h : flared C A) (v : Vec n) : width (A *ᵥ v) ≤ C * width v := by
  calc
    _ ≤ ∑ i, ∑ j, |A i j * v j| := sum_le_sum fun i _ => abs_sum_le_sum_abs ..
    _ = ∑ j, (∑ i, |A i j|) * |v j| := by rw [sum_comm]; simp_rw [abs_mul,← sum_mul]
    _ ≤ _ := by unfold width; rw [mul_sum]; exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (abs_nonneg _)

private lemma precise {Q A : Gaussian.Table n} {δ : ℝ} (h : flared δ Q) (hd : det A≠0) (he : δ≤1/2)
    (hA : A=1+Q) : flared (1+2*δ) A⁻¹ := by
  let L := A⁻¹
  have hx := A.mul_nonsing_inv (IsUnit.mk0 _ hd)
  intro j
  let b : Vec n := Pi.single j (1:ℝ)
  have hp : width b = 1 := by unfold width b; simp [Pi.single_apply,apply_ite abs]
  have hL : L *ᵥ b = fun i => L i j := Matrix.mulVec_single_one ..
  let v := L *ᵥ b
  have ht : A*ᵥ v = b := by unfold v L; rw [mulVec_mulVec,hx,one_mulVec]
  have hz : v=b-Q *ᵥ v := by rw [hA,add_mulVec,one_mulVec] at ht; rw [← ht]; abel
  change width (fun i => L i j) ≤ _
  rw [← hL]; change width v ≤ _
  have hu : width v ≤ 1+δ*width v := calc
    _ ≤ width b + width (Q*ᵥ v) := by
      conv_lhs => rw [hz]
      unfold width; rw [← sum_add_distrib]; exact sum_le_sum fun i _ => abs_sub ..
    _ ≤ _ := add_le_add hp.le (moves h v)
  have hn : 0≤width v := sum_nonneg fun _ _ => abs_nonneg _
  have hr : 0≤δ := (sum_nonneg (s:=Finset.univ) (f:= fun i=>|Q i j|) fun _ _ => abs_nonneg _).trans (h j)
  have hh : width v ≤ 2 := by nlinarith
  nlinarith

lemma local_log {Q A : Gaussian.Table n} {δ : ℝ} (h : flared δ Q) (hA : A=1+Q)
    (hd : 0<det A) (hδ : 0≤δ) (he : δ≤1/2) :
    |Real.log (Matrix.det A)| ≤ (Fintype.card n:ℝ)*(2*δ) := by
  let N : ℝ := Fintype.card n
  have hN : 0≤N := by unfold N; exact Nat.cast_nonneg _
  have hi {A : Gaussian.Table n} {x : ℝ} (h : 0≤x) (hs : 0<det A) (hv : flared (1+x) A) : Real.log (det A) ≤ N*x := by
    calc
      _ ≤ Real.log ((1+x)^Fintype.card n) := Real.log_le_log hs ((le_abs_self _).trans (det_pay hv))
      _ ≤ _ := by
        rw [Real.log_pow]; apply mul_le_mul_of_nonneg_left ?_ hN
        have he := Real.log_le_sub_one_of_pos (by linarith : 0<1+x); linarith
  have hr : flared (1+δ) A := fun j => by
    rw [hA]
    calc
      _ ≤ ∑ i, (|(1:Gaussian.Table n) i j|+|Q i j|) := sum_le_sum fun _ _ => abs_add_le ..
      _ ≤ _ := by
        simp_rw [sum_add_distrib, Matrix.one_apply,apply_ite abs]
        simp [h j]
  have ht := hi (x:=2*δ) (by positivity) (A:=A⁻¹) (show 0< Matrix.det (A⁻¹) by rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]; positivity) (precise h hd.ne' he hA)
  rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,Real.log_inv] at ht
  change |Real.log (Matrix.det A)| ≤ N*(2*δ)
  rw [abs_le]
  constructor
  · linarith
  exact (hi hδ hd hr).trans (by gcongr; linarith)

/-- If moreover A,S,C stems give invertible products, `C⁻¹-A` has entry
budget O(epsilon*A). No positivity assumptions on pure math version. -/
lemma inverse_correct {S A C : Gaussian.Table n} {δ K : ℝ} {c} {p : n → Site c}
    (hS : S=A*C-1) (h : Pours S p p 0 δ) (ha : Pours A p p 0 K)
    (hA : A.PosDef) (hC : C.PosDef) (hs : δ≤1/2) :
    Pours (C⁻¹-A) p p 0 ((1+2*δ)*(δ*K)) := by
  let T := (A*C)
  have hd : 0 < T.det := by unfold T; rw [Matrix.det_mul]; exact mul_pos hA.det_pos hC.det_pos
  have he : IsUnit A.det := IsUnit.mk0 _ hA.det_pos.ne'
  have hx p := h.col p
  simp_rw [rate, zero_mul,Real.exp_zero,one_mul] at hx
  have hl p := h.row p
  simp_rw [rate,zero_mul,Real.exp_zero,one_mul] at hl
  have hu := precise hx hd.ne' hs (show T=1+S by rw [hS]; unfold T; abel)
  have ht : flared δ S.transpose := hl
  have hm := precise ht (A:=T.transpose) (by rw [Matrix.det_transpose]; exact hd.ne') hs
    (by rw [hS,transpose_sub, transpose_one]; unfold T; abel)
  rw [← Matrix.transpose_nonsing_inv] at hm 
  have hg : Pours T⁻¹ p p 0 (1+2*δ) := by
    constructor
    · have ht := h.pos; positivity
    · intro i; simp_rw [rate,zero_mul,Real.exp_zero,one_mul]; exact hm i
    intro j; simp_rw [rate,zero_mul,Real.exp_zero,one_mul]; exact hu j
  have hv := (hg.fuse (h.fuse ha (by rfl)) (by rfl)).scale (-1)
  have hy : C⁻¹-A=(-1:ℝ) • (T⁻¹*(S*A)) := by
    have h1 : -(T⁻¹*(S*A))=(-1:ℝ) • (T⁻¹*(S*A)) := by simp
    unfold T at *
    rw [← h1,hS,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_sub, ← Matrix.mul_assoc _ _ A,
      Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hd.ne'),Matrix.one_mul, Matrix.mul_inv_rev,Matrix.mul_assoc,
      A.nonsing_inv_mul he,Matrix.mul_one,neg_sub]
  rw [hy]; simpa using hv
end numeric
section physical
variable (G : Gauge) (P : Patch) (T : Teller G)

/-- Post-L residual quadratic and one of the *two* log terms in Fsct (the
C vs A^-1 part). TRUE covariance/window and A from the actual affvd.
No unmarked path hypotheses beyond Teller's. This does not price A vs Aflat
in the same exponentially improving cost (holes not small, differently
paired addresses, different matrix dimensions; see Campaign). Nor η correction
which would need quantitative Y source/mean-window comparisons. -/
lemma paid_kernel (h : P.Branches T.bind G) : ∃ u E : ℝ, 0<u ∧ 0<E ∧ ∀ᶠ x : ℝ in atTop,
    let K := E*Real.exp (-u * (radiusB x))
    ∀ {c f : Side} (S : StepData c f) (B : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val →
      T.Funds S B → ∀ (A : Stores S) (F : Forest S.ratio) (k:S.Choices) (V : Config G c),
      A.flags=RG.flags (temp x) V →
      let C := fog A F B x V k; let Q := Rows.gram B x V k (shots S x) A F
      |Real.log (det (1+(Q*C-1)))| ≤ Fintype.card (In x A F (G:=G))*K ∧
      Schur.Pours (C⁻¹-Q) (front A F) (front A F) 0 K ∧
        ∀ z : Prices G (Active A x F), |z ⬝ᵥ ((C⁻¹-Q) *ᵥ z)| ≤ K*∑ i, ‖tape z i‖^2 := by
  obtain ⟨v,k,η,b,E,hv,hk,hη,hb,hE,H⟩ := opaqueCost G P T h
  let u := b/120
  have hu : 0<u := by unfold u; positivity
  let M := max 1 k
  have hm : 0 < M := by unfold M; positivity
  let D := 2*M*M*E
  have hD : 0<D := by unfold D; positivity
  have ht : Tendsto (fun x => k*(E * Real.exp (-u*(radiusB x)))) atTop (𝓝 0) := by
    have hi : Tendsto (fun x => Real.exp (-u*(radiusB x))) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp
      ((tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp Work.E01.radiusB_tendsto) |>.const_mul_atTop_of_neg (neg_lt_zero.mpr hu))
    simpa only [mul_zero] using (hi.const_mul E).const_mul k
  refine ⟨u,D,hu,hD,?_⟩
  filter_upwards [H,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)), Work.E01.radiusB_tendsto.eventually_ge_atTop 120] with x hx hT he
  intro K c f S B hs hl hp A F i V hA C Q
  obtain ⟨hr,hQ,hQ',hR,hC⟩ := hx S B hs hl hp A F i V hA
  let r := E*rate (-b) (radiusB x/60)
  have hy : Schur.Pours (Q*C-1) (front A F) (front A F) 0 (k*r) := by
    have hx : Q*C-1=Q*(C-Q⁻¹) := by
      rw [Matrix.mul_sub, Matrix.mul_nonsing_inv]
      exact (Q.isUnit_iff_isUnit_det).mp hQ'.isUnit
    rw [hx]; exact (hr.weaker hv.le le_rfl).fuse hR le_rfl
  have hm' := le_max_right 1 k; have he' := le_max_left 1 k
  let s := E*Real.exp (-u * radiusB x)
  have hw : r ≤ s := by
    have hf : radiusB x ≤ 120*(radiusB x/60) := by omega
    unfold r s rate; apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) hE.le
    unfold u; have hi : (radiusB x:ℝ) ≤ 120*((radiusB x/60:ℕ):ℝ) := by exact_mod_cast hf
    nlinarith
  have ht : k*r ≤ 1/2 := (mul_le_mul_of_nonneg_left hw hk).trans hT.le
  have h' j := hy.col j
  simp_rw [rate,zero_mul,Real.exp_zero,one_mul] at h'
  have hf := inverse_correct rfl hy (hr.weaker hv.le le_rfl) hQ' hC ht
  have hy' : 0 ≤ r := by unfold r rate; positivity
  have hm' : k≤M := hm'
  have he' : 1≤M := he'
  have hh : 2*(k*r) ≤ 2*M*s := by
    calc
      _ ≤ 2*(M*s) := by gcongr
      _ = _ := by ring
  have hN : 0 ≤ s := by unfold s; positivity
  have hL : K = 2*M*M*s := by unfold K D s; ring
  have h2 : Schur.Pours (C⁻¹-Q) (front A F) (front A F) 0 K := by
    refine hf.weaker le_rfl ?_
    rw [hL]
    calc
      _ ≤ 2*((k*r)*k) := by gcongr; linarith
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hh hk, mul_le_mul_of_nonneg_left hm' (mul_nonneg (by linarith only [hm] : 0≤2*M) hN)]
  refine ⟨?_,h2,fun z => ?_⟩
  · apply (local_log h' rfl (by rw [show (1+(Q*C-1))=Q*C by abel,Matrix.det_mul]; exact mul_pos hQ'.det_pos hC.det_pos) hy.pos ht).trans
    gcongr
    rw [hL]; apply hh.trans; nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he' hm.le) hN]
  have h₁ := Schur.estimate h2 z z
  rw [Schur.sumSq_dot,price_square] at h₁
  linarith
end physical
end YM.Next.SectorChange.ResidualPrice
