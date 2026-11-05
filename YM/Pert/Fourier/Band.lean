import YM.Pert.Fourier.Modes
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
/-! Rescaled finite-difference symbol. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open Lattice Function Complex BigOperators Topology Filter Set
open scoped ContDiff
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma quot_smooth {f : ℝ → Z} [CompleteSpace Z] (h : AnalyticAt ℝ f 0) (hall : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (dslope f 0) := contDiff_iff_contDiffAt.mpr fun r => by
  by_cases hr : r=0
  · subst r; obtain ⟨p,H⟩ := h; have ht := H.has_fpower_series_dslope_fslope
    exact (show AnalyticAt ℝ _ _ from ⟨p.fslope,ht⟩).contDiffAt
  have he : dslope f 0 =ᶠ[𝓝 r] fun x => x⁻¹ • (f x-f 0) := Eventually.mono (isOpen_ne_fun continuous_id continuous_const |>.mem_nhds hr) fun w hw => by
    change w ≠ 0 at hw
    rw [dslope_of_ne f hw,slope,sub_zero]; rfl
  exact ((contDiffAt_id.inv hr).smul (hall.contDiffAt.sub contDiffAt_const)).congr_of_eventuallyEq he

def phase (x : ℝ) := Complex.exp ((x:ℂ)*I)
def phaseQ (x : ℝ) := dslope phase 0 x
def sinQ (x : ℝ) := dslope Real.sin 0 x
lemma phaseQ_mul (x : ℝ) : x • phaseQ x = phase x - 1 := by simpa [phaseQ,phase] using sub_smul_dslope phase 0 x
lemma phaseQ_zero : phaseQ 0 = I := by
  have he := ((Complex.ofRealCLM.hasDerivAt (x:=0)).mul_const I).cexp
  rw [phaseQ,dslope_same]; convert! he.deriv using 1; simp
lemma sinQ_mul (x : ℝ) : x * sinQ x = Real.sin x := by simpa [sinQ] using sub_smul_dslope Real.sin 0 x
lemma sinQ_zero : sinQ 0 = 1 := by simp only [sinQ,dslope_same]; simp
lemma phaseQ_diff : ContDiff ℝ ∞ phaseQ := by
  have h : AnalyticAt ℝ phase 0 := analyticAt_cexp.restrictScalars.comp ((Complex.ofRealCLM.analyticAt 0).mul analyticAt_const)
  apply quot_smooth h (contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const))
lemma sinQ_diff : ContDiff ℝ ∞ sinQ := quot_smooth Real.analyticAt_sin Real.contDiff_sin

def numerator (t : ℝ) (k : E4) (i : Axis) := (k i : ℂ) * phaseQ (t*k i)
def latticeD (t : ℝ) (k : E4) := ∑ i, (k i * sinQ (t*k i/2))^2
def symbol (D : List Axis) (t : ℝ) (k : E4) := (latticeD t k : ℂ)⁻¹ * (D.map (numerator t k)).prod
lemma sin_sign (x : ℝ) (h : |x|<2*Real.pi) : 0 < sinQ (x/2) := by
  rcases lt_trichotomy x 0 with hx|rfl|hx
  · have h2 := Real.sin_pos_of_mem_Ioo (x:=-x/2) ⟨by linarith,by have ⟨ht,hy⟩ := abs_lt.mp h; linarith⟩
    have ht : -x/2=-(x/2) := by ring
    rw [ht,Real.sin_neg,← sinQ_mul] at h2; exact pos_of_mul_neg_right (show (x/2)*_ < 0 from neg_pos.mp h2) (le_of_lt (by linarith))
  · simp [sinQ_zero]
  have h2 := Real.sin_pos_of_mem_Ioo (x:=x/2) ⟨by linarith,by have ⟨ht,hy⟩ := abs_lt.mp h; linarith⟩
  rw [← sinQ_mul] at h2; exact pos_of_mul_pos_right h2 (by linarith)
lemma latticeD_pos {t : ℝ} {k : E4} (h : k ≠ 0) (ht : ∀ i, |t*k i|<2*Real.pi) : 0 < latticeD t k := by
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ 0 := by by_contra! ht; exact h (PiLp.ext ht)
  exact (sq_pos_of_ne_zero (mul_ne_zero hi (sin_sign _ (ht i)).ne')).trans_le (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => sq_nonneg (k j * sinQ (t*k j/2))) (Finset.mem_univ i))
lemma bd (i : Axis) : ContDiff ℝ ∞ (fun p : ℝ×E4 => p.2 i) := ((EuclideanSpace.proj i).contDiff (𝕜:=ℝ) (n:=∞)).comp (show ContDiff ℝ ∞ (Prod.snd : ℝ × E4 → E4) from contDiff_snd)
lemma symbol_diff (D : List Axis) (t : ℝ) (k : E4) (h : latticeD t k ≠ 0) : ContDiffAt ℝ ∞ (uncurry (symbol D)) (t,k) := by
  have he : ContDiff ℝ ∞ (uncurry latticeD) := by
    unfold latticeD uncurry; apply ContDiff.sum; intro i hi; exact ((bd i).mul (sinQ_diff.comp ((contDiff_fst.mul (bd i)).div_const _))).pow _
  have hn (i : Axis) : ContDiff ℝ ∞ (uncurry (fun t k => numerator t k i)) := (Complex.ofRealCLM.contDiff.comp (bd i)).mul (phaseQ_diff.comp (contDiff_fst.mul (bd i)))
  unfold symbol uncurry
  have hd := Complex.ofRealCLM.contDiff.comp he
  have hw : ContDiffAt ℝ ∞ (Complex.ofRealCLM ∘ uncurry latticeD) (t,k) := hd.contDiffAt
  apply (hw.inv (x:=(t,k)) (ofReal_ne_zero.mpr h)).mul
  induction D with
  | nil => exact contDiffAt_const
  | cons i d ih => exact (hn i).contDiffAt.mul ih

def disk : ContDiffBump (0:E4) := ⟨1/2,1,by norm_num,by norm_num⟩
def middle (D : List Axis) (t : ℝ) (k : E4) := (((disk ((1/2:ℝ) • k) - disk k):ℝ):ℂ) * symbol D t k
def last (D : List Axis) (t : ℝ) (k : E4) := (((1-disk k):ℝ):ℂ) * symbol D t k
lemma disk_one {k : E4} (h : ‖k‖≤1/2) : disk k = 1 := disk.one_of_mem_closedBall (by simpa [disk] using h)
lemma disk_out {k : E4} (h : 1 ≤ ‖k‖) : disk k = 0 := disk.zero_of_le_dist (by simpa [disk] using h)
lemma innermost {k : E4} (h : ‖k‖≤1/2) : disk ((1/2:ℝ) • k)=1 := disk_one (by rw [norm_smul,show ‖(1/2:ℝ)‖=1/2 from Real.norm_of_nonneg (by norm_num)]; linarith)
lemma outermost {k : E4} (h : 2 ≤ ‖k‖) : disk ((1/2:ℝ) • k) = 0 := disk_out (by rw [norm_smul,show ‖(1/2:ℝ)‖=1/2 from Real.norm_of_nonneg (by norm_num)]; linarith)
lemma disk_diff : ContDiff ℝ ∞ (disk ∘ fun p : ℝ×E4 => p.2) := disk.contDiff.comp contDiff_snd
lemma two_diff : ContDiff ℝ ∞ (disk ∘ fun p : ℝ×E4 => (1/2:ℝ) • p.2) := disk.contDiff.comp ((show ContDiff ℝ ∞ (fun x : ℝ×E4 => (1/2:ℝ)) from contDiff_const).smul (show ContDiff ℝ ∞ (Prod.snd : ℝ × E4 → E4) from contDiff_snd))
lemma coordinate_le (k : E4) (i : Axis) : |k i|≤‖k‖ := by simpa using abs_real_inner_le_norm (basis i) k
lemma middle_diff (D : List Axis) (t : ℝ) (ht : |t|≤1) (k : E4) : ContDiffAt ℝ ∞ (uncurry (middle D)) (t,k) := by
  by_cases hi : ‖k‖<1/2
  · have he : uncurry (middle D)=ᶠ[𝓝 (t,k)] fun _=>0 := Eventually.mono (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const |>.mem_nhds (x:=(t,k)) hi) fun y hy => by
      unfold uncurry middle; rw [innermost (k:=y.2) hy.le,disk_one (k:=y.2) hy.le]; simp
    exact contDiffAt_const.congr_of_eventuallyEq he
  by_cases ho : 2<‖k‖
  · have he : uncurry (middle D)=ᶠ[𝓝 (t,k)] fun _=>0 := Eventually.mono (isOpen_lt continuous_const (continuous_norm.comp continuous_snd) |>.mem_nhds (x:=(t,k)) ho) fun y hy => by
      unfold uncurry middle; rw [outermost (k:=y.2) hy.le,disk_out (k:=y.2) (by linarith only [show 2<‖y.2‖ from hy])]; simp
    exact contDiffAt_const.congr_of_eventuallyEq he
  unfold uncurry middle; refine (Complex.ofRealCLM.contDiff.comp (two_diff.sub disk_diff)).contDiffAt.mul (symbol_diff _ _ _ (latticeD_pos ?_ ?_).ne')
  · exact norm_pos_iff.mp (by linarith)
  intro i; rw [abs_mul]; refine lt_of_le_of_lt (mul_le_mul ht ((coordinate_le k i).trans (le_of_not_gt ho)) (abs_nonneg _) zero_le_one) ?_; have := Real.two_le_pi; linarith
lemma last_diff (D : List Axis) (t : ℝ) (k : E4) (h : ∀ i, |t*k i| < 2 * Real.pi) : ContDiffAt ℝ ∞ (uncurry (last D)) (t,k) := by
  by_cases hi : ‖k‖<1/2
  · have he : uncurry (last D)=ᶠ[𝓝 (t,k)] fun _=>0 := Eventually.mono (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const |>.mem_nhds (x:=(t,k)) hi) fun y hy => by
      unfold uncurry last; rw [disk_one (by linarith only [show ‖y.2‖<1/2 from hy])]; simp
    exact contDiffAt_const.congr_of_eventuallyEq he
  unfold last uncurry; exact (Complex.ofRealCLM.contDiff.comp (contDiff_const.sub disk_diff)).contDiffAt.mul (symbol_diff _ _ _ (latticeD_pos (norm_pos_iff.mp (by linarith)) h).ne')
end YM.Pert.Band
