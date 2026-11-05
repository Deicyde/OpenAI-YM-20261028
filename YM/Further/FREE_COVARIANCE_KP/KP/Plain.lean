import Mathlib.Analysis.Calculus.SmoothSeries
import YM.Further.FREE_COVARIANCE_KP.KP.Weight
import YM.Laurent.Eval



/-! # Smooth real-frequency price from the installed strip budgets -/

set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex Lattice Laurent
open scoped Topology ContDiff BigOperators InnerProductSpace

variable {ι : Type*} {U : Window} {S R : ℝ}

/-- Global smooth; common prices on closed ball inclusive of 0. -/
structure Plain (R : ℝ) (f : ι → E4 → ℂ) : Prop where
  smooth i : ContDiff ℝ ∞ (f i)
  quotes n : ∃ C : ℝ, 0≤C ∧ ∀ i,∀ p, ‖p‖≤R → ‖iteratedFDeriv ℝ n (f i) p‖ ≤ C

namespace Plain
variable {f g : ι → E4 → ℂ}
lemma sample (h : E4 → ℂ) (he : ContDiff ℝ ∞ h) : Plain (ι:=ι) R (fun _ => h) := by
  refine ⟨fun _ => he,fun n => ?_⟩
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E4) R).bddAbove_image ((he.continuous_iteratedFDeriv (show (n:ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (↑n:ℕ∞)≤⊤))).norm.continuousOn)
  refine ⟨max 0 C,le_max_left ..,fun i p hp => ?_⟩; exact (hC (mem_image_of_mem _ (mem_closedBall_zero_iff.mpr hp))).trans (le_max_right ..)
lemma sub (hf : Plain R f) (hg : Plain R g) : Plain R (fun i p=> f i p-g i p) := by
  refine ⟨fun i => (hf.smooth i).sub (hg.smooth i),fun n => ?_⟩
  obtain ⟨A,hA,ha⟩ := hf.quotes n; obtain ⟨B,hB,hb⟩ := hg.quotes n
  refine ⟨A+B,by positivity,fun i p hp => ?_⟩
  have he : (n:ℕ∞ω)≤∞ := by exact_mod_cast (le_top : (↑n:ℕ∞)≤⊤)
  change ‖iteratedFDeriv ℝ n (f i-g i) p‖ ≤ _
  rw [iteratedFDeriv_sub_apply ((hf.smooth i).of_le he).contDiffAt ((hg.smooth i).of_le he).contDiffAt]
  exact (norm_sub_le ..).trans (add_le_add (ha i p hp) (hb i p hp))
lemma lose_powers (hf : Plain R f) (hR : 0<R) (bound : ∀ p:E4,p∈U→‖p‖≤R) {l : ℤ} {n : ℕ} (hn : l≤(n:ℤ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ i,∀ p:E4, p∈U → ‖iteratedFDeriv ℝ n (f i) p‖ ≤ C*‖p‖^(l-n:ℤ) := by
  obtain ⟨C,hC,H⟩ := hf.quotes n
  refine ⟨C*R^(n-l:ℤ),by positivity,fun i p hp => (H i p (bound p hp)).trans ?_⟩
  have he := norm_pos_iff.mpr (U.out hp)
  rw [show l-(n:ℤ)=-(n-l:ℤ) by ring,zpow_neg,← div_eq_mul_inv,le_div_iff₀ (zpow_pos he _)]; gcongr; exact zpow_le_zpow_left₀ (by omega) he.le (bound p hp)
lemma zero_power (hf : Plain R f) (hR : 0<R) (bound : ∀ p:E4,p∈U→‖p‖≤R) : Weight U 0 f := ⟨fun i => (hf.smooth i).contDiffOn,fun n => hf.lose_powers hR bound (by omega)⟩
lemma one_power (hf : Plain R f) (hR : 0<R) (bound : ∀ p:E4,p∈U→‖p‖≤R) (ho : ∀ i, f i 0=0) : Weight U 1 f := by
  refine ⟨fun i => (hf.smooth i).contDiffOn,?_⟩
  rintro (_|n)
  · obtain ⟨A,hA,H⟩ := hf.quotes 1
    refine ⟨A,hA,fun i p hp => ?_⟩
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => (hf.smooth i).differentiable (by simp) x) (fun x hx => show ‖fderiv ℝ (f i) x‖ ≤ A from by rw [← norm_iteratedFDeriv_one]; exact H i x (mem_closedBall_zero_iff.mp hx))
        (convex_closedBall (0:E4) R) (mem_closedBall_self hR.le) (mem_closedBall_zero_iff.mpr (bound p hp))
    simpa [ho] using he
  exact hf.lose_powers hR bound (by omega)
lemma two_powers (hf : Plain R f) (hR : 0<R) (bound : ∀ p:E4,p∈U→‖p‖≤R) (ho : ∀ i, f i 0=0) (hg : ∀ i, fderiv ℝ (f i) 0=0) : Weight U 2 f := by
  obtain ⟨C,hC,H⟩ := hf.quotes 2
  have he (i : ι) (p : E4) (hp : ‖p‖≤R) : ‖fderiv ℝ (f i) p‖ ≤ C*‖p‖ := by
    have ha : ContDiff ℝ ∞ (fderiv ℝ (f i)) := (hf.smooth i).fderiv_right (by simp)
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => ha.differentiable (by simp) x) (fun x hx => show ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ C from by
        rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]; exact H i x (mem_closedBall_zero_iff.mp hx))
        (convex_closedBall (0:E4) R) (mem_closedBall_self hR.le) (mem_closedBall_zero_iff.mpr hp)
    simpa [hg] using he
  refine ⟨fun i => (hf.smooth i).contDiffOn,?_⟩
  rintro (_|_|n)
  · refine ⟨C,hC,fun i p hp => ?_⟩
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => (hf.smooth i).differentiable (by simp) x) (fun x hx => show ‖fderiv ℝ (f i) x‖≤ C*‖p‖ from by
        have hs := mem_closedBall_zero_iff.mp hx; exact (he i x (hs.trans (bound p hp))).trans (mul_le_mul_of_nonneg_left hs hC))
        (convex_closedBall (0:E4) ‖p‖) (mem_closedBall_self (norm_nonneg _)) (mem_closedBall_zero_iff.mpr le_rfl)
    rw [norm_iteratedFDeriv_zero]; simpa [ho,zpow_ofNat, pow_two,mul_assoc] using h
  · exact ⟨C,hC,fun i p hp => by rw [norm_iteratedFDeriv_one]; simpa using he i p (bound p hp)⟩
  exact hf.lose_powers hR bound (by omega)
end Plain

/-- Radian cover frequencies (already real). -/
def london (z : E4) := (I : ℂ) • (Complex.ofRealCLM.comp (innerSL ℝ z))
def song (z : E4) (p : E4) : ℂ := exp (london z p)
lemma london_at (z p : E4) : london z p = I * (⟪z,p⟫_ℝ : ℂ) := rfl
lemma london_fee (z : E4) : ‖london z‖ ≤ ‖z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro p
  rw [london_at]; simpa using abs_real_inner_le_norm z p
lemma song_fee (z p) : ‖song z p‖=1 := by rw [song,london_at,mul_comm]; apply norm_exp_ofReal_mul_I
lemma song_smooth (z : E4) {n : ℕ∞ω} : ContDiff ℝ n (song z) := contDiff_exp.comp (london z).contDiff
lemma song_gradient (z : E4) (p : E4) : HasFDerivAt (song z) (song z p • london z) p := (london z).hasFDerivAt.cexp
lemma song_quotes (n : ℕ) (z p : E4) : ‖iteratedFDeriv ℝ n (song z) p‖ ≤ ‖z‖^n := by
  induction n with
  | zero => simp [song_fee]
  | succ n ih =>
    rw [← norm_iteratedFDeriv_fderiv,show fderiv ℝ (song z) = fun p => song z p • london z from funext fun x => (song_gradient z x).fderiv]
    let L := (ContinuousLinearMap.id ℝ ℂ).smulRight (london z)
    have hh : ‖L‖ ≤ ‖z‖ := L.opNorm_le_bound (norm_nonneg _) fun c => by
      change ‖c • london z‖ ≤ _; rw [norm_smul,mul_comm]; gcongr; exact london_fee z
    rw [pow_succ,mul_comm]; apply le_trans (L.norm_iteratedFDeriv_comp_left (song_smooth z (n:=n)).contDiffAt (show (n:ℕ∞ω)≤n from le_rfl)); gcongr

def mcast (p : E4) : Phase Axis := fun i => (p i:ℂ)
def rcast (x : Cover) : E4 := WithLp.toLp 2 fun i => (x i:ℝ)

lemma cast_mode (p : E4) (x : Cover) : mode (mcast p) x = song (rcast x) p := by
  rw [mode,song,london_at]; simp [PiLp.inner_apply,mcast,rcast]
lemma word_fee (x : Cover) : ‖rcast x‖ ≤ size x := by
  have he : rcast x=∑ a : Axis, ((x a:ℝ)) • basis a := by ext i; simp [rcast, mul_ite]
  rw [he]; apply (norm_sum_le ..).trans_eq; simp [norm_smul,size]

/-- Exponential receipt pays all symbol derivatives on real momenta. -/
lemma radial_prices {α Ω : ℝ} (ha : 0<α) (R : ℝ) (f : ι→Cover→ℂ) (h : ∀ i, Width α Ω (f i)) :
    Plain R (fun i p => Laurent.read (f i) (mcast p)) := by
  have hu (n : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0≤t → t^n ≤ A*Real.exp (α*t) := by
    cases n
    · exact ⟨1,zero_le_one,fun t ht => by simpa using (Real.one_le_exp (mul_nonneg ha.le ht))⟩
    next n =>
      let b := α / ((n+1:ℕ):ℝ)
      have hb : 0<b := by unfold b; positivity
      refine ⟨b⁻¹ ^(n+1),by positivity,fun t ht => ?_⟩
      have he : t ≤ b⁻¹ * Real.exp (b*t) := by
        rw [mul_comm,← div_eq_mul_inv,le_div_iff₀ hb,mul_comm]; exact le_trans (by linarith) (Real.add_one_le_exp _)
      apply (pow_le_pow_left₀ ht he (n+1)).trans_eq; rw [mul_pow,← Real.exp_nat_mul]; congr 2; unfold b; field_simp
  choose A hA H using hu
  let B i n x := A n * (Real.exp (α * size x)*‖f i x‖)
  let F (i : ι) (x : Cover) (p:E4) := f i x • song (rcast x) p
  have he (i : ι) : (fun p:E4=> Laurent.read (f i) (mcast p)) = fun p => ∑' x : Cover, F i x p := by
    unfold Laurent.read; simp_rw [cast_mode, F,smul_eq_mul]; funext p; apply tsum_congr; intro z; exact mul_comm ..
  have hx i n : Summable (B i n) := (h i).2.1.mul_left _
  have ht (n i) (x : Cover) (p : E4) : ‖iteratedFDeriv ℝ n (F i x) p‖ ≤ B i n x := by
    unfold F; rw [iteratedFDeriv_const_smul_apply' (song_smooth (rcast x) (n:=n)).contDiffAt,norm_smul]
    unfold B
    rw [← mul_assoc,mul_comm ‖_‖]; gcongr
    exact (song_quotes ..).trans ((pow_le_pow_left₀ (norm_nonneg _) (word_fee _) n).trans (H _ _ (by positivity)))
  have hd (i x) : ContDiff ℝ ∞ (F i x) := (song_smooth _).const_smul _
  refine ⟨fun i => ?_,fun n => ?_⟩
  · rw [he]; exact contDiff_tsum (hd i) (fun j _ => hx i j) (fun n x p _ => ht n i x p)
  refine ⟨A n * max 0 Ω,mul_nonneg (hA n) (le_max_left ..),fun i p _ => ?_⟩
  rw [he,iteratedFDeriv_tsum (hd i) (fun j _ => hx i j) (fun n x p _ => ht n i x p) le_top]; dsimp only
  have hu := Summable.of_nonneg_of_le (fun x:Cover=> norm_nonneg (iteratedFDeriv ℝ n (F i x) p)) (fun x=> ht n i x p) (hx i n)
  apply (norm_tsum_le_tsum_norm hu).trans ((hu.tsum_le_tsum (fun x=> ht n i x p) (hx i n)).trans ?_)
  unfold B
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left ((h i).2.2.trans (le_max_right ..)) (hA n)

end YM.Further.FreeCovariance.KP
