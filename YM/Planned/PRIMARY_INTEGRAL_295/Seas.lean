import YM.Planned.PRIMARY_INTEGRAL_295.Oval


/-!
# Normalized fine log chart for J-pr. Entire smooth extension & powers estimate

Bump extension is immaterial on all actually permitted paths. Inputs the
absorbable m and α, and tree/fine Gauge φ at EVERY pair of endpoints. Keep
`start - end` under such gauge. Predictor represented in absolute log
coords from genuine E `u_*` slices. Costs throughout, even at nonlinear
stationary round due to b directions; no promising a Fourier multiplier in
the nonlinear variables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Seas
open Function Filter Set Metric MeasureTheory Oval Place Labels Lattice RG Source Source.Drops
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {E F G Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {l k n : ℕ}

section
variable {x : E} {f : E→F} {q : F→G} {g : E→Y}
lemma joined (hq : ContDiff ℝ k q) (hf : ContDiffAt ℝ k f x)
    {C D : ℝ} (hB : Oval.Envelope x k f C) (hC : Oval.Envelope (f x) k q D) :
    Oval.Envelope x k (q ∘ f) (k.factorial*D*(1+C)^k) := by
  classical
  have ht':=hC.1; have hb := hB.1; have hP := show 1 ≤ 1+C by linarith
  let s := interior {x | ContDiffAt ℝ k f x}
  have hs : IsOpen s := isOpen_interior; have hx : x∈s := mem_interior_iff_mem_nhds.mpr (hf.eventually (by simp))
  refine ⟨by positivity,fun n hn=>?_⟩
  have he : ContDiffOn ℝ k f s := fun y hy=> (show ContDiffAt ℝ k f y from interior_subset hy).contDiffWithinAt
  have hz := norm_iteratedFDerivWithin_comp_le (s:=s) (t:=univ) hq.contDiffOn he (Nat.cast_le.mpr hn) uniqueDiffOn_univ hs.uniqueDiffOn
    (fun x _=> mem_univ _) hx (C:=D) (D:=1+C)
  rw [iteratedFDerivWithin_of_isOpen _ hs hx] at hz; apply le_trans (hz ?_ ?_) _
  · simpa only [iteratedFDerivWithin_univ] using fun i hi=> hC.2 i (hi.trans hn)
  · intro i hi he; rw [iteratedFDerivWithin_of_isOpen _ hs hx]; exact ((hB.2 i (he.trans hn)).trans (le_add_of_nonneg_left zero_le_one)).trans (le_self_pow₀ hP (by omega))
  gcongr



lemma scaleBy (hf : ContDiffAt ℝ k f x) (t C : ℝ) (h : Oval.Envelope x k f C) : Oval.Envelope x k (t • f) (‖t‖ * C) := by
  refine ⟨mul_nonneg (norm_nonneg _) h.1,fun n hn=>?_⟩
  rw [iteratedFDeriv_const_smul_apply (hf.of_le (Nat.cast_le.mpr hn)),norm_smul]; exact mul_le_mul_of_nonneg_left (h.2 n hn) (norm_nonneg t)

lemma add {g : E→F} (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x)
    {C D : ℝ} (h : Oval.Envelope x k f C) (h' : Oval.Envelope x k g D) : Oval.Envelope x k (f+g) (C+D) := by
  refine ⟨add_nonneg h.1 h'.1,fun n hn=>?_⟩
  rw [iteratedFDeriv_add_apply (hf.of_le (Nat.cast_le.mpr hn)) (hg.of_le (Nat.cast_le.mpr hn))]
  exact (norm_add_le ..).trans (add_le_add (h.2 n hn) (h'.2 n hn))
lemma less {C D : ℝ} (h : Oval.Envelope x k f C) (hc : C≤D) : Oval.Envelope x k f D := ⟨h.1.trans hc,fun n hn=> (h.2 n hn).trans hc⟩
lemma fuzzy {g : E→F} (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) (C : ℝ) : Oval.Envelope x k (f-g) C ↔ Fuzz x k f g C := by
  have he (n:ℕ) (hn:n≤k) := iteratedFDeriv_sub_apply (hf.of_le (Nat.cast_le.mpr hn)) (hg.of_le (Nat.cast_le.mpr hn))
  constructor <;> intro h <;> refine ⟨h.1,fun n hn=>?_⟩
  · rw [← he n hn]; exact h.2 n hn
  rw [he n hn]; exact h.2 n hn

lemma paidLinear (L : F →L[ℝ] G) (hf : ContDiffAt ℝ k f x) {C D : ℝ} (h : Oval.Envelope x k f C) (hL : ‖L‖≤D) :
    Oval.Envelope x k (L ∘ f) (D*C) := by
  have hh:0≤D := (norm_nonneg _).trans hL; refine ⟨mul_nonneg hh h.1,fun n hn=>?_⟩
  apply (L.norm_iteratedFDeriv_comp_left hf (Nat.cast_le.mpr hn)).trans
  exact mul_le_mul hL (h.2 n hn) (norm_nonneg _) hh

-- Group Taylor residual on `q: F→G`; convert by actual C^k germs.
def glaze (L : F →L[ℝ] G) (q : F→G) (t : ℝ) (f : E→F) (x : E) := t⁻¹ • q (t • f x) - L (f x)

variable [FiniteDimensional ℝ F]

lemma expenseLog (L : F →L[ℝ] G) (q : F → G) (hq : ContDiff ℝ ∞ q) (h₀ : q 0=0) (h₁ : fderiv ℝ q 0=L) (k : ℕ) (R : ℝ) :
    ∃ C:ℝ, 1 ≤ C ∧ ∀ {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (x:E') (f:E'→F)
      (_:ContDiffAt ℝ k f x) (N:ℝ) (_:Oval.Envelope x k f N) (t:ℝ), t∈Ioc (0:ℝ) 1 → ‖t • f x‖ ≤ R →
        Oval.Envelope x k (glaze L q t f) (t*C*(1+N)^(2+k)) := by
  classical
  let Q := q-(fun y=> L y)
  have h : ContDiff ℝ ∞ Q := hq.sub L.contDiff
  have HQ₀ : Q 0=0 := by simp [Q,h₀]
  have HQ₁ : fderiv ℝ Q 0=0:=by
    unfold Q; rw [fderiv_sub (hq.differentiable (by simp) 0) L.differentiableAt,h₁,L.fderiv,sub_self]
  letI:= FiniteDimensional.proper ℝ F
  have he (n:ℕ) : ∃ C:ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1, ∀ z:F, ‖t • z‖≤R →
      ‖iteratedFDeriv ℝ n (fun z:F => t⁻¹ • Q (t • z)) z‖ ≤ t*C*(1+‖z‖)^2 := by
    have hv (i) (hi : n ≤ i) (hh : i < n+(2-n)) : iteratedFDeriv ℝ i Q 0=0 := by
      rcases show i=0 ∨ i=1 by omega with rfl|rfl
      · ext; simp [HQ₀]
      ext; simp [HQ₁]
    obtain ⟨C,hC,H⟩ := Outer.earnings Q h n (2-n) hv R
    refine ⟨C,hC,fun t ht z hz=>?_⟩
    have hp : 0<t:=ht.1; have hh : t ≤ 1:=ht.2
    let g (z:F):=Q (t • z)
    have hN : (n:WithTop ℕ∞)≤∞ := by exact_mod_cast le_top
    have hg : ContDiff ℝ n g := (h.of_le hN).comp (contDiff_const.smul contDiff_id)
    change ‖iteratedFDeriv ℝ n (t⁻¹ • g) z‖≤_
    rw [iteratedFDeriv_const_smul_apply hg.contDiffAt,norm_smul]; unfold g
    rw [iteratedFDeriv_comp_const_smul t (h.of_le hN),norm_smul]
    rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity),←mul_assoc]
    apply (mul_le_mul_of_nonneg_left (H _ hz) (by positivity)).trans
    let m:=2-n
    have ht : 1≤1+‖z‖ := by simp
    have he : t⁻¹ * t^(n+m)≤ t := by
      apply (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hp.le hh (show 2 ≤ n+m by omega)) (inv_nonneg.mpr hp.le)).trans
      rw [pow_two,inv_mul_cancel_left₀ hp.ne']
    have hW : ‖z‖^m≤(1+‖z‖)^2 := (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) _).trans (pow_le_pow_right₀ ht (by omega))
    calc
      _ = (t⁻¹*t^(n+m))*C*‖z‖^m := by rw [norm_smul,Real.norm_of_nonneg hp.le,mul_pow,pow_add]; unfold m; ring
      _ ≤ t*C*(1+‖z‖)^2 := by exact mul_le_mul (mul_le_mul_of_nonneg_right he hC) hW (by positivity) (by positivity)
  choose B hB h' using he
  let K:=1+∑ i∈Finset.range (k+1),B i; have hK : 1 ≤ K := le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> hB i)
  have ht (n:ℕ) (hn:n≤k) : B n≤K := (Finset.single_le_sum (fun i _=> hB i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))).trans (le_add_of_nonneg_left zero_le_one)
  have hk : 1 ≤ (k.factorial:ℝ):= by exact_mod_cast k.factorial_pos
  refine ⟨k.factorial*K,one_le_mul_of_one_le_of_one_le hk hK, fun x f hf N hF t Ht hv'=>?_⟩
  have hp := show 0<t from Ht.1
  let A (z : F):=t⁻¹ • Q (t • z)
  have hh : ContDiff ℝ k A := contDiff_const.smul ((h.of_le (by exact_mod_cast le_top)).comp (contDiff_const.smul contDiff_id))
  have he : glaze L q t f = A ∘ f := by
    funext x; unfold glaze A Q; change _ = _ • (_-L _); rw [smul_sub,map_smul, inv_smul_smul₀ hp.ne']
  rw [he]
  have hf' : Oval.Envelope (f x) k A (t*K*(1+N)^2) := by
    have hg:=hF.1; refine ⟨by positivity,fun n hn=> (h' n t Ht _ hv').trans ?_⟩
    gcongr; exacts [ht n hn,hF.value]
  convert! joined hh hf hF hf' using 1
  rw [pow_add]; ring
end
end YM.Planned.PrimaryIntegral295.Seas
