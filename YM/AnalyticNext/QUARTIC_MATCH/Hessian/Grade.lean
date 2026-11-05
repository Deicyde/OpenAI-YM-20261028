import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Stripe
import YM.Progress.STATIONARY_SCENES.Probe


/-!
# Mixed-sheet conjugation invoices (pre-L)

Coordinates on embedded physical tori for both fine and coarse part. Includes
these exact S paths before any sheet lengths chosen. No spectral smoothness
away from the identity. Use reciprocal weights ON FINE log-weight scale α/L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Hessian
open Filter Function Lattice Laurent Bloch Exterior Matrix Precision RG Work.F06
open Pre.Centered YM.Next.Free YM.Progress.StationaryScenes
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ComplexConjugate InnerProductSpace
namespace Tracks
open Green (Rows Both wt)
variable {ι m : Type*} [Fintype ι] [Fintype m] {n c f : Side}

section CT

variable (a : m→Site n) (b : ι→Site n) (H : Matrix m ι ℝ)

def hood (a : m→Site n) (η : ℝ) (z : Site n) (y : m→ℝ) := fun i => wt η (a i) z * y i
def shade (a : m→Site n) (b : ι→Site n) (θ : ℝ) (z : Site n) (H : Matrix m ι ℝ) : Matrix m ι ℝ :=
    Matrix.of fun i j => wt θ (a i) z / wt θ (b j) z * H i j
omit [Fintype m] [Fintype ι] in
lemma lefties (θ : ℝ) (x y : Site n) : wt (-θ) x y=(wt θ x y)⁻¹ := by unfold wt; rw [neg_mul, Real.exp_neg]
omit [Fintype m] in
lemma hit (θ : ℝ) (z : Site n) (x : ι→ℝ) : hood a θ z (H*ᵥ hood b (-θ) z x)=shade a b θ z H *ᵥ x := by
  funext i; unfold shade hood Matrix.mulVec dotProduct; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
  simp only [of_apply,lefties]; ring
omit [Fintype m] in
lemma hood_switch (θ : ℝ) (z : Site n) (x : m→ℝ) : hood a θ z (hood a (-θ) z x)=x := by
  funext i; unfold hood; rw [lefties,mul_inv_cancel_left₀ (Green.wt_pos ..).ne']
lemma hood_dot (θ : ℝ) (z : Site n) (x y : m→ℝ) : dotProduct (hood a θ z x) (hood a (-θ) z y)=dotProduct x y := by
  refine Finset.sum_congr rfl fun i _ => ?_; unfold hood; rw [lefties,mul_mul_mul_comm,mul_inv_cancel₀ (Green.wt_pos ..).ne',one_mul]
omit [Fintype m] [Fintype ι] in
lemma both_directions {t r η : ℝ} (he : 0 ≤ η) (hr : 0 ≤ r) (hu : |t| ≤ r*η) (hy : r ≤ 1) (i j z : Site n) :
    |wt t i z / wt t j z-1| ≤ r*wt η i j := by
  by_cases h : η=0
  · subst η; rw [mul_zero,abs_nonpos_iff] at hu; subst t; simpa [wt] using hr
  have hp : 0 < η := lt_of_le_of_ne he (Ne.symm h)
  rcases le_total 0 t with ha|ha
  · have hh : t/η ≤ r := (div_le_iff₀ hp).mpr ((le_abs_self t).trans hu)
    have hs := Green.diminishing he (div_nonneg ha he) (hh.trans hy) i j z; rw [div_mul_cancel₀ _ h] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right hh (Green.wt_pos ..).le)
  have hh : (-t)/η ≤ r := (div_le_iff₀ hp).mpr ((neg_le_abs _).trans hu)
  have hs := Green.diminishing he (div_nonneg (neg_nonneg.mpr ha) he) (hh.trans hy) j i z
  rw [div_mul_cancel₀ _ h,lefties,lefties,inv_div_inv,Green.wt_symm _ j i] at hs; exact hs.trans
    (mul_le_mul_of_nonneg_right hh (Green.wt_pos ..).le)
lemma shaded {t r η c d K : ℝ} (he : 0 ≤ η) (hr : 0 ≤ r) (hu : |t| ≤ r*η) (hy : r ≤ 1)
    (h : Both a b H η c d) (hp : c*d ≤ K^2) (hc : 0 ≤ c) (hk : 0 ≤ K) (z : Site n) (x : ι→ℝ) :
    ell2 (shade a b t z H *ᵥ x-H*ᵥ x) ≤ (r*K)*ell2 x := by
  let W := shade a b t z H-H
  have he i j : ‖W i j‖ ≤ r*(wt η (a i) (b j)*|H i j|) := by
    simp only [W, shade,Matrix.sub_apply, of_apply, Real.norm_eq_abs]
    rw [show _*_-H i j=(wt t (a i) z / wt t (b j) z-1)*H i j by rw [sub_mul,one_mul],abs_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (both_directions he hr hu hy _ _ _) (abs_nonneg _)
  have hX i : ∑ j, ‖W i j‖ ≤ r*c := by
    apply (Finset.sum_le_sum (fun j _ => he i j)).trans; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (h.1 i) hr
  have hY j : ∑ i, ‖W i j‖ ≤ r*d := by
    apply (Finset.sum_le_sum (fun i _ => he i j)).trans
    simp_rw [Green.wt_symm _ _ (b j)]; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (h.2 j) hr
  rw [← Matrix.sub_mulVec]; apply smear hX (mul_nonneg hr hc) hY _ (mul_nonneg hr hk)
  rw [mul_pow,mul_mul_mul_comm,← pow_two]; exact mul_le_mul_of_nonneg_left hp (sq_nonneg _)

lemma original {η c d K : ℝ} (he : 0 ≤ η) (h : Both a b H η c d) (hp : c*d ≤ K^2)
    (hc : 0 ≤ c) (hk : 0 ≤ K) (x : ι→ℝ) : ell2 (H *ᵥ x) ≤ K*ell2 x := by
  have hT (x y : Site n) (w : ℝ) : ‖w‖ ≤ wt η x y* |w| := le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_exp (by positivity))
  apply smear (fun i => le_trans _ (h.1 i)) hc (fun i => le_trans _ (h.2 i)) hp hk
  · intro i; exact Finset.sum_le_sum fun j _ => hT ..
  intro j; exact Finset.sum_le_sum fun i _ => hT ..
end CT

section locality
variable (S : StepData c f)
local notation "L" => S.patch.L.val

def small (i : ℕ) : ℕ := 4*(i+3)+1
lemma many (x : Site c) (v : S.patch.Points) (a : Axis) (l : ℕ) (hl : l ≤ L) :
    separation (S.ratio.embed x) (atPoint S x v + l • step a) ≤ small S.patch.J*L := by
  have hs := Response.at_point S x v
  apply (separation_triangle _ (atPoint S x v) _).trans
  have hg (y : Site f) (l : ℕ) : separation y (y+l • step a) ≤ l := by
    induction l with
    | zero => simp
    | succ l ih =>
      have hh := (separation_triangle y (y+l • step a) (y+l • step a+step a)).trans (Nat.add_le_add ih ((Response.by_one (y+l • step a) (posDir a)).1))
      rwa [succ_nsmul,← add_assoc]
  apply (Nat.add_le_add hs ((hg _ _).trans hl)).trans_eq; unfold Patch.radius small; ring

lemma mean_radius (i k) (h : small S.patch.J*L < separation (S.ratio.embed i.1) k.1) : Precision.mean S i k=0 := by
  let v : form 1 f := Pi.single k 1
  have ht : Precision.mean S i k=(Precision.mean S*ᵥ v) i := by rw [show v=_ from (rfl : v=Pi.single k 1), Matrix.mulVec_single_one]; rfl
  rw [ht,mean_run_real]; refine Finset.sum_eq_zero fun j _ => mul_eq_zero.mpr (Or.inr ?_)
  refine Finset.sum_eq_zero fun l hl => Pi.single_eq_of_ne ?_ _
  intro heq
  have he := many S i.1 j (axisEquiv.symm i.2) l (Finset.mem_range.mp hl).le
  rw [show _ + _ = k.1 from congr_arg Prod.fst heq] at he; omega
lemma palette_radius (i k) (h : small S.patch.J*L < separation (S.ratio.embed i.1) k.1) : palette S i k=0 := by
  let v : form 0 f := Pi.single k 1
  have ht : palette S i k=(palette S*ᵥ v) i := by unfold v; rw [Matrix.mulVec_single_one]; rfl
  rw [ht,palette_site]; refine Finset.sum_eq_zero fun j _ => mul_eq_zero.mpr (Or.inr ?_)
  apply Pi.single_eq_of_ne ?_ _; intro heq; have he := many S i.1 j 0 0 (Nat.zero_le _)
  rw [zero_smul,add_zero, show atPoint S i.1 j = k.1 from congr_arg Prod.fst heq] at he; omega

abbrev locator {r : ℕ} (i : Body r c) := S.ratio.embed i.1
def tagPrice (i : ℕ) (η : ℝ) := Real.exp (η*small i)
lemma tp_pos (i : ℕ) (η : ℝ) : 0 < tagPrice i η := Real.exp_pos _
lemma color_pay {η : ℝ} {r k : ℕ} (he : 0 ≤ η) (i : Body r c) (q : Body k f)
    {x : ℝ} (h : 0 ≤ x) (hv : small S.patch.J*L < separation (locator S i) q.1 → x=0) :
    wt (η/L) (locator S i) q.1*|x| ≤ tagPrice S.patch.J η*x := by
  by_cases hh : small S.patch.J*L < separation (locator S i) q.1
  · rw [hv hh]; simp
  have hp := side_pos S.patch.L
  have ht : (separation (locator S i) q.1:ℝ)/(L:ℝ) ≤ small S.patch.J := by apply (div_le_iff₀ hp).mpr; exact_mod_cast le_of_not_gt hh
  rw [abs_of_nonneg h]; apply mul_le_mul_of_nonneg_right _ h; apply Real.exp_monotone
  rw [div_mul_eq_mul_div, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left ht he
lemma mean_price {η : ℝ} (he : 0 ≤ η) : Both (locator S) Prod.fst (Precision.mean S) (η/L)
    (tagPrice S.patch.J η*L) (tagPrice S.patch.J η*((L:ℝ)^3)⁻¹) := by
  constructor <;> intro i
  · conv_rhs => rw [← mean_rows S i,Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => color_pay S he _ _ (mean_pos ..) (mean_radius S _ _)
  conv_rhs => rw [← mean_columns S i,Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_; rw [Green.wt_symm]; exact color_pay S he _ _ (mean_pos ..) (mean_radius S _ _)
lemma palette_price {η : ℝ} (he : 0 ≤ η) : Both (locator S) Prod.fst (palette S) (η/L)
    (tagPrice S.patch.J η) (tagPrice S.patch.J η*((L:ℝ)^4)⁻¹) := by
  constructor <;> intro i
  · conv_rhs => rw [← mul_one (tagPrice S.patch.J η),← palette_rows S i,Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => color_pay S he _ _ (palette_pos ..) (palette_radius S _ _)
  conv_rhs => rw [← palette_columns S i,Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_; rw [Green.wt_symm]; exact color_pay S he _ _ (palette_pos ..) (palette_radius S _ _)

open Work.F08 in
def dc (r : ℕ) (η : ℝ) := 1+max 0 (max ((Fintype.card (TypeFace r):ℝ)*stencilCost r η)
      ((Fintype.card (TypeFace (r+1)):ℝ)*stencilCost r η))
lemma dc_pos (r : ℕ) (η : ℝ) : 0<dc r η := add_pos_of_pos_of_nonneg one_pos (le_max_left ..)
lemma both_axis (r : ℕ) (n : Side) {η : ℝ} (he : 0 ≤ η) : Both Prod.fst Prod.fst (d r n) η (dc r η) (dc r η) := by
  obtain ⟨h,g⟩ := Green.periodic (cobound r) n he (Work.F08.strip_stencil r η)
  exact ⟨fun i => (h i).trans ((le_max_of_le_right (le_max_left ..)).trans (le_add_of_nonneg_left zero_le_one)),
    fun i => (g i).trans ((le_max_of_le_right (le_max_right ..)).trans (le_add_of_nonneg_left zero_le_one))⟩
lemma both_coarse (r : ℕ) {η : ℝ} (he : 0 ≤ η) : Both (locator S) (locator S) (d r c) (η/L) (dc r η) (dc r η) := by
  obtain ⟨h,g⟩ := both_axis r c he
  have he' (x y : Site c) : wt (η/L) (S.ratio.embed x) (S.ratio.embed y) ≤ wt η x y := by
    apply Real.exp_monotone; rw [div_mul_eq_mul_div, mul_div_assoc]; apply mul_le_mul_of_nonneg_left _ he
    apply (div_le_iff₀ (side_pos S.patch.L)).mpr; rw [mul_comm]; exact_mod_cast (scaled_root S.ratio x y)
  exact ⟨fun i => le_trans (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (he' i.1 j.1) (abs_nonneg _)) (h i),
    fun i => le_trans (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (he' i.1 j.1) (abs_nonneg _)) (g i)⟩
end locality
end Tracks
end YM.AnalyticNext.QuarticMatch.Hessian
