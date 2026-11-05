import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import YM.Next.MAXWELL.House


/-!
# Real polarized Maxwell stress and local currents

The bilinear used throughout includes both assignments of the two legs.
Flux taken **outward** (minus gradient of a cutoff).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Can use locally even on fields that don't satisfy homogeneous Maxwell
(smooth regularized source leg). -/
structure Bianchi (U : Set E4) (f : Field F) : Prop where
  smooth (a b : Axis) (x : E4) : x ∈ U → ContDiffAt ℝ ∞ (f a b) x
  skew (a b : Axis) (x : E4) : x ∈ U → f a b x = -f b a x
  cycle (a b c : Axis) (x : E4) : x ∈ U →
    grad a (f b c) x + grad b (f c a) x + grad c (f a b) x = 0

lemma wave_closed {U : Set E4} {f : Field F} (H : WaveOn U f) : Bianchi U f := ⟨H.smooth,H.form,H.cycle⟩

def divF (f : Field F) (c : Axis) (x : E4) := ∑ a : Axis, grad a (f a c) x

def cross (f g : Field F) (a b : Axis) (x : E4) :=
    (∑ c : Axis, (⟪f a c x,g b c x⟫_ℝ + ⟪f b c x,g a c x⟫_ℝ)) -
      kr a b * (1/2) * ∑ i : Axis, ∑ l : Axis, ⟪f i l x,g i l x⟫_ℝ

lemma cross_comm (f g : Field F) (a b) (x) : cross f g a b x = cross g f a b x := by
  unfold cross
  conv_rhs =>
    arg 1
    rhs; intro c
    rw [← real_inner_comm (g a c x),← real_inner_comm (g b c x),add_comm]
  congr 2
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => real_inner_comm _ _

lemma cross_adjoin (f g u : Field F) (a b x) : cross f (g+u) a b x = cross f g a b x + cross f u a b x := by
  simp only [cross,Pi.add_apply,inner_add_right, Finset.sum_add_distrib,mul_add]; ring

lemma cross_stretch (f g : Field F) (t : ℝ) (a b x) : cross f (t • g) a b x = t * cross f g a b x := by
  simp only [cross,Pi.smul_apply,real_inner_smul_right,← mul_add, ← Finset.mul_sum]; ring

lemma cross_rotate_indices (f g : Field F) (a b x) : cross f g a b x = cross f g b a x := by
  unfold cross; rw [kr_symm a b]; simp only [Finset.sum_add_distrib,add_comm (_ : ℝ)]

lemma cross_trace (f g : Field F) (x) : ∑ a : Axis, cross f g a a x = 0 := by
  unfold cross
  simp only [kr_eq, if_true, one_mul,Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  ring

lemma grad_skew {U : Set E4} {g : Field F} (H : Bianchi U g) (hU : IsOpen U) (a b c) {x} (hx : x ∈ U) :
    grad a (g b c) x = -grad a (g c b) x := by
  have he : g b c =ᶠ[𝓝 x] -g c b := by
    filter_upwards [hU.mem_nhds hx] with y hy; exact H.skew b c y hy
  unfold grad D; rw [he.fderiv_eq,fderiv_neg]; rfl

lemma force_sym {U : Set E4} {f g : Field F} (H : Bianchi U f) (K : Bianchi U g)
    (hU : IsOpen U) (b : Axis) {x : E4} (hx : x ∈ U) :
    (∑ a : Axis, ∑ c : Axis, ⟪f a c x, grad a (g b c) x⟫_ℝ) =
      (1/2) * ∑ a : Axis, ∑ c : Axis, ⟪f a c x, grad b (g a c) x⟫_ℝ := by
  have he (a c : Axis) : grad a (g b c) x = grad b (g a c) x - grad c (g a b) x := by
    have ht := K.cycle a b c x hx; nth_rw 1 [grad_skew K hU b c a hx] at ht
    rw [eq_sub_iff_add_eq]
    rw [← sub_eq_zero]
    refine Eq.trans ?_ ht
    abel
  let R := ∑ a : Axis, ∑ c : Axis, ⟪f a c x, grad a (g b c) x⟫_ℝ
  have hm : ∑ a : Axis, ∑ c : Axis, ⟪f a c x, grad c (g a b) x⟫_ℝ = R := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro c _
    rw [H.skew c a x hx, grad_skew K hU a c b hx,inner_neg_neg]
  change R = _
  have hr : R = (∑ a : Axis, ∑ c : Axis, ⟪f a c x, grad b (g a c) x⟫_ℝ) - R := by
    conv_lhs =>
      unfold R; rhs; intro i; rhs; intro l; rw [he i l, inner_sub_right]
    simp only [Finset.sum_sub_distrib, hm]
  linarith

lemma cross_diff {f g : Field F} (a b : Axis) {x} (hf : ∀ i l, ContDiffAt ℝ ∞ (f i l) x)
    (hg : ∀ i l, ContDiffAt ℝ ∞ (g i l) x) : ContDiffAt ℝ ∞ (cross f g a b) x := by
  unfold cross; refine ContDiffAt.sub ?_ (contDiffAt_const.mul ?_)
  · exact ContDiffAt.sum fun i _ => ((hf _ _).inner ℝ (hg _ _)).add ((hf _ _).inner ℝ (hg _ _))
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => (hf _ _).inner ℝ (hg _ _)

lemma crossD {f g : Field F} {x} (hf : ∀ i l, ContDiffAt ℝ ∞ (f i l) x)
    (hg : ∀ i l, ContDiffAt ℝ ∞ (g i l) x) (a b : Axis) (u : E4) :
    D u (cross f g a b) x = cross (fun i l => D u (f i l)) g a b x +
      cross f (fun i l => D u (g i l)) a b x := by
  let L (i l m k : Axis) (z : E4) := ⟪f i l z, g m k z⟫_ℝ
  have ht (i l m k) : DifferentiableAt ℝ (L i l m k) x :=
    (((hf i l).inner ℝ (hg m k)).differentiableAt (by simp))
  have he (i l m k) : fderiv ℝ (L i l m k) x u = ⟪D u (f i l) x, g m k x⟫_ℝ + ⟪f i l x, D u (g m k) x⟫_ℝ := by
    dsimp only [L]
    rw [fderiv_inner_apply _ ((hf i l).differentiableAt (by simp)) ((hg m k).differentiableAt (by simp))]
    exact add_comm _ _
  have hr (c) : DifferentiableAt ℝ (fun z => L a c b c z + L b c a c z) x := (ht ..).add (ht ..)
  have hs (i : Axis) : DifferentiableAt ℝ (fun z => ∑ l : Axis, L i l i l z) x :=
    DifferentiableAt.fun_sum (fun l _ => ht ..)
  have hd : DifferentiableAt ℝ (fun z => ∑ i : Axis, ∑ l : Axis, L i l i l z) x :=
    DifferentiableAt.fun_sum (fun i _ => hs ..)
  change fderiv ℝ (fun z => (∑ c : Axis, (L a c b c z + L b c a c z)) -
    kr a b * (1/2) * ∑ i : Axis, ∑ l : Axis, L i l i l z) x u = _
  rw [fderiv_fun_sub (DifferentiableAt.fun_sum (fun i _ => hr _))
    (show DifferentiableAt ℝ (fun z => kr a b * (1/2) * ∑ i : Axis, ∑ l : Axis, L i l i l z) x from hd.const_mul _),
    fderiv_fun_sum (fun i _ => hr _), fderiv_const_mul hd, fderiv_fun_sum (fun i _ => hs _)]
  have hk (c : Axis) : fderiv ℝ (fun z => L a c b c z + L b c a c z) x u =
      fderiv ℝ (L a c b c) x u + fderiv ℝ (L b c a c) x u := by
    rw [fderiv_fun_add (ht ..) (ht ..)]; rfl
  have hw (i : Axis) : fderiv ℝ (fun z => ∑ l : Axis, L i l i l z) x u = ∑ l : Axis, fderiv ℝ (L i l i l) x u := by
    rw [fderiv_fun_sum (fun l _ => ht i l i l),sum_apply]
  unfold cross; simp only [sub_apply,sum_apply,smul_apply, smul_eq_mul,hk,hw,he, Finset.sum_add_distrib,mul_add]
  ring

lemma div_cross {f g : Field F} {U : Set E4} (H : Bianchi U f) (K : Bianchi U g)
    (hU : IsOpen U) {x} (hx : x ∈ U) (b : Axis) :
    (∑ a : Axis, grad a (cross f g a b) x) = ∑ c : Axis, (⟪divF f c x,g b c x⟫_ℝ + ⟪f b c x,divF g c x⟫_ℝ) := by
  have he (f g : Field F) (H : Bianchi U f) (K : Bianchi U g) : (∑ a : Axis,
      cross f (fun i l => grad a (g i l)) a b x) = ∑ c : Axis, ⟪f b c x,divF g c x⟫_ℝ := by
    unfold cross
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,force_sym H K hU b hx,kr_eq, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    unfold divF
    simp_rw [inner_sum,Finset.sum_comm (f := fun a c => ⟪f b c x,grad a (g a c) x⟫_ℝ)]
    ring
  have ht (a : Axis) : grad a (cross f g a b) x = cross g (fun i l => grad a (f i l)) a b x +
      cross f (fun i l => grad a (g i l)) a b x := by
    rw [grad, crossD (fun i l => H.smooth i l x hx) (fun i l => K.smooth i l x hx), cross_comm (fun i l => _) g]; rfl
  simp_rw [ht, Finset.sum_add_distrib,he _ _ K H, he _ _ H K,← real_inner_comm (divF f _ x)]

abbrev Drive := Axis → E4 → ℝ

/-- Dilation, rotations and translations are all admitted. -/
structure Killing (v : Drive) : Prop where
  diff i : ContDiff ℝ ∞ (v i)
  off (a b : Axis) : a ≠ b → ∀ x, grad a (v b) x = -grad b (v a) x
  diag (a b : Axis) : ∀ x, grad a (v a) x = grad b (v b) x

def current (v : Drive) (f g : Field F) (a : Axis) (x : E4) := ∑ b : Axis, v b x * cross f g a b x

lemma current_diff {v : Drive} (h : Killing v) {f g : Field F} (a : Axis) {x}
    (hf : ∀ i l, ContDiffAt ℝ ∞ (f i l) x) (hg : ∀ i l, ContDiffAt ℝ ∞ (g i l) x) :
    ContDiffAt ℝ ∞ (current v f g a) x := ContDiffAt.sum fun i _ => (h.diff _).contDiffAt.mul (cross_diff a i hf hg)

lemma current_div {f g : Field F} {U : Set E4} (H : Bianchi U f) (K : Bianchi U g) (hU : IsOpen U)
    {v : Drive} (h : Killing v) {x : E4} (hx : x ∈ U) : (∑ a : Axis, grad a (current v f g a) x) =
      ∑ b : Axis, v b x * ∑ c : Axis, (⟪divF f c x,g b c x⟫_ℝ + ⟪f b c x,divF g c x⟫_ℝ) := by
  have hd (a b : Axis) : DifferentiableAt ℝ (cross f g a b) x := (cross_diff a b
    (fun i l => H.smooth i l x hx) (fun i l => K.smooth i l x hx)).differentiableAt (by simp)
  let w := grad timeAxis (v timeAxis) x
  let T a b := grad a (v b) x * cross f g a b x
  have he (a : Axis) : grad a (current v f g a) x = ∑ b : Axis,
      (T a b + v b x * grad a (cross f g a b) x) := by
    change fderiv ℝ (fun y => ∑ b : Axis, v b y * cross f g a b y) x _ = _
    have hm (b : Axis) : DifferentiableAt ℝ (fun x => v b x * cross f g a b x) x :=
      ((h.diff b).differentiable (by simp) x).mul (hd a b)
    rw [fderiv_fun_sum (fun i _ => hm i),sum_apply]; apply Finset.sum_congr rfl; intro b _
    rw [fderiv_fun_mul ((h.diff b).differentiable (by simp) x) (hd a b)]
    simp [T,grad,D,add_comm, mul_comm]
  simp_rw [he,Finset.sum_add_distrib]
  have ht : ∑ a : Axis, ∑ b : Axis, T a b = 0 := by
    let R := ∑ a : Axis, ∑ b : Axis, T a b
    have hy : R+R = ∑ a : Axis, ∑ b : Axis, (T a b+T b a) := by
      simp only [Finset.sum_add_distrib]; unfold R; rw [Finset.sum_comm (f := fun a b => T b a)]
    have hw (a b : Axis) : T a b + T b a = if a=b then 2*w * cross f g a a x else 0 := by
      unfold T
      split_ifs with hb
      · subst b; rw [h.diag a timeAxis x]; unfold w; ring
      rw [h.off a b hb, cross_rotate_indices f g a b x, neg_mul]; simp
    simp_rw [hw] at hy
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum,
      cross_trace f g x, mul_zero] at hy
    change R = 0
    linarith
  rw [ht,zero_add,Finset.sum_comm]; simp_rw [← Finset.mul_sum, div_cross H K hU hx, Finset.sum_add_distrib]

/-- General usable cutoff, not necessarily equal to one in these definitions. -/
def exportFlux {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] (j : Axis → E4 → M)
    (χ : E4 → ℝ) : M := -∑ a : Axis, ∫ y : E4, grad a χ y • j a y

def singleFlux (v : Drive) (χ : E4 → ℝ) (f g : Field F) := exportFlux (current v f g) χ

section Test
-- many manipulations about real currents and also complex coefficients
variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
variable {χ : E4 → ℝ}

lemma cutoff_cost (hχ : Continuous χ) (Hχ : HasCompactSupport χ) {f : E4 → M}
    (h : ∀ x ∈ tsupport χ, ContinuousAt f x) : Integrable (fun x : E4 => χ x • f x) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ Hχ.smul_right
  apply continuous_iff_continuousAt.mpr; intro y
  by_cases he : y ∈ tsupport χ
  · exact hχ.continuousAt.smul (h y he)
  apply continuousAt_const.congr (show (fun _ : E4 => (0:M)) =ᶠ[𝓝 y] (fun x => χ x • f x) from ?_)
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp he] with z hz; rw [hz]; exact (zero_smul _ _).symm

lemma gradient_smooth (hχ : ContDiff ℝ ∞ χ) (i) : ContDiff ℝ ∞ (grad i χ) := contDiff_iff_contDiffAt.mpr fun _ =>
  grad_smooth _ hχ.contDiffAt (by simp)

lemma gradient_small (Hχ : HasCompactSupport χ) (i) : HasCompactSupport (grad i χ) :=
  Hχ.fderiv_apply ℝ (basis i)

lemma gradient_part (χ : E4 → ℝ) (a : Axis) : tsupport (grad a χ) ⊆ tsupport (fderiv ℝ χ) :=
  tsupport_comp_subset (g := ContinuousLinearMap.apply ℝ ℝ (basis a)) (map_zero _) _

lemma shell_cost (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ) {f : E4 → M}
    (h : ∀ x ∈ tsupport (fderiv ℝ χ), ContinuousAt f x) (a : Axis) :
    Integrable (fun x => grad a χ x • f x) := cutoff_cost (gradient_smooth hχ a).continuous
      (gradient_small Hχ a) fun x hx => h x (gradient_part χ a hx)

lemma by_parts (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ) {j : Axis → E4 → M}
    (h : ∀ a x, x ∈ tsupport χ → ContDiffAt ℝ ∞ (j a) x) :
    exportFlux j χ = ∫ y : E4, χ y • ∑ a : Axis, grad a (j a) y := by
  have ht (a) : Integrable (fun y => χ y • grad a (j a) y) := cutoff_cost hχ.continuous Hχ (fun x hx =>
    (grad_smooth _ (h a x hx) (m := ∞) (by simp)).continuousAt)
  have he (a) : -(∫ y : E4, grad a χ y • j a y) = ∫ y : E4, χ y • grad a (j a) y :=
    (integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (shell_cost hχ Hχ
      (fun x hx => (h a x (tsupport_fderiv_subset ℝ hx)).continuousAt) a) (ht a)
      (cutoff_cost hχ.continuous Hχ (fun x hx => (h a x hx).continuousAt))
      (fun x _ => hχ.differentiable (by simp) x) (fun x hx => (h a x hx).differentiableAt (by simp))).symm
  simp_rw [exportFlux, ← Finset.sum_neg_distrib,he,Finset.smul_sum]
  rw [← integral_finsetSum _ (fun a _ => ht a)]

lemma enclosed (x : E4) (hw : χ =ᶠ[𝓝 x] fun _ => 1) : x ∈ tsupport χ := by
  apply subset_closure; change χ x ≠ 0
  rw [show χ x=1 from hw.self_of_nhds]; norm_num

lemma collar {x : E4} (hw : χ =ᶠ[𝓝 x] fun _ => 1) : x ∉ tsupport (fderiv ℝ χ) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [hw.fderiv (𝕜 := ℝ)] with z hz; simp [hz]
end Test

lemma sourcefree_flux {v : Drive} (h : Killing v) {U : Set E4} {χ : E4 → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (Hχ : HasCompactSupport χ) (ht : tsupport χ ⊆ U) {f g : Field F} (H : WaveOn U f)
    (K : WaveOn U g) (hU : IsOpen U) : singleFlux v χ f g = 0 := by
  rw [singleFlux,by_parts hχ Hχ (fun a x hx => current_diff h _ (fun i l => H.smooth i l x (ht hx))
    fun i l => K.smooth i l x (ht hx))]
  rw [show (fun y : E4 => χ y • ∑ a : Axis, grad a (current v f g a) y) = 0 by
    funext y
    by_cases hy : y ∈ tsupport χ
    · rw [current_div (wave_closed H) (wave_closed K) hU h (ht hy)]
      simp [divF, H.divergence _ y (ht hy), K.divergence _ y (ht hy)]
    simp [image_eq_zero_of_notMem_tsupport hy]]
  exact integral_zero ..

end YM.Maxwell.Free
