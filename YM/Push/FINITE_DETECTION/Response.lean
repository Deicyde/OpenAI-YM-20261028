import YM.Push.FINITE_DETECTION.Harmonic
import YM.Work.B06

/-!
# Kelvin response of homogeneous Maxwell probes

Test a rank-j leg by contracting its Taylor coefficient with an on-shell
symmetric tensor (basis colors, Euclidean contraction). Off zero the field
left on the other end, still in the difference variable `x`, is exactly a
positive constant times the inverted homogeneous solution (inversion here
has argument **minus** `x/‖x‖²`). In particular this computes a family of
independent leg probes on the covariance in the *given* normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Kelvin
open Analysis Tensor Maxwell WaveOn Function Set Filter ContinuousMultilinearMap
open scoped Topology ContDiff BigOperators
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Gauge} {j : ℕ}

def actual (Y : TwoJet F j) : Maxwell.Field F := fun a b => Tensor.diagonal (Y a b)

lemma wave_actual {Y : TwoJet F j} (hY : Y ∈ onShell F j) : WaveOn univ (actual Y) :=
  ⟨fun _ _ _ _ => (diag_smooth _ ∞).contDiffAt,
   fun a b _ _ => by unfold actual; nth_rw 1 [hY.1.antisymmetric a b]; rfl,
   fun a b c x _ => hY.1.closed a b c x, fun b x _ => hY.2 b x⟩

def monochrome (Y : TwoJet G.Color j) (c : G.ColorIndex) : TwoJet ℝ j := fun i l =>
  (EuclideanSpace.proj c : G.Color →L[ℝ] ℝ).compContinuousMultilinearMap (Y i l)

lemma monochrome_mem (Y : Shell G j) (c : G.ColorIndex) : monochrome (G := G) Y.val c ∈ onShell ℝ j := by
  have H := Y.property.1
  have hw : WaveOn univ (actual (monochrome (G := G) Y.val c)) := composeColor (EuclideanSpace.proj c) (wave_actual Y.property)
  exact ⟨⟨fun a b v s => congr_arg (fun (z : G.Color) => z c) (H.coeffSym a b v s),
    fun a b => by ext1 v; exact congr_arg (fun (A : T E4 G.Color j) => A v c) (H.antisymmetric a b),
    fun a b m x => hw.cycle a b m x trivial⟩,fun b x => hw.divergence b x trivial⟩

/-- Functional indexed by a tensor (ordinary component contraction over ALL
a,b, positions & colors, no conjugation, no 1/2 for antisymmetrized pairs). -/
def frob (Y : TwoJet G.Color j) : Extended G j := ∑ c : G.ColorIndex, ∑ a : Axis, ∑ b : Axis,
  ∑ u : Fin j → Axis, (Y a b (basis ∘ u) c) • fromF G (basis ∘ u) c a b

lemma frob_apply (Y Z : TwoJet G.Color j) : frob (G := G) Y Z = ∑ c : G.ColorIndex, ∑ a : Axis, ∑ b : Axis,
    ∑ u : Fin j → Axis, Y a b (basis ∘ u) c * Z a b (basis ∘ u) c := by simp [frob,fromF]

lemma component_left (c d : G.ColorIndex) (a b k m : Axis) (u : Fin j → Axis) {x : E4} (hx : x ≠ 0) :
    nth (leftF G d k m) j x a b (basis ∘ u) c = if c=d then coeff (bareCurl a b k m) j x (basis ∘ u) else 0 := by
  rw [← tests_curl _ c a b k m d hx, observed]; rfl

lemma frob_left (Y : TwoJet G.Color j) (c : G.ColorIndex) (k m : Axis) {x : E4} (hx : x ≠ 0) :
    responded G (frob Y) k m x c = ∑ a : Axis, ∑ b : Axis, diffOp (monochrome (G := G) Y c a b) (bareCurl a b k m) x := by
  rw [observed,scalarTest,Function.comp_apply,frob_apply]; simp_rw [component_left _ _ _ _ _ _ _ hx]
  rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c) (fun d _ hd => by simp [hd])]; simp [diffOp,monochrome]

/-- Insertion of the radius vector in first slot. -/
def iota (x : E4) (Y : Axis → Axis → F) (b : Axis) := ∑ a : Axis, x a • Y a b

/-- Tensor action of the normal reflection in two antisymmetric slots. -/
def adjust (x : E4) (Y : Axis → Axis → F) (k m : Axis) :=
  Y k m - (2 * R x) • (x k • iota x Y m - x m • iota x Y k)

def inversion (x : E4) := -(R x • x)

def inverted (Y : Maxwell.Field F) : Maxwell.Field F := fun k m x =>
  (R x)^2 • adjust x (fun a b => Y a b (inversion x)) k m

lemma d_iota (Y : TwoJet ℝ j) (hs : Y ∈ onShell ℝ j) (k m : Axis) (x : E4) :
    let w (i : Axis) (x : E4) := iota x (fun a b => actual Y a b x) i
    grad k (w m) x - grad m (w k) x = (j+2 : ℝ) * actual Y k m x := by
  intro w
  let f := actual Y
  have he a b : grad a (w b) x = f a b x + ∑ i : Axis, x i * grad a (f i b) x := grad_self _ a x
  have h := wave_actual hs
  have ht (a) : grad k (f a m) x - grad m (f a k) x = grad a (f k m) x := by
    have hu := h.cycle k m a x trivial
    change grad k (f m a) x + grad m (f a k) x + _ = 0 at hu
    have hw : grad k (f a m) x = -grad k (f m a) x := by
      rw [show f a m = -f m a from funext fun y => h.form a m y trivial,grad,D,fderiv_neg]; rfl
    rw [hw]; change _ + _ + grad a (f k m) x = 0 at hu; linarith
  rw [he k m, he m k, add_sub_add_comm, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, ht, show f m k x = -f k m x from h.form m k x trivial]
  rw [show ∑ a : Axis, x a * grad a (f k m) x = _ from grad_euler (Y k m) (hs.1.coeffSym k m) x]; simp [f,actual]; ring

lemma diffOp_neg (Y : T E4 ℝ j) (f : E4 → ℝ) (x : E4) : diffOp (-Y) f x = -diffOp Y f x := by
  simp [diffOp,Finset.sum_neg_distrib]
lemma diffOp_sub (Y : T E4 ℝ j) {f g : E4 → ℝ} {x : E4} (hf : smoothAt f x) (hg : smoothAt g x) :
    diffOp Y (f-g) x = diffOp Y f x - diffOp Y g x := by
  unfold diffOp
  have he := coeff_add (g := -g) (j := j) (hf.of_le (allOrders _)) (hg.neg.of_le (allOrders _))
  simp only [sub_eq_add_neg, he,neg_coeff,add_apply,neg_apply, mul_add, Finset.sum_add_distrib, mul_neg,Finset.sum_neg_distrib]

def gain (j : ℕ) : ℝ := (2^j * normal) * (4 * (j+1 : ℝ) * (j+2 : ℝ))
lemma gain_pos : 0 < gain j := by unfold gain; have := normal_pos; positivity

/-- Scalar-color computation of the homogeneous response by differentiating
through the two curls in E's convention. -/
lemma scalar_response (Y : TwoJet ℝ j) (hs : Y ∈ onShell ℝ j) (k m : Axis) {x : E4} (hx : x ≠ 0) :
    ∑ a : Axis, ∑ b : Axis, diffOp (Y a b) (bareCurl a b k m) x = gain j * inverted (actual Y) k m x := by
  let n := j+1
  let c : ℝ := (-2)^j * normal
  let f := actual Y
  let w (b) (x : E4) := iota x (fun a b => f a b x) b
  let S (a b : Axis) := diffOp (Y a b) Green
  have hsS a b {y : E4} (hy : y ≠ 0) := smooth_diffOp (Y a b) (freeSmooth hy)
  have HF := wave_actual hs
  have sw (i) : smoothAt (w i) x := ContDiffAt.sum (fun a _ => (compAxis a).contDiff.contDiffAt.smul (HF.smooth a i x trivial))
  have he (a b : Axis) {y : E4} (hy : y ≠ 0) : S a b =ᶠ[𝓝 y] fun z => c * (R z ^ n * f a b z) := by
    filter_upwards [open_away.mem_nhds hy] with z hz
    exact harmonic_Green (Y a b) (hs.1.coeffSym a b) (fun _ => harmonic_form isOpen_univ HF trivial a b) hz
  have hd (b : Axis) : (fun y => ∑ a : Axis, grad a (S a b) y) =ᶠ[𝓝 x]
      fun y => (-2 * n * c) * (R y ^ (n+1) * w b y) := by
    filter_upwards [open_away.mem_nhds hx] with y hy
    change y ≠ 0 at hy
    have hq (a : Axis) : grad a (S a b) y = c * ((-2 * n * R y ^ (n+1)) * (y a * f a b y) + R y ^ n * grad a (f a b) y) := by
      have hj := (R_smooth hy).pow n
      have hF := HF.smooth a b y trivial
      change smoothAt (f a b) y at hF
      rw [show grad a (S a b) y = grad a (fun z => c * (R z ^ n * f a b z)) y from GermD _ (he a b hy),
        const_grad (hj.mul hF), prod_grad hj hF, R_pow_grad hy]
      ring
    simp_rw [hq, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [show ∑ a, grad a (f a b) y = 0 from HF.divergence b y trivial]
    change c * _ = _; dsimp only [w,iota]; simp only [smul_eq_mul]; ring
  have hopp a b (Y : T E4 ℝ j) : diffOp Y (grad a (curlOpp b k m)) x =
      (if k=b then grad m (grad a (diffOp Y Green)) x else 0) - (if m=b then grad k (grad a (diffOp Y Green)) x else 0) := by
    have hgrad i : grad a (diffOp Y (grad i Green)) x = grad i (grad a (diffOp Y Green)) x := by
      have he : diffOp Y (grad i Green) =ᶠ[𝓝 x] grad i (diffOp Y Green) := by
        filter_upwards [open_away.mem_nhds hx] with y hy
        exact (grad_diffOp Y (freeSmooth hy) i).symm
      exact (GermD _ he).trans (gcomm (smooth_diffOp Y (freeSmooth hx)) ..)
    rw [← grad_diffOp Y (Bare.opp_diff hx b k m), curlOpp]
    have he : diffOp Y ((if k=b then grad m Green else 0) - (if m=b then grad k Green else 0)) =ᶠ[𝓝 x]
        diffOp Y (if k=b then grad m Green else 0) - diffOp Y (if m=b then grad k Green else 0) := by
      filter_upwards [open_away.mem_nhds hx] with y hy
      exact diffOp_sub Y (Bare.choose_diff hy b m k) (Bare.choose_diff hy b k m)
    rw [show grad a (diffOp Y ((if k=b then grad m Green else 0) - (if m=b then grad k Green else 0))) x = _ from GermD (basis a) he]
    change grad a (_ - _) x = _
    rw [Bare.grad_sub (smooth_diffOp Y (Bare.choose_diff hx b m k)) (smooth_diffOp Y (Bare.choose_diff hx b k m))]
    have hz : diffOp Y 0 = fun _ => 0 := by ext y; simp [diffOp,coeff_zero,Pi.zero_def]
    split_ifs <;> simp only [hgrad,hz,show grad a (fun _ : E4 => (0:ℝ)) x = 0 by simp [grad,D]]
  let A (a b : Axis) := diffOp (Y a b) (grad a (curlOpp b k m)) x
  have huv (a b) : diffOp (Y a b) (bareCurl a b k m) x = A a b + A b a := by
    rw [bareCurl,diffOp_sub _ (gsmooth (Bare.opp_diff hx _ _ _) a) (gsmooth (Bare.opp_diff hx _ _ _) b)]
    unfold A
    nth_rw 2 [hs.1.antisymmetric a b]
    rw [diffOp_neg,sub_neg_eq_add]
  simp_rw [huv,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b : Axis => A b a)]
  have hadd a : ∑ b, A a b = grad m (grad a (S a k)) x - grad k (grad a (S a m)) x := by
    simp [A,hopp, Finset.sum_sub_distrib,S]
  let e (i b : Axis) := grad i (fun y => R y ^ (n+1) * w b y) x
  have hrewrite i b : ∑ a, grad i (grad a (S a b)) x = (-2 * n * c) * e i b := by
    rw [← sum_grad (fun a => grad a (S a b)) (fun _ => gsmooth (hsS _ _ hx) _)]
    exact (GermD _ (hd b)).trans (const_grad (((R_smooth hx).pow _).mul (sw b)) _ _)
  rw [Finset.sum_congr rfl (fun a _ => hadd a), Finset.sum_sub_distrib,hrewrite, hrewrite]
  have ht (b m : Axis) : f b m (inversion x) = (-R x)^j * f b m x := by
    rw [inversion, ← neg_smul]; exact Tensor.homogeneous (Y b m) _ _
  have hp i : iota x (fun a b => actual Y a b (inversion x)) i = (-R x)^j * w i x := by
    change (∑ a : Axis, x a * f a i (inversion x)) = _
    dsimp [w,iota]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; rw [ht]; ring
  have heq : grad k (w m) x - grad m (w k) x = (j+2 : ℝ) * f k m x := d_iota Y hs k m x
  change grad k (w m) x - grad m (w k) x = _ at heq
  rw [gain, inverted, adjust, hp, hp, show actual Y k m (inversion x) = (-R x)^j * f k m x from ht k m]
  have he i b : e i b = (-2*(n+1 : ℕ)*R x^(n+2) * x i) * w b x + R x^(n+1) * grad i (w b) x := by
    dsimp only [e]; rw [prod_grad ((R_smooth hx).pow _) (sw _),R_pow_grad hx (n+1)]
  simp only [smul_eq_mul, he,n,c]
  rw [show -R x = (-1)*R x from (neg_one_mul _).symm,mul_pow,show (-2:ℝ) = (-1)*2 by norm_num, mul_pow]
  push_cast; simp only [pow_succ]
  rw [show grad k (w m) x = grad m (w k) x + (j+2 : ℝ) * f k m x by linarith]
  ring

lemma response_eq (Y : Shell G j) (k m : Axis) {x : E4} (hx : x ≠ 0) :
    responded G (frob Y.val) k m x = gain j • inverted (actual Y.val) k m x := by
  ext1 c
  rw [frob_left Y.val c k m hx,scalar_response _ (monochrome_mem Y c) k m hx]
  simp [actual,inverted,adjust,iota,Tensor.diagonal,monochrome]
end YM.Push.FiniteDetection.Kelvin
