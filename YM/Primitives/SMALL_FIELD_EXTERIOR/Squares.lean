import YM.Primitives.SMALL_FIELD_EXTERIOR.Identity
import YM.Push.STATIONARY_UNIFORM.Resolvent


/-!
# Positive and conjugated Hessian charges

`R = D Hess D⁻¹` need not be Hermitian; its quadratic coercivity is
what we need for inverse control of the Neumann problem. It's a pointwise
condition on this box; how slow weights can be purchased on the physical
torus is a SEPARATE (off-diagonal) kernel estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior
open Function Set Filter Matrix
open scoped Topology BigOperators ContDiff

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V u : Points ι → ℝ} {w : ι → ℝ} {r m : ℝ}

/-- The Hessian in the actual counting metric, **positive** convention. -/
def curvature (V : Points ι → ℝ) (x : Points ι) : Matrix ι ι ℝ := Matrix.of (fun i j => pc i (pc j V) x)

def Charged (r : ℝ) (V : Points ι → ℝ) (m : ℝ) := ∀ x∈cube ι r, YM.Push.Uniform.Charge (curvature V x) m

def conjugated (w : ι → ℝ) (H : Matrix ι ι ℝ) := Matrix.of (fun i j => w i * H i j * (w j)⁻¹)

def Dirichlet (w : ι → ℝ) (r : ℝ) (V u : Points ι → ℝ) := Real.sqrt (∑ i, w i ^2 * size r V (pc i u)^2)

def adjRow (w : ι → ℝ) (V u : Points ι → ℝ) := ∑ i, w i ^2 • row V i u

lemma curvature_sym {x : Points ι} (hV : ContDiffAt ℝ 2 V x) : (curvature V x).IsHermitian := by
  apply isHermitian_iff_isSymm.mpr
  ext i j; exact pc_comm j i hV

/-- Germ (no price needed for coefficient derivatives outside cube). -/
lemma curvature_smul {x : Points ι} (hV : ContDiffAt ℝ 2 V x) (c : ℝ) : curvature (c • V) x=c • curvature V x := by
  ext i j
  have he : pc j (c • V)=ᶠ[𝓝 x] c • pc j V := by
    filter_upwards [hV.eventually (by norm_num)] with y hy
    exact pc_smul _ c (hy.differentiableAt two_ne_zero)
  change pc i (pc j (c • V)) x = c • pc i (pc j V) x
  rw [show pc i (pc j (c • V)) x = pc i (c • pc j V) x from congr_arg (fun L : Points ι →L[ℝ] ℝ => L (Pi.single i 1)) he.fderiv_eq,
    pc_smul i c ((pcat j hV (k:=1) (by norm_num)).differentiableAt one_ne_zero), smul_eq_mul]

lemma Charged.drop (h : Charged r V m) {m'} (hm : m' ≤ m) : Charged r V m' :=
  fun x hx v => (mul_le_mul_of_nonneg_right hm (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans (h x hx v)
lemma Charged.smul (h : Charged r V m) (hV : Regular r 2 V) (t : ℝ) (ht : 0≤t) : Charged r (t • V) (t*m) := by
  intro x hx v
  rw [curvature_smul (hV x hx), smul_mulVec,dotProduct_smul,smul_eq_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x hx v) ht
lemma dirichlet_sq (w : ι → ℝ) (r : ℝ) (V u : Points ι → ℝ) :
    Dirichlet w r V u ^ 2 = ∑ i, w i ^2 * size r V (pc i u)^2 := Real.sq_sqrt (by positivity)
lemma dirichlet_nn (w : ι → ℝ) (r : ℝ) (V u : Points ι → ℝ) : 0 ≤ Dirichlet w r V u := Real.sqrt_nonneg _
omit [Fintype ι] [DecidableEq ι] in
lemma conjugated_one (H : Matrix ι ι ℝ) : conjugated (1 : ι → ℝ) H = H := by ext; simp [conjugated]
lemma adjRow_one (V u : Points ι → ℝ) : adjRow (1 : ι → ℝ) V u=elliptic V u := by simp [adjRow,elliptic]

private lemma matrix_cost (hu : Neumann r u) (hV : Regular r 2 V) (hw : ∀ i, w i ≠ 0)
    (hh : ∀ x∈cube ι r, YM.Push.Uniform.Charge (conjugated w (curvature V x)) m) :
    m*Dirichlet w r V u ^2 ≤ ∑ i, w i^2 * ∑ j, bracket r V (pc i (pc j V) * pc j u) (pc i u) := by
  let F i := w i ^ 2 • (pc i u * pc i u)
  let H i j := pc i (pc j V) * pc j u * pc i u
  have hc i : ContinuousOn (pc i u) (cube ι r) := (hu.stripe (n:=1) i).cOn
  have hf i : ContinuousOn (F i) (cube ι r) := continuousOn_const.smul ((hc i).mul (hc i))
  have hg i j : ContinuousOn (H i j) (cube ι r) := (((hV.tangent j).tangent_continuous i).mul (hc j)).mul (hc i)
  have sumC (f : ι → Points ι → ℝ) (hi : ∀ i, ContinuousOn (f i) (cube ι r)) :
      ContinuousOn (∑ i, f i) (cube ι r) := by
    rw [show ∑ i, f i= fun x => ∑ i, f i x from funext (fun x => Finset.sum_apply ..)]
    exact continuousOn_finsetSum _ fun i _ => hi i
  let L : Points ι → ℝ := m • ∑ i, F i
  let R : Points ι → ℝ := ∑ i, w i^2 • ∑ j, H i j
  have he (x : Points ι) (hx : x∈cube ι r) : L x ≤ R x := by
    let W (i : ι) := w i*pc i u x
    have hi : L x = m*∑ i, W i^2 := by simp only [W,L,F, mul_pow, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.mul_apply]; simp only [pow_two]
    have hk i j : W i * ((conjugated w (curvature V x)) i j * W j) = w i^2 * H i j x := by
      simp only [W,conjugated, Matrix.of_apply,H,curvature, Pi.mul_apply]; field_simp [hw j]
    rw [hi]; apply le_trans (hh x hx W) _
    unfold dotProduct mulVec R
    simp only [dotProduct, Finset.sum_apply, Pi.smul_apply,smul_eq_mul,Finset.mul_sum,hk,le_refl]
  have ht := raw_mono hV.cOn (f:=L) (g:=R) (continuousOn_const.smul (sumC _ hf))
    (sumC _ fun i => continuousOn_const.smul (sumC _ (hg i))) he
  have hr (i : ι) : ContinuousOn (w i^2 • ∑ j, H i j) (cube ι r) := continuousOn_const.smul (sumC _ (hg i))
  have hi (i : ι) : raw r V (∑ j, H i j)= ∑ j, raw r V (H i j) := raw_sum hV.cOn _ (fun j _ => hg _ _)
  unfold L R at ht
  rw [raw_smul, raw_sum hV.cOn _ (fun i _ => hf i), raw_sum hV.cOn _ (fun i _ => hr i)] at ht
  simp_rw [raw_smul,F,raw_smul,hi] at ht
  simp_rw [dirichlet_sq,size_sq]
  exact ht

/-- Estimate before inversion. Nonnegative second partial charges *also*
retained, used in the PDE argument. -/
theorem squares (hr : 0 ≤ r) (hu : Neumann r u) (hV : Regular r 2 V) (hw : ∀ i, w i ≠ 0)
    (hh : ∀ x∈cube ι r, YM.Push.Uniform.Charge (conjugated w (curvature V x)) m) :
    (∑ i, w i^2 * ∑ j, size r V (pc j (pc i u))^2)+m*Dirichlet w r V u^2 ≤
      bracket r V (adjRow w V u) (elliptic V u) := by
  have hi (i) : ContinuousOn (row V i u) (cube ι r) := (hu.row1 hV i).cOn
  have hg (i) : ContinuousOn (w i^2 • row V i u) (cube ι r) := continuousOn_const.smul (hi i)
  apply (add_le_add (le_refl _) (matrix_cost hu hV hw hh)).trans
  unfold adjRow
  rw [bracket_sum hV.cOn _ (fun i _ => hg i) (hu.elliptic1 hV).cOn]
  rw [← Finset.sum_add_distrib]
  refine Eq.le (Finset.sum_congr rfl fun i _ => ?_)
  rw [bracket_smul, bracket_sym r V (row V i u), elliptic, bracket_sum hV.cOn _ (fun j _ => hi j) (hi i)]
  conv_rhs => arg 2; arg 2; ext j; rw [bracket_sym r V (row V j u), hu.cross hr hV i j]
  rw [Finset.sum_add_distrib,mul_add]

lemma second_budget (hr : 0 ≤ r) (hu : Neumann r u) (hV : Regular r 2 V) (hh : Charged r V 0) (i j : ι) :
    size r V (pc j (pc i u)) ≤ size r V (elliptic V u) := by
  have he : (∑ i, ∑ j, size r V (pc j (pc i u))^2) ≤ size r V (elliptic V u)^2 := by
    have ht := squares hr hu hV (w:=(1:Points ι)) (fun i => one_ne_zero) (m:=0) (fun x hx => by rw [conjugated_one]; exact hh x hx)
    simpa only [size_sq,Pi.one_apply,one_pow,one_mul,zero_mul,add_zero,adjRow_one] using ht
  apply (sq_le_sq₀ (size_nn ..) (size_nn ..)).mp
  apply le_trans _ he
  exact (Finset.single_le_sum (f:=fun j => size r V (pc j (pc i u))^2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f:=fun i => ∑ j, size r V (pc j (pc i u))^2) (fun j _ => by positivity) (Finset.mem_univ i))
lemma weighed (hr : 0 ≤ r) (hu : Neumann r u) (hV : Regular r 2 V) (hw : ∀ i, w i ≠ 0)
    (hh : ∀ x∈cube ι r, YM.Push.Uniform.Charge (conjugated w (curvature V x)) m) :
    m*Dirichlet w r V u^2 ≤ bracket r V (adjRow w V u) (elliptic V u) := le_trans (le_add_of_nonneg_left (by positivity))
  (squares hr hu hV hw hh)
end YM.Primitives.SmallFieldExterior
