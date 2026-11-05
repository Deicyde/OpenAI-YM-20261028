import YM.Extra.WILSON_STARTUP.Overlay
import YM.Laurent.Art
import YM.Work.F07.Read

/-!
# Real exponential rows for an inverse shifted Gram matrix, uniform in input

Application: align any supplied real top root (need not be a positive square
root).

Here need
only the inverse gram of z = full metric column stack plus upper identity.

Work first in the fixed number of column types at real momentum with entrywise
conjugation (not Hermiticity postulated away from the real slice!), then on a
strip whose width and symbol bounds are chosen uniformly before L.

This is a
LIBRARY estimate with assumptions, no loops solution.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Polar
open Matrix Function Filter Lattice Bloch Laurent Work Work.F07
open scoped Matrix.Norms.Frobenius ComplexOrder Topology BigOperators
variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev Column (ι : Type) := ι → ι → ℂ
abbrev Region (ι : Type) := Column ι × Column ι
abbrev Square (ι : Type) := Matrix ι ι ℂ
abbrev into : Column ι ≃L[ℂ] Square ι := (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv

def boost (r : ℝ) (X : Region ι) : Square ι := (r:ℂ) • 1 + (of X.2).transpose * of X.1

def invert (r : ℝ) (X : Region ι) : Square ι := Ring.inverse (boost r X)

lemma boost_unit (r : ℝ) (hr : 0<r) (X : Column ι) : IsUnit (boost r (X,star X)) := by
  have h : (boost r (X,star X)).PosDef := Matrix.PosDef.add_posSemidef
    (Matrix.PosDef.one.smul (show (0:ℂ)<r by exact_mod_cast hr)) (posSemidef_conjTranspose_mul_self (of X))
  rw [Matrix.isUnit_iff_isUnit_det]; exact IsUnit.mk0 _ h.det_pos.ne'

lemma boost_diff (r : ℝ) : Differentiable ℂ (boost r (ι:=ι)) := by
  let e : Region ι →ₗ[ℂ] Column ι := LinearMap.pi (fun i => LinearMap.pi fun j => LinearMap.proj i ∘ₗ LinearMap.proj j ∘ₗ LinearMap.snd ℂ _ _)
  exact differentiable_const _ |>.add ((into.differentiable.comp e.toContinuousLinearMap.differentiable).mul ((into (ι:=ι)).differentiable.comp (f:=Prod.fst (β:=Column ι)) differentiable_fst))

lemma inv_diff (r : ℝ) {X : Region ι} (h : IsUnit (boost r X)) : DifferentiableAt ℂ (invert r) X :=
  (analyticAt_inverse (𝕜:=ℂ) h.unit).differentiableAt.comp (f:=boost r) X (boost_diff r X)

def domain (ι : Type) [Fintype ι] (A : ℝ) := (fun x : Column ι => (x,star x)) '' (Metric.closedBall 0 A)

variable (ι)

theorem invest (r A : ℝ) (hr : 0 < r) : ∃ b δ : ℝ, 0 < δ ∧
    ∀ X ∈ Metric.cthickening δ (domain ι A), IsUnit (boost r X) ∧ ∀ i j, ‖invert r X i j‖ ≤ b := by
  have h := (isCompact_closedBall (0:Column ι) A).image (continuous_id.prodMk continuous_id.star)
  change IsCompact (domain ι A) at h
  obtain ⟨δ,hδ,he⟩ := h.exists_cthickening_subset_open (t:={X | (boost r X).det ≠ 0}) (isOpen_ne_fun (boost_diff r).continuous.matrix_det continuous_const) (by
    rintro _ ⟨x,-,rfl⟩; exact (Matrix.isUnit_iff_isUnit_det _ |>.mp (boost_unit r hr x)).ne_zero)
  have hh {X : Region ι} (hx : X ∈ Metric.cthickening δ (domain ι A)) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (he hx) : IsUnit (boost r X).det)
  let f : Region ι → Column ι := fun X => into.symm (invert r X)
  have hf : ContinuousOn f (Metric.cthickening δ (domain ι A)) := fun x hx =>
    (into.symm.continuous.continuousAt.comp (inv_diff r (hh hx)).continuousAt).continuousWithinAt
  obtain ⟨b,hb⟩ := h.cthickening.bddAbove_image hf.norm
  refine ⟨b,δ,hδ,fun x hx => ⟨hh hx,fun i j => ?_⟩⟩
  exact ((norm_le_pi_norm (f x i) j).trans (norm_le_pi_norm (f x) i)).trans (hb ⟨x,hx,rfl⟩)

variable {ι}

def param (P : Row ι ι) (v : Momentum) : Region ι := (into.symm (P.read v),into.symm (P.read (-v)))

-- near-real-axis bounds, entrywise Pi not dimension-weighted
omit [DecidableEq ι] in
lemma near (P : Row ι ι) {v : Momentum} {A σ η : ℝ} (hP : P.strip η A) (hA : 0 ≤ A) (hσ : 0 < σ) (ht : σ ≤ η/2)
    (hv : v∈strip σ) : param P v ∈ Metric.cthickening ((η/2)⁻¹*A*σ) (domain ι A) := by
  let q : Momentum := fun i => (v i).re
  have hη : 0 < η/2 ∧ η/2 < η := by constructor <;> linarith
  have hq : star q = q := by funext i; simp [q]
  have hv' : v ∈ strip (η/2) := fun i => (hv i).trans_le ht
  have hb : ‖v-q‖ ≤ σ := by
    refine pi_norm_le_iff_of_nonneg hσ.le |>.mpr fun i => ?_
    have he : v i - q i = ((v i).im:ℂ)*Complex.I := by apply Complex.ext <;> simp [q]
    simpa only [Pi.sub_apply, he, norm_mul, Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] using (hv i).le
  have he (w p : Momentum) (hw : w ∈ strip (η/2)) (hp : star p = p) (h : ‖w-p‖ ≤ σ) :
      dist (into.symm (P.read w)) (into.symm (P.read p)) ≤ (η/2)⁻¹ * A * σ := by
    obtain ⟨hy,hH⟩ := hη
    have hn : 0 ≤ (η/2)⁻¹ * A * σ := by positivity
    rw [dist_eq_norm]; refine (pi_norm_le_iff_of_nonneg hn).mpr fun i => (pi_norm_le_iff_of_nonneg hn).mpr fun j => ?_
    have he := readDiff (Row.constant_strip _ hP i j) hy hH hw (realStrip _ hy hp)
    rw [show η - η/2 = η/2 by ring] at he
    exact he.trans (mul_le_mul_of_nonneg_left h (by positivity))
  refine Metric.mem_cthickening_of_dist_le _ (param P q) _ _ ?_ ?_
  · refine ⟨(param P q).1,Metric.mem_closedBall.mpr ?_,?_⟩
    · rw [dist_zero_right]; refine (pi_norm_le_iff_of_nonneg hA).mpr fun i => (pi_norm_le_iff_of_nonneg hA).mpr fun j => ?_
      have hh := (P.constant_strip hP i j).series q (fun a => (realStrip η (by linarith) hq a).le)
      exact (norm_tsum_le_tsum_norm hh.2.1).trans hh.2.2
    unfold param; simp only [← show (P.read q).map star = P.read (-q) by simpa [hq] using (P.conjugate q).symm]; rfl
  rw [Prod.dist_eq]; exact max_le (he v q hv' hq hb) (he (-v) (-q) (fun i => by simpa using! hv' i) (by rw [star_neg,hq])
    (by rwa [neg_sub_neg,norm_sub_rev]))

lemma invest_params (r η A : ℝ) (hr : 0<r) (hη : 0<η) (hA : 0 ≤ A) : ∃ b σ : ℝ, 0 < σ ∧ σ < η ∧
    ∀ P : Row ι ι,P.strip η A → ∀ v ∈ strip σ, IsUnit (boost r (param P v)) ∧ ∀ i j, ‖invert r (param P v) i j‖ ≤ b := by
  obtain ⟨b,δ,hδ,h⟩ := invest ι r A hr
  let m := (η/2)⁻¹*A + 1
  have hM : 0 < m := by unfold m; positivity
  let σ := min (η/2) (δ/m)
  have hs : 0<σ := lt_min (half_pos hη) (by positivity)
  have he : σ≤η/2 := min_le_left ..
  refine ⟨b,σ,hs, he.trans_lt (by linarith),fun P hP v hv => h _ (Metric.cthickening_mono ?_ _ (near P hP hA hs he hv))⟩
  calc
    _ ≤ σ*m := by unfold m; linarith
    _ ≤ δ := (le_div_iff₀ hM).mp (min_le_right ..)

omit [DecidableEq ι] in
lemma param_diff {P : Row ι ι} {σ η A : ℝ} {v : Momentum} (hP : P.strip η A) (hs : 0 < σ) (hη : σ < η) (hv : v ∈ strip σ) :
    DifferentiableAt ℂ (param P) v := by
  have he (p) (hp : p∈strip σ) : DifferentiableAt ℂ (fun w => (param P w).1) p := differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr
    fun j => (readDeriv (Row.constant_strip _ hP i j) hs hη hp).1
  exact (he v hv).prodMk ((he (-v) (fun i => by simpa using! hv i)).comp v differentiableAt_id.neg)

omit [DecidableEq ι] in
lemma param_periodic (P : Row ι ι) (v : Momentum) (x : Cover) : param P (v + reciprocal x) = param P v := by
  have he : reciprocal (-x) = -(reciprocal x) := by ext1 i; simp [reciprocal]
  rw [param, P.periods, neg_add, ← he, P.periods]; rfl

lemma invert_conjugate (r : ℝ) (X : Region ι) : invert r (star X) = (invert r X).map star := by
  have e (x : Square ι) : x.map star = x.conjTranspose.transpose := rfl
  have hs : boost r (star X) = (boost r X).map star := by
    rw [e]; simp only [boost,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,Matrix.conjTranspose_one,Matrix.transpose_add,
      Matrix.transpose_smul,Matrix.transpose_one,Matrix.conjTranspose_mul,Matrix.transpose_mul,Complex.star_def,Complex.conj_ofReal]; rfl
  rw [invert, hs, invert,e,e, ← Matrix.nonsing_inv_eq_ringInverse,← Matrix.nonsing_inv_eq_ringInverse, conjTranspose_nonsing_inv,transpose_nonsing_inv]

omit [DecidableEq ι] in
lemma param_conjugate (P : Row ι ι) (v : Momentum) (hv : star v = v) : param P (-v)=star (param P v) := by
  have he (p : Momentum) (hp : star p=p) : P.read (-p) = (P.read p).map star := by
    rw [← P.conjugate,hp]
  unfold param
  rw [he (-v) (by rw [star_neg,hv])]
  nth_rw 1 [he v hv]
  rfl

lemma writes (r η A : ℝ) (hr : 0<r) (hη : 0<η) (hA : 0≤A) : ∃ C τ : ℝ, 0 < τ ∧ 0 ≤ C ∧ ∀ P : Row ι ι,
    P.strip η A → ∃ S : Row ι ι, S.strip τ C ∧ ∀ v : Momentum,star v=v → S.read v=invert r (param P v) := by
  obtain ⟨b,σ,hs,hσ,h⟩ := invest_params (ι:=ι) _ _ _ hr hη hA
  let τ := σ/3
  have he : 0 < τ ∧ τ+τ < σ := ⟨by unfold τ; positivity, by unfold τ; linarith⟩
  let c := b*(2*((1+τ)/τ))^ Fintype.card Axis
  refine ⟨max 0 c,τ,he.1,le_max_left ..,fun P hP => ?_⟩
  let f := fun i j v => invert r (param P v) i j
  have hV i j : Vane (f i j) σ := by
    refine ⟨hs,fun p hp => ?_,fun p _ x => by simp only [f,param_periodic]⟩
    have hy := (inv_diff r (h P hP p hp).1).comp p (param_diff hP hs hσ hp)
    exact differentiableAt_pi.mp (differentiableAt_pi.mp (into.symm.differentiableAt.comp p hy) i) j
  have hh i j p hp := (h P hP p hp).2 i j
  have hw i j : Width τ c (market (f i j) 0) := (hV i j).issues (hh i j) τ τ he.1.le he.1 he.2
  let S : Row ι ι := fun i j x => (market (f i j) 0 x).re
  refine ⟨S,fun i j => (widthRealPart (hw i j)).mono le_rfl (le_max_right ..),fun v hv => ?_⟩
  ext i j
  have hQ : star (f i j (-v)) = f i j v := by simp only [f,param_conjugate P v hv,invert_conjugate,map_apply,star_star]
  change Laurent.read _ v = f i j v
  rw [readRealPart (hw i j) he.1 hv,(hV i j).paints (hh i j) v (realStrip _ hs hv),
    (hV i j).paints (hh i j) (-v) (realStrip _ hs (by rw [star_neg,hv])),hQ]
  ring
end YM.WilsonStartup.Polar
