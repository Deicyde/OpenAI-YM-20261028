import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import YM.SNAG.Dense


/-!
# Complete unital orb model into C(Ω)
-/
set_option autoImplicit false
noncomputable section
namespace YM.SNAG
open Function Set Filter Spectral Boundary Probe MeasureTheory Measure Complex
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators ContDiff
variable {H : Hilbert} {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X]

lemma absolute (f : R X) (y : ℝ) (hy : ‖f.val‖ < y) : ∃ η : R X, (↑(y^2):ℂ) • 1 - star f*f=star η * η := by
  have hz := lt_of_le_of_lt (norm_nonneg f.val) hy
  let d (x : OnePoint X) := y^2-‖f.val x‖^2
  have hd x : 0 < d x := sub_pos.mpr ((sq_lt_sq₀ (norm_nonneg _) hz.le).2 ((ContinuousMap.norm_coe_le_norm _ _).trans_lt hy))
  let r : C(OnePoint X,ℂ) := ⟨fun x => ↑(√(d x)),continuous_ofReal.comp (Real.continuous_sqrt.comp
    (continuous_const.sub (f.val.continuous.norm.pow _)))⟩
  have hs : Tail f.val := f.property
  let g (x : X) : ℝ := d x
  have hh : ContDiff ℝ ∞ g := by
    exact contDiff_const.sub ((contDiff_norm_sq ℝ).comp hs.smooth)
  have he : ContDiff ℝ ∞ fun x : X => r x := ofRealCLM.contDiff.comp (hh.sqrt fun x => (hd _).ne')
  let u : R X := ⟨r,show Tail r from ⟨he,hs.quiet.mono fun i hi => by
    change ↑(√(d _))= (↑(√(d _)):ℂ); simp only [d,hi] ⟩⟩
  refine ⟨u,Subtype.ext (ContinuousMap.ext fun x => ?_)⟩
  let t := f.val x
  change ↑(y^2)*(1:ℂ)-star t*t=star (↑(√(d x)):ℂ) * ↑(√(d x))
  rw [mul_one,show star t*t= ↑(‖t‖^2) from by change starRingEnd ℂ _ * _=_; rw [mul_comm,mul_conj,normSq_eq_norm_sq],
    show star _=(↑(√(d x)):ℂ) from conj_ofReal _,← sq,← ofReal_pow, Real.sq_sqrt (hd x).le,← ofReal_sub]

variable [MeasurableSpace X] [BorelSpace X] (S : Orbit H X)

theorem wins (f : R X) : ‖optic S f‖ ≤ ‖f.val‖ := by
  apply le_of_forall_gt_imp_ge_of_dense; intro b hb
  obtain ⟨g,hg⟩ := absolute f b hb
  let t := optic S f
  let u := optic S g
  have he : (↑(b^2):ℂ) • ContinuousLinearMap.id ℂ _-t.adjoint.comp t=u.adjoint.comp u := by
    have hx := congr_arg (optic S) hg
    simp only [map_sub,map_smul,map_one,map_mul,map_star] at hx; exact hx
  apply ContinuousLinearMap.opNorm_le_bound t ((norm_nonneg _).trans hb.le)
  intro v
  have hh := congr_arg (fun z : H.Op => (inner ℂ v (z v)).re) he
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,_root_.smul_apply,
    inner_sub_right,inner_smul_right, ContinuousLinearMap.id_apply,
    sub_re,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero, ContinuousLinearMap.adjoint_inner_right] at hh
  have hi (x : H) : (inner ℂ x x).re=‖x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  simp_rw [hi] at hh
  change ‖t v‖ ≤ _ -- bound by nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (lt_of_le_of_lt (norm_nonneg _) hb).le (norm_nonneg _))).mp
  nlinarith [sq_nonneg ‖u v‖]

abbrev CΩ (X : Type*) [TopologicalSpace X] := C(OnePoint X,ℂ)
def lens : CΩ X →L[ℂ] H.Op := (optic S).toAlgHom.toLinearMap.extendOfNorm embed.toAlgHom.toLinearMap

lemma optic_route (f : R X) : lens S f.val=optic S f :=
  LinearMap.extendOfNorm_eq here ⟨1,fun u => by
    change ‖optic S u‖≤1*‖embed u‖
    rw [one_mul]; exact wins .. ⟩ f

def plots : CΩ X →⋆ₐ[ℂ] H.Op where
  toFun := lens S
  map_mul' := by
    suffices h : ∀ x : CΩ X × CΩ X, lens S (x.1*x.2)=lens S x.1*lens S x.2 from fun p q => h (p,q)
    let A : CΩ X × CΩ X → H.Op := fun p => lens S (p.1*p.2)
    let B : CΩ X × CΩ X → H.Op := fun p => lens S p.1*lens S p.2
    have hw : A=B := by
      apply (here.prodMap here).equalizer ((lens S).continuous.comp continuous_mul)
        ((lens S).continuous.comp continuous_fst |>.mul ((lens S).continuous.comp continuous_snd))
      funext x
      change lens S (embed x.1 * embed x.2) = lens S x.1.val*lens S x.2.val
      rw [← map_mul]; change lens S (x.1*x.2).val = _; rw [optic_route, optic_route, optic_route,map_mul]
    exact congr_fun hw
  map_zero' := map_zero (lens S)
  map_one' := (optic_route S 1).trans (map_one _)
  map_add' := map_add (lens S)
  commutes' c := (optic_route S (algebraMap ℂ (R X) c)).trans ((optic S).commutes c)
  map_star' := by
    intro x
    have ht : (fun y => lens S (star y))=(fun y => star (lens S y)) := by
      apply here.equalizer ((lens S).continuous.comp continuous_star) (continuous_star.comp (lens S).continuous)
      funext x; change lens S (star x).val=star (lens S x.val)
      rw [optic_route, optic_route,map_star]
    exact congr_fun ht x

lemma focuses (t : Probe X) (h : HasCompactSupport ⇑t) : plots S (adds t h).val=send S t := (optic_route S _).trans (in_map ..)
end YM.SNAG
