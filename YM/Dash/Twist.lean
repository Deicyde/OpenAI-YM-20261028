import Mathlib.Analysis.Distribution.Support
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.IntegralConvolution
import YM.Distribution.Tests
import YM.Euclid.Differential
import YM.Euclid.RPPeak
import YM.Extraction.Orders
import YM.Mink.Geometry
import YM.Source.Insertion
import YM.TimeKernel.Trace


/-!
# Through-ties mechanism I: compactified K decays by all weak derivatives

 via (pure Mathlib Radian? uses 2π here! Only local, cancels by inversion.)
No Sobolev/regularizing dimension assumptions. No contact tests on K; actual
Test only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dash
open Set Filter MeasureTheory Measure Complex Analysis Extraction Boundary
open scoped ContDiff Topology FourierTransform InnerProductSpace BigOperators
variable {n : ℕ}

def down (t : Test n) (i : Fin n) (a : Axis) : Test n := by
  let p := Points.direction i a
  let I := ContinuousLinearMap.apply ℝ ℂ p
  let f := fderiv ℝ ⇑t
  have he : ContDiff ℝ ∞ (I ∘ f) := I.contDiff.comp (t.contDiff.fderiv_right (by exact_mod_cast le_top))
  have hp : tsupport (I ∘ f) ⊆ ↑(patch n) := ((tsupport_comp_subset I.map_zero f).trans (tsupport_fderiv_subset ℝ)).trans t.tsupport_subset
  exact ⟨I ∘ f, he, (t.hasCompactSupport.fderiv ℝ).comp_left I.map_zero, hp⟩
lemma desc (t : Test n) (i : Fin n) (a x) : down t i a x= D (Points.direction i a) t x := rfl

lemma extend (t : Test n) {f : Points n → ℂ} (h : ContDiff ℝ ∞ f) : ∃ v : Test n, ⇑v = fun x => f x*t x := by
  let g (x) := f x*t x
  have hg : Function.support g ⊆ Function.support t := fun i hi hh => hi (by unfold g; rw [show t i=0 from hh]; simp)
  exact ⟨⟨g,h.mul t.contDiff, t.hasCompactSupport.mul_left, (closure_mono hg).trans t.tsupport_subset⟩,rfl⟩

def wave (k x : Points n) := Complex.exp (↑((-2)*Real.pi*inner ℝ x k) * I)
lemma enough (k : Points n) : ContDiff ℝ ∞ (wave k) := ((Complex.ofRealCLM.contDiff.comp
    (show ContDiff ℝ ∞ (fun x : Points n => (-2)*Real.pi*inner ℝ x k) from (contDiff_const.mul (((innerSL ℝ).flip k).contDiff)))).mul contDiff_const).cexp
lemma rate (k : Points n) (p : Fin n) (a : Axis) (x : Points n) : D (Points.direction p a) (wave k) x =
    -I*(↑Probe.q)*↑(k p a)*wave k x := by
  let c := (-Probe.q : ℝ) • (innerSL ℝ k)
  let U := (Complex.ofRealCLM).comp c
  have hx : wave k=(fun i => Complex.exp (U i * I)) := by
    funext i; simp [wave,U,c,Probe.q,real_inner_comm]
  rw [D,hx,show fderiv ℝ _ _ = _ from ((U.hasFDerivAt (x := x)).mul_const I |>.cexp).fderiv]
  have he : inner ℝ k (Points.direction p a) = k p a := by simp [Points.direction,PiLp.inner_apply, PiLp.single_apply,apply_ite]
  simp [U,c,he]; ring

/-- Local integrability of kernels pinned against *all separated compact supports*.
RawLimit measurable/representative after proof. -/
def Loc {n : ℕ} (K : Points n → ℂ) := ∀ f : Test n, Integrable (fun x => f x*K x)

def currents (K H : Points n → ℂ) (i : Fin n) (a : Axis) := ∀ f : Test n,
    f.applyTo H = -(down f i a).applyTo K -- parse minus outside? test

lemma scanned (f : Points n→ℂ) (t : Points n) : 𝓕 f t = ∫ x, wave t x*f x := Real.fourier_eq' ..

lemma controls (K : Points n → ℂ) (h : Loc K) (f : Test n) (k : Points n) : ‖𝓕 (fun x => f x*K x) k‖ ≤ ∫ x, ‖f x*K x‖ := by
  rw [scanned]; apply norm_integral_le_of_norm_le ((h f).norm) (Eventually.of_forall (fun x => by rw [norm_mul, show ‖wave k x‖=1 from by rw [wave,Complex.norm_exp]; simp]; exact le_of_eq (one_mul _)))

lemma iter (K H : Points n → ℂ) (h : Loc K) (p : Fin n) (a : Axis) (hc : currents K H p a)
    (x : Points n) (f : Test n) :
    (I*↑Probe.q*↑(x p a)) * 𝓕 (fun i => f i*K i) x = 𝓕 (fun i => f i*H i) x +
        𝓕 (fun i => down f p a i*K i) x := by
  obtain ⟨y,hy⟩ := extend f (enough x)
  obtain ⟨z,hz⟩ := extend (down f p a) (enough x)
  let g := I*↑Probe.q*↑(x p a)
  have hw : y.applyTo H= - (z.applyTo K-g*y.applyTo K) := by
    rw [hc,Test.applyTo,Test.applyTo,Test.applyTo,← integral_const_mul,← integral_sub (h z) ((h y).const_mul _)]
    congr 2
    funext u
    have ht : down y p a u=wave x u*down f p a u-g*y u := by
      have hh := rate x p a u
      rw [desc,desc,hy,Analysis.D, fderiv_fun_mul]; rotate_left
      · exact ((enough x).differentiable (by simp)) u
      · exact f.contDiff.differentiable (by exact_mod_cast (show (⊤ : ℕ∞)≠0 by simp)) _
      change _=wave x u*Analysis.D (Points.direction p a) f u-g*(wave x u*f u)
      unfold Analysis.D at hh ⊢; simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]; rw [hh]; unfold g;ring
    rw [ht,show z u=wave x u*down f p a u from congr_fun hz u]; ring
  have ht (H : Points n → ℂ) : (𝓕 (fun i => f i*H i) x)=y.applyTo H := by
    rw [scanned,Test.applyTo]; congr! 2
    rename_i u; rw [show y u=_ from congr_fun hy u];simp [mul_assoc]
  rw [ht K,ht H,hw]
  have hv : 𝓕 (fun i => down f p a i*K i) x=z.applyTo K := by
    rw [scanned,Test.applyTo]; congr! 2; rename_i u; rw [show z u=_ from congr_fun hz u]; simp [mul_assoc]
  rw [hv]; unfold g; ring

/-- Compactified polynomial estimate in each coordinate. -/
def Hidden (d : Fin n) (p : Axis) (m : ℕ) (K : Points n → ℂ) := ∀ f : Test n, ∃ A : ℝ, ∀ i : Points n,
    (Probe.q*|i d p|)^m * ‖𝓕 (fun x => f x*K x) i‖ ≤ A

lemma begins (d : Fin n) p (K : Points n→ℂ) (h : Loc K) : Hidden d p 0 K := fun f => ⟨_,fun i => by simpa using controls K h f i⟩
lemma arises (d : Fin n) p m {K H : Points n → ℂ} (h : Loc K)
    (hw : currents K H d p) (hc : Hidden d p m H) (hu : Hidden d p m K) : Hidden d p (m+1) K := by
  intro f
  obtain ⟨A,hA⟩ := hc f
  obtain ⟨B,hB⟩ := hu (down f d p)
  refine ⟨A+B,fun x => ?_⟩
  have he := iter K H h d p hw x f
  let F := 𝓕 (fun i => f i*H i)
  let C := 𝓕 (fun i => down f d p i * K i)
  let G := 𝓕 (fun i => f i*K i)
  let q := Probe.q*|x d p|
  have ht : q*‖G x‖ ≤ ‖F x‖+‖C x‖ := by
    apply le_trans _ (norm_add_le ..)
    change q*‖G x‖ ≤ ‖F x+C x‖
    unfold F C
    rw [← he]; simp [q,abs_of_nonneg Probe.qpos.le,G]
  rw [pow_succ, mul_assoc]; apply (mul_le_mul_of_nonneg_left ht (pow_nonneg (mul_nonneg Probe.qpos.le (abs_nonneg _)) m)).trans
  rw [mul_add]; exact add_le_add (hA _) (hB _)
end YM.Dash
