import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.A15
import YM.Work.B06

/-!
# Ordered polarizations of real germ derivatives

Lists for external labels when positions repeat (or different test
directions used at a single field); partition the occurrences not the labels.
In log charts use ordinary Fréchet calculus with ordered fixed directions,
a legitimate coordinate convention for . Jets here are derivatives,
no factorial. No neighborhood/ContDiff assumptions inferred from mere bounds
on directional values.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Matrix Filter Function Topology
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

namespace TestD
variable {τ : Type*}
/-- occurrences routed to the left or right, in-place -/
abbrev Masks : List τ → Type
  | [] => Unit
  | _ :: t => Masks t ⊕ Masks t

instance masksFin : (l : List τ) → Fintype (Masks l)
  | [] => inferInstanceAs (Fintype Unit)
  | _::l => @instFintypeSum _ _ (masksFin l) (masksFin l)
instance masksDec : (l : List τ) → DecidableEq (Masks l)
  | [] => inferInstanceAs (DecidableEq Unit)
  | _::l => @instDecidableEqSum _ _ (masksDec l) (masksDec l)

def lo : (l : List τ) → Masks l → List τ
  | [], _ => []
  | a::l, .inl m => a::lo l m
  | _::l, .inr m => lo l m

def hi : (l : List τ) → Masks l → List τ
  | [], _ => []
  | _::l, .inl m => hi l m
  | a::l, .inr m => a::hi l m

def pureR : (l : List τ) → Masks l
  | [] => ()
  | _::l => .inr (pureR l)
@[simp] lemma hi_right (l : List τ) : hi l (pureR l)=l := by induction l <;> simp [hi,pureR, *]
@[simp] lemma lo_right (l : List τ) : lo l (pureR l)=[] := by induction l <;> simp [lo,pureR, *]
lemma lo_ne : ∀ {l : List τ} {m : Masks l}, m ≠ pureR l → lo l m ≠ []
  | [], (),h => False.elim (h rfl)
  | a::l,.inl m,_ => List.cons_ne_nil _ _
  | a::l,.inr m,h => by rw [lo]; exact lo_ne (fun he => h (congr_arg Sum.inr he))
lemma lengths : ∀ (l : List τ) (m : Masks l), (lo l m).length+(hi l m).length=l.length
  | [], () => rfl
  | a::l,.inl m => by rw [lo,hi,List.length_cons]; have := lengths l m; simp; omega
  | a::l,.inr m => by rw [lo,hi,List.length_cons]; have := lengths l m; simp; omega
lemma len_low (l : List τ) (m : Masks l) : (lo l m).length ≤ l.length := by have := lengths l m; omega
lemma len_high (l : List τ) (m : Masks l) : (hi l m).length ≤ l.length := by have := lengths l m; omega
lemma card (l : List τ) : Fintype.card (Masks l) = 2^l.length := by
  induction l with
  | nil => simp [Masks]
  | cons i l ih =>
    change Fintype.card (Masks l ⊕ Masks l) = _; rw [Fintype.card_sum, ih,List.length_cons,pow_succ]; omega

lemma masks_sum {X : Type*} [AddCommMonoid X] (i : τ) (l : List τ) (F : Masks (i::l) → X) :
    (∑ k : Masks (i::l), F k) = (∑ k : Masks l, F (.inl k)) + ∑ k : Masks l, F (.inr k) :=
  Fintype.sum_sum_type _

section calculus
variable {E F H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G]

variable (v : τ → E) {A B : E → F} {x : E}

def jet (A : E → F) (l : List τ) (x : E) : F := iteratedFDeriv ℝ l.length A x (v ∘ l.get)

lemma identical (h : A =ᶠ[𝓝 x] B) (l : List τ) : jet v A l x = jet v B l x := by
  unfold jet; rw [(h.iteratedFDeriv ..).eq_of_nhds]
lemma jet_add (l : List τ) (hf : ContDiffAt ℝ l.length A x) (hg : ContDiffAt ℝ l.length B x) :
    jet v (fun x => A x + B x) l x = jet v A l x + jet v B l x := by
  unfold jet; rw [fun_iteratedFDeriv_add_apply hf hg]; rfl
lemma jet_sub (l : List τ) (hf : ContDiffAt ℝ l.length A x) (hg : ContDiffAt ℝ l.length B x) :
    jet v (fun x => A x - B x) l x = jet v A l x - jet v B l x := by
  unfold jet; change (iteratedFDeriv ℝ l.length (A-B) x) _ = _; rw [iteratedFDeriv_sub_apply hf hg]; rfl
lemma jet_linear (l : List τ) (L : F →L[ℝ] H) (h : ContDiffAt ℝ l.length A x) :
    jet v (fun x => L (A x)) l x = L (jet v A l x) := by
  unfold jet; change (iteratedFDeriv ℝ l.length (L ∘ A) x) _ = _; rw [L.iteratedFDeriv_comp_left h le_rfl]; rfl
lemma jet_sum {ι : Type*} (l : List τ) (t : Finset ι) (C : ι → E → F) (h : ∀ i ∈ t, ContDiffAt ℝ l.length (C i) x) :
    jet v (fun x => ∑ i ∈ t, C i x) l x = ∑ i ∈ t, jet v (C i) l x := by
  unfold jet; rw [iteratedFDeriv_fun_sum_apply h,_root_.sum_apply]
lemma zeroth (A : E → F) (x : E) : jet v A [] x=A x := iteratedFDeriv_zero_apply ..
lemma jet_const (l : List τ) (h : l≠[]) (z : F) (x : E) : jet v (fun _ : E => z) l x=0 := by
  cases l; · contradiction
  simp [*,jet, iteratedFDeriv_succ_const]
lemma smooth_of_le {n m : ℕ} (h : ContDiffAt ℝ m A x) (hm : n ≤ m) : ContDiffAt ℝ n A x := h.of_le (by exact_mod_cast hm)
lemma jet_diff (l : List τ) (h : ContDiffAt ℝ (↑(l.length+1):ℕ∞ω) A x) : DifferentiableAt ℝ (jet v A l) x := by
  have he := h.differentiableAt_iteratedFDeriv (m:=l.length) (by exact_mod_cast Nat.lt_succ_self l.length)
  exact he.continuousMultilinear_apply_const _
lemma jet_step (i : τ) (l : List τ) (h : ContDiffAt ℝ (↑(l.length+1):ℕ∞ω) A x) :
    jet v A (i::l) x=fderiv ℝ (jet v A l) x (v i) := by
  have he := h.differentiableAt_iteratedFDeriv (m:=l.length) (by exact_mod_cast Nat.lt_succ_self l.length)
  exact he.iteratedFDeriv_succ_apply_left' (m:= v ∘ (i::l).get)

lemma smooth_product (p : F →L[ℝ] G →L[ℝ] H) {n} {B : E → G}
    (h : ContDiffAt ℝ n A x) (hh : ContDiffAt ℝ n B x) : ContDiffAt ℝ n (fun x => p (A x) (B x)) x :=
  (p.contDiff.contDiffAt.comp x h).clm_apply hh

lemma leibniz (p : F →L[ℝ] G →L[ℝ] H) {B : E → G} (l : List τ)
    (hf : ContDiffAt ℝ l.length A x) (hg : ContDiffAt ℝ l.length B x) :
    jet v (fun x => p (A x) (B x)) l x = ∑ m : Masks l, p (jet v A (lo l m) x) (jet v B (hi l m) x) := by
  induction l generalizing x with
  | nil =>
    rw [zeroth]; change _ = ∑ m : Unit, p (jet v A [] x) (jet v B [] x)
    simp [zeroth]
  | cons i l ih =>
    let P (m : Masks l) (x : E) := p (jet v A (lo l m) x) (jet v B (hi l m) x)
    have HA m := smooth_of_le (n:=(i::lo l m).length) hf (by simp [len_low])
    have HB m := smooth_of_le (n:=(i::hi l m).length) hg (by simp [len_high])
    have he : jet v (fun x => p (A x) (B x)) l =ᶠ[𝓝 x] fun y => ∑ m, P m y := by
      filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hy hh
      exact ih (smooth_of_le hy (by simp)) (smooth_of_le hh (by simp))
    have h (m : Masks l) : DifferentiableAt ℝ (P m) x :=
      (p.hasFDerivAt_of_bilinear (jet_diff v (lo l m) (HA m)).hasFDerivAt
        (jet_diff v (hi l m) (HB m)).hasFDerivAt).differentiableAt
    have hq := HasFDerivAt.fun_sum (u:=Finset.univ) fun m _ => (h m).hasFDerivAt
    rw [jet_step v _ _ (smooth_product p hf hg), he.fderiv_eq,hq.fderiv,_root_.sum_apply, masks_sum i l, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold P; rw [(p.hasFDerivAt_of_bilinear (jet_diff v (lo l m) (HA m)).hasFDerivAt
        (jet_diff v (hi l m) (HB m)).hasFDerivAt).fderiv,_root_.add_apply]
    change _ = p (jet v A (i :: lo l m) x) (jet v B (hi l m) x) + p (jet v A (lo l m) x) (jet v B (i :: hi l m) x)
    rw [jet_step v _ _ (HA m),jet_step v _ _ (HB m)]; exact add_comm _ _
end calculus

-- matrices are rectangular; Frobenius merely topology here.
section Matrix
variable {ι κ μ E : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

def times : Matrix ι κ ℝ →L[ℝ] Matrix κ μ ℝ →L[ℝ] Matrix ι μ ℝ := LinearMap.toContinuousLinearMap
  (LinearMap.toContinuousLinearMap.toLinearMap.comp (LinearMap.mk₂ ℝ (fun x y => x*y)
    Matrix.add_mul (fun _ _ _ => Matrix.smul_mul ..) Matrix.mul_add (fun _ _ _ => Matrix.mul_smul ..)))

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {A : E → Matrix ι κ ℝ} {B : E → Matrix κ μ ℝ}
variable (v : τ → E) {x : E}
lemma prod_smooth {n : ℕ∞ω} (hf : ContDiffAt ℝ n A x) (hg : ContDiffAt ℝ n B x) :
    ContDiffAt ℝ n (fun x => A x * B x) x := smooth_product times hf hg
lemma jet_mul (l : List τ) (hf : ContDiffAt ℝ l.length A x) (hg : ContDiffAt ℝ l.length B x) :
    jet v (fun x => A x * B x) l x = ∑ m : Masks l, jet v A (lo l m) x * jet v B (hi l m) x := leibniz v times _ hf hg

def evaluate (i : ι) (j : κ) : Matrix ι κ ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  ({ toFun := fun (A : Matrix ι κ ℝ) => A i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }: Matrix ι κ ℝ →ₗ[ℝ] ℝ)
lemma entry (l : List τ) (hf : ContDiffAt ℝ l.length A x) (i j) :
    jet v (fun x => A x i j) l x = jet v A l x i j := jet_linear v l (evaluate i j) hf
end Matrix
end TestD
end YM.FreeResolvent
