import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Analysis.Polydisc
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07

set_option warningAsError false

/-!
# The real position filtration to use about an anchor

Using span of exactly homogeneous expressible polynomial functions
(here equivalent to Tensor diagonal via real dilation differentiation
at zero -- so says the same as usual polynomial degree). Doesn't
commit to a p before testing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Powers
open Function Filter Finset Tensor Work
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {V E F X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup X] [NormedSpace ℝ X]

def home (f : V → E) (k : ℕ) := ContDiff ℝ ω f ∧ ∀ (t : ℝ) (v : V), f (t • v) = t^k • f v


lemma tensor_form {k : ℕ} {p : V→ E} (h : home p k) : p = diagonal (Tensor.coeff p k 0) := by
  funext v
  let W : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hw := W.iteratedFDeriv_comp_right h.1 0 (show (k:WithTop ℕ∞) ≤ ω from le_top)
  have hh : (k.factorial:ℝ) • p v=(iteratedFDeriv ℝ k p 0) (fun _ => v) := by
    have ht := congrArg (fun F : T ℝ E k => F (fun _ => 1)) hw
    rw [map_zero] at ht
    change iteratedDeriv k _ 0=(iteratedFDeriv ℝ k p 0) (fun _ => (1:ℝ) • v) at ht
    rw [one_smul, show p ∘ W = (fun t : ℝ => t^k • p v) from funext (fun t => h.2 t v),
        iteratedDeriv_smul_const (contDiffAt_id.pow _), iteratedDeriv_fun_pow_zero] at ht
    simpa using ht
  change _=( (k.factorial:ℝ)⁻¹ • ((iteratedFDeriv ℝ k p 0) _))
  rw [← hh,inv_smul_smul₀ (by positivity)]

/-- Space of polynomial functions of degree ≤k. -/
def space (V E : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :=
    Submodule.span ℝ {f : V → E|∃ i,i ≤ k ∧ home f i}
variable {d k : ℕ} {f f' : V→ E} {g : V→ F}

lemma residence (h : home f k) (hk : k ≤ d) : f∈space V E d := Submodule.subset_span (Set.mem_setOf.mpr ⟨_,hk,h⟩)
lemma constants (x : E) (i : ℕ) : (fun _ : V => x)∈space V E i := residence
    (k:=0) ⟨contDiff_const,fun _ _ => by simp⟩ (Nat.zero_le _)
lemma add (h : f∈space V E k) (hh : f'∈space V E k) : (fun x => f x + f' x) ∈ space V E k := (space ..).add_mem h hh
lemma smul (h : f∈space V E k) (v : ℝ) : (fun x => v • f x) ∈ space V E k := (space ..).smul_mem _ h
lemma sums {i : Type*} (s : Finset i) (R : i→V→E) (h : ∀ j∈s,R j∈space V E k) :
    (fun v => ∑ j∈s,R j v)∈space V E k := by
  rw [← show (∑ j∈s,R j)= (fun v => ∑ j∈s,R j v) from funext fun _ => Finset.sum_apply ..]; exact (space ..).sum_mem h
lemma widen (k d : ℕ) (h : k ≤ d) : space V E k ≤ space V E d :=
  Submodule.span_mono (fun _ ⟨j,hj,hv⟩ => ⟨j,hj.trans h,hv⟩)

lemma next {p : (V→E)→Prop}
    (hi : ∀ f∈({f : V → E|∃ i,i ≤ k ∧ home f i} : Set _), p f) (hz : p 0)
    (ha : ∀ (x y : V→E), p x → p y → p (x+y)) (hs : ∀ (a : ℝ) (x : V→E),p x→p (a • x)) (h : f∈space V E k) : p f :=
  Submodule.span_induction (p:=fun i _ => p i) hi hz (fun x y _ _ => ha x y) (fun a x _ => hs a x) h

lemma carried (Y : E→L[ℝ]F) (h : f ∈ space V E k) : (fun x => Y (f x))∈space V F k := by
  refine next (p:=fun f => (fun x => Y (f x))∈space V F k) (k:=k) ?_ ?_ ?_ ?_ h
  · rintro f ⟨i,hi,hH,h⟩; exact residence ⟨Y.contDiff.comp hH, fun v x => by dsimp only; rw [h v,map_smul]⟩ hi
  · simp only [Pi.zero_apply, map_zero]; exact constants 0 k
  · intro f g h1 h2; simp only [Pi.add_apply,map_add]; exact add h1 h2
  intro a x hx; simp only [Pi.smul_apply,map_smul]; exact smul hx a

lemma genie (Y : E →L[ℝ] F →L[ℝ] X) (h : f∈space V E k) (hg : g∈space V F d) :
    (fun x => Y (f x) (g x))∈space V X (k+d) := by
  let Q (f : V→E) (g : V→F) := (fun x => Y (f x) (g x))∈space V X (k+d)
  refine next (p:=fun f => Q f g) ?_ ?_ ?_ ?_ h
  · rintro f ⟨i,hi,hc⟩
    refine next (p:=Q f) ?_ ?_ ?_ ?_ hg
    · rintro g ⟨j,hj,ht⟩
      exact residence ⟨(Y.contDiff.comp hc.1).clm_apply ht.1,fun t q => by dsimp only; simp only [hc.2,ht.2,map_smul,smul_apply,
        smul_smul, pow_add,mul_comm]⟩ (Nat.add_le_add hi hj)
    · simp only [Q,Pi.zero_apply, map_zero]; exact constants 0 (k+d)
    · intro x y hh hi; simp only [Q,Pi.add_apply,map_add]; exact add hh hi
    intro a x hx; simp only [Q,Pi.smul_apply,map_smul]; exact smul hx a
  · simp only [Q,Pi.zero_apply,map_zero,zero_apply]; exact constants 0 (k+d)
  · intro i j hi hj; simp only [Q,Pi.add_apply,map_add,add_apply]; exact add hi hj
  intro a x hx; simp only [Q,Pi.smul_apply,map_smul,smul_apply]; exact smul hx a

lemma interact {n : ℕ} (P : V → T E F n) (u : Fin n → V→E) (a b : ℕ) (k : Fin n→ℕ)
    (hA : P∈space V (T E F n) a) (h : ∀ i, u i∈space V E (k i)) (hx : a +∑ i,k i ≤ b) : (fun x => P x (fun i => u i x))∈space V F b := by
  induction n generalizing a with
  | zero =>
    have he : a ≤ b := by simpa using hx
    let i : (T E F 0) →L[ℝ] F := ContinuousMultilinearMap.apply ℝ (fun i => E) F (fun _ => 0)
    convert carried i (widen _ _ he hA) using 1; funext x; exact congr_arg (P x) (Subsingleton.elim ..)
  | succ n ih =>
    let Y : T E F (n+1) →L[ℝ] E →L[ℝ] T E F n := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).toContinuousLinearEquiv
    have he := genie Y hA (h 0)
    have ht : a + k 0 + ∑ i,k (i : Fin n).succ ≤ b := by rw [Fin.sum_univ_succ] at hx; omega
    convert ih (fun x => Y (P x) (u 0 x)) (u ∘ Fin.succ) _ (k ∘ Fin.succ) he (fun i => h _) ht using 1
    funext x
    exact congr_arg (P x) (show (fun i => u i x)=Fin.cons (u 0 x) (fun i => u i.succ x) from funext fun i => Fin.cases (by simp) (fun j => by simp) i)

lemma many {n : ℕ} (A : T E F n) (u : Fin n → V→E) (b : ℕ) (k : Fin n→ℕ)
    (h : ∀ i,u i∈space V E (k i)) (hx : ∑ i,k i ≤ b) : (fun x => A (fun i => u i x))∈space V F b :=
  interact (fun _ => A) u 0 b k (constants A 0) h (by rw [zero_add]; exact hx)


end YM.MultiNext.SignedSource.Powers
