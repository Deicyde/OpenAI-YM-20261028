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
import YM.Bid.Fuels
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06
import YM.Work.G05.Taylor

set_option warningAsError false

/-!
# Weighted calculus API – first step towards E polynomial moments

Finitely many weighted summand projections. Show even without picking
colored coords, that total weighted h substitution kills mixed
**iterated** Fréchet moments (not separate Jet weights). Only real vector
spaces; if complexify charge the extraction before or after as licensed
separately. Pure antecedent `evolved` is exactly on all inputs at
once. Doesn't need global analyticity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Weighted
open Function Filter Finset Tensor Work
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {V E F : Type*} [Fintype V] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (Y : V → ℕ) (p : V → E →L[ℝ] E)

def scaled (x : ℝ) (v : E) := ∑ i,x^Y i • p i v
def evolved (y : ℕ) (u : E → F) := ∀ v : E,∀ i,i ≤ y → iteratedDeriv i (fun t => u (scaled Y p t v)) 0 = 0

def heft {i : ℕ} (r : Fin i → V) := ∑ v : Fin i,Y (r v)

/-- Table at fixed arity and fixed substitution engineering. -/
def levy (i d : ℕ) (A : T E F i) : T E F i :=
    ∑ r : Fin i → V, if heft Y r=d then A.compContinuousLinearMap (p ∘ r) else 0

lemma levy_read (i d : ℕ) (A : T E F i) (z : Fin i → E) : levy Y p i d A z =
    ∑ r : Fin i → V, if heft Y r=d then A (fun x => p (r x) (z x)) else 0 := by
  unfold levy; rw [_root_.sum_apply]; apply Finset.sum_congr rfl; intro r _; split_ifs with h <;> rfl

lemma compatible {m : ℕ} {A : T E F m} (h : Sym A) (d : ℕ) : Sym (levy Y p m d A) := by
  intro z s
  simp only [levy_read, Function.comp_apply]
  let φ : Equiv.Perm (Fin m → V) := Equiv.arrowCongr s (Equiv.refl V)
  refine Fintype.sum_equiv φ _ _ fun i => ?_
  have hh (x) : φ i x=i (s.symm x) := rfl
  have hp : heft Y (φ i)=heft Y i := Fintype.sum_equiv s.symm _ _ (fun x => rfl)
  rw [hp]; split; swap; rfl
  let T (x) := p ((φ i) x) (z x)
  refine Eq.trans (congr_arg A ?_) (h T s)
  funext v; simp [T,hh]

lemma block_price {m : ℕ} (A : T E F m) (h : ℝ) (x : E) : diagonal A (scaled Y p h x)=
    ∑ i : Fin m → V,h^(heft Y i) • A (fun j => p (i j) x) := by
  unfold scaled diagonal
  have he := A.toMultilinearMap.map_sum (α:=fun _ => V) (fun _ i => h^Y i • p i x)
  refine he.trans (sum_congr rfl fun i hi => ?_)
  change A (fun j => h^Y (i j) • p (i j) x) = _
  simp only [A.map_smul_univ, Finset.prod_pow_eq_pow_sum,heft]

private lemma smooth (z : F) (m : ℕ) (d : WithTop ℕ∞) : ContDiffAt ℝ d (fun t : ℝ => t^m • z) 0 :=
    (contDiffAt_id.pow _).smul contDiffAt_const

private lemma step (z : F) (m d : ℕ) : iteratedDeriv d (fun t : ℝ => t^m • z) 0 =
    (d.factorial : ℝ) • if m=d then z else 0 := by
  rw [iteratedDeriv_smul_const (contDiffAt_id.pow _),iteratedDeriv_fun_pow_zero]; by_cases h : m=d
  · simp [h]
  simp [h, Ne.symm h]

lemma converse (d : ℕ) {f : E → F} (hp : ∀ v,1 ≤ Y v) (h : evolved Y p d f) (hf : ContDiffAt ℝ d f 0)
    (i m : ℕ) (hi : i ≤ d) (hm : m ≤ d) : levy Y p i m (Tensor.coeff f i 0)=0 := by
  let C (k : ℕ) := Tensor.coeff f k 0
  let R := Finset.range (d+1)
  have he (z : E) : (∑ k∈R, diagonal (levy Y p k m (C k)) z)=0 := by
    let v (t : ℝ) := scaled Y p t z
    have hz : v 0=0 := by simp [v,scaled,fun i => Nat.ne_of_gt (hp i)]
    have hv : ContDiffAt ℝ d v 0 := ContDiffAt.sum (fun i _ => smooth _ _ _)
    let f' := G05.blockTaylor d f
    have hx := G05.jets_comp hv hv (hz.symm ▸ hf) (G05.blockTaylor_contDiff d f _ |>.contDiffAt) rfl (fun _ _ => rfl)
      (fun j hi => by rw [hz]; exact (G05.blockTaylor_jets hf j hi).symm) m hm
    have hh : iteratedDeriv m (fun t => ∑ k∈R, ∑ i : Fin k → V,t^heft Y i • C k (fun j => p (i j) z)) (0:ℝ)=0 := by
      have hT : iteratedDeriv m (f' ∘ v) 0=0 := (congrArg (fun p : T ℝ F m => p (fun _ => 1)) hx.symm).trans (h z _ hm)
      rw [show (fun t => ∑ k∈R, _)=(f' ∘ v) from funext fun t => ?_]; exact hT
      simp only [f',G05.blockTaylor,v,comp_apply,Finset.sum_apply,block_price]
      rfl
    apply smul_right_injective F (show (m.factorial:ℝ)≠0 by positivity)
    simp only [smul_zero,diagonal,levy_read,Finset.smul_sum]
    rw [iteratedDeriv_fun_sum (fun i hi => ContDiffAt.sum fun v _ => smooth _ _ _)] at hh
    simp_rw [iteratedDeriv_fun_sum (fun i hi => smooth _ _ _),step] at hh
    exact hh
  have hD z : diagonal (levy Y p i m (C i)) z=0 := by
    have hx (t : ℝ) : (∑ k∈R, t^k • diagonal (levy Y p k m (C k)) z)=0 := by
      simpa only [homogeneous] using he (t • z)
    have hh := congrArg (fun f : ℝ → F => iteratedDeriv i f 0) (funext hx)
    rw [show iteratedDeriv i (fun t : ℝ => (0:F)) 0=0 from ?_] at hh
    · rw [iteratedDeriv_fun_sum (fun i hi => smooth _ _ _)] at hh; simp_rw [step,← Finset.smul_sum] at hh
      apply smul_right_injective F (show (i.factorial:ℝ)≠0 by positivity)
      simp only [smul_zero]
      simpa only [Finset.sum_ite_eq',Finset.mem_range,R,show i < d+1 from Nat.lt_succ_of_le hi, if_pos] using hh
    exact iteratedDeriv_fun_const_zero
  exact ext_diag _ _ (compatible Y p (coeff_symm (hf.of_le (Nat.cast_le.mpr hi))) m) (fun _ _ => rfl) (funext hD)

/-- Kill all tensors tested at list TOTAL engineering n, where each input
has summands only at or below its engineering weight (`Σ pi (x_i) = x_i`
and min grade ≥1 required). -/
lemma cancel (d : ℕ) {f : E → F} (he : ∀ i,1 ≤ Y i) (hp : ∀ z, (∑ i,p i z)=z) (h : evolved Y p d f) (hf : ContDiffAt ℝ d f 0)
    {m : ℕ} (x : Fin m → E) (k : Fin m → ℕ) (hi : ∀ i,1 ≤ k i) (ht : ∑ i,k i ≤ d) (hh : ∀ i v,k i<Y v → p v (x i)=0) :
    iteratedFDeriv ℝ m f 0 x=0 := by
  have hs : m ≤ d := le_trans (by simpa using sum_le_sum (s:=Finset.univ) (f:=fun _ => 1) fun i _ => hi i) ht
  let R : ℕ → T E F m := fun i => levy Y p m i (Tensor.coeff f m 0)
  have hw (p' : Fin m → V) (hP : d < heft Y p') : ∃ i, k i < Y (p' i) := by
    by_contra! h
    exact (hP.not_ge ((sum_le_sum (fun i _ => h i)).trans ht))
  let A := Tensor.coeff f m 0
  have hq : A x=∑ i∈Finset.range (d+1), R i x := by
    have hx : A x = ∑ i : Fin m → V,A (fun j => p (i j) (x j)) := by
      have hz := A.toMultilinearMap.map_sum (α:=fun _ => V) (fun j i => p i (x j))
      change _=∑ _,_
      simp_rw [hp] at hz; exact hz
    simp_rw [hx,R,levy_read]; rw [Finset.sum_comm]
    refine sum_congr rfl fun i hi => ?_
    by_cases hT : d < heft Y i
    · obtain ⟨j,hj⟩:=hw i hT
      have he : A (fun j => p (i j) (x j))=0 := A.map_coord_zero j (hh _ _ hj)
      change _=∑ v∈Finset.range (d+1), if heft Y i=v then A _ else 0
      simp [he]
    have he : heft Y i < d+1 := by omega
    simp [A,Finset.sum_ite_eq, he]
  have hs' : A x=0 := hq.trans (sum_eq_zero fun i hi => by
    have he : R i=0 := converse Y p d he h hf m i hs (Nat.le_of_lt_succ (mem_range.mp hi))
    rw [he]; rfl)
  apply smul_right_injective F (show (m.factorial:ℝ)⁻¹≠0 by positivity)
  simp only [smul_zero]; exact hs'
end YM.MultiNext.SignedSource.Weighted
