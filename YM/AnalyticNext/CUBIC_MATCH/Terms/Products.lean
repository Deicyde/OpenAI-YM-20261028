import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Liouville
import YM.AnalyticNext.CUBIC_MATCH.Rays
import YM.Pressure.Seeds

set_option warningAsError false

/-!
# Line terms under bilinear operations and repeated products

For extracting terms on the actual torus before making estimates on their
translation-summed norms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Filter Function RG Precision Wilson Lattice Tree Exterior
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius

variable {E F Z T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedRing T] [NormedAlgebra ℝ T]

section bilin
variable (L : E →L[ℝ] F →L[ℝ] Z) {f : ℝ → E} {g : ℝ → F} {x : ℝ}

lemma bilin_smooth (hf : ContDiffAt ℝ ω f x) (hg : ContDiffAt ℝ ω g x) :
    ContDiffAt ℝ ω (fun t => L (f t) (g t)) x := (L.contDiff.contDiffAt.comp (f:=f) x hf).clm_apply hg
lemma bilin_rate {y} {z} (hf : HasDerivAt f y x) (hg : HasDerivAt g z x) :
    HasDerivAt (fun t => L (f t) (g t)) (L y (g x)+L (f x) z) x := by
  simpa [Function.comp_def,add_comm] using (L.hasFDerivAt.comp_hasDerivAt _ hf).clm_apply hg

lemma iterated_bilin (k : ℕ) (hf : ContDiffAt ℝ ω f x) (hg : ContDiffAt ℝ ω g x) :
    iteratedDeriv k (fun t => L (f t) (g t)) x = ∑ i∈Finset.range (k+1),
      k.choose i • L (iteratedDeriv i f x) (iteratedDeriv (k-i) g x) := by
  induction k generalizing f g with
  | zero => simp
  | succ n ih =>
    have he : deriv (fun t => L (f t) (g t)) =ᶠ[𝓝 x] fun t => L (f t) (deriv g t)+L (deriv f t) (g t) := by
      filter_upwards [hf.eventually (by simp),hg.eventually (by simp)] with a ha hb
      rw [(bilin_rate L (ha.differentiableAt (by simp)).hasDerivAt (hb.differentiableAt (by simp)).hasDerivAt).deriv,add_comm]
    have hF : ContDiffAt ℝ ω (deriv f) x := (hf.fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _ => 1) contDiffAt_const
    have hG : ContDiffAt ℝ ω (deriv g) x := (hg.fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _ => 1) contDiffAt_const
    rw [iteratedDeriv_succ', he.iteratedDeriv_eq,iteratedDeriv_fun_add
      ((bilin_smooth L hf hG).of_le le_top) ((bilin_smooth L hF hg).of_le le_top),ih hf hG,ih hF hg]
    nth_rw 1 [Finset.sum_range_succ'] -- first sum n→ first term + i+1
    nth_rw 2 [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, iteratedDeriv_zero, tsub_zero, one_smul, Nat.reduceSubDiff,
      ← iteratedDeriv_succ']
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Nat.choose_self,tsub_self,iteratedDeriv_zero,one_smul,Nat.choose]
    have hz : ∀ i∈ Finset.range n,n-(i+1)+1=n-i := fun i hi => by simp only [Finset.mem_range] at hi; omega
    rw [Nat.choose_eq_zero_of_lt n.lt_succ_self]
    simp +contextual only [hz,add_zero,add_smul,one_smul, Finset.sum_add_distrib]
    abel
lemma term_bilin (k : ℕ) (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) :
    term k (fun t => L (f t) (g t))=∑ i∈Finset.range (k+1), L (term i f) (term (k-i) g) := by
  unfold term
  rw [iterated_bilin L k hf hg, Finset.smul_sum]; refine Finset.sum_congr rfl fun i hi => ?_
  have h : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hw : ((k.choose i:ℕ):ℝ)*i.factorial*(k-i).factorial=k.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,map_smul,smul_apply]
  congr 1
  field_simp
  linarith
end bilin

lemma term_mul (k : ℕ) {f g : ℝ → T} (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) :
    term k (fun t => f t * g t)=∑ i∈Finset.range (k+1), term i f * term (k-i) g :=
  term_bilin (ContinuousLinearMap.mul ℝ T) _ hf hg

lemma term_mul_two {f g : ℝ → T} (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) :
    term 2 (fun t => f t*g t)= f 0 * term 2 g + deriv f 0 * deriv g 0 + term 2 f * g 0 := by
  rw [term_mul _ hf hg]
  simp [Finset.sum_range_succ]

variable {ι : Type*}

lemma rise_zero (s : Finset ι) {f : ι → ℝ → ℝ} (hf : ∀ i ∈ s, ContDiffAt ℝ ω (f i) 0)
    (hg : ∀ i∈s,f i 0=0) : (∀ j : ℕ,j<s.card → term j (fun x => ∏ i∈s, f i x)=0) ∧
      term s.card (fun x => ∏ i∈s, f i x)=∏ i∈s,deriv (f i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s h ih =>
    obtain ⟨p,q⟩ := (Finset.forall_mem_insert _ _ _).mp hf
    obtain ⟨u,v⟩ := (Finset.forall_mem_insert _ _ _).mp hg
    obtain ⟨hx,hy⟩ := ih q v
    simp_rw [Finset.prod_insert h,Finset.card_insert_of_notMem h,term_mul _ p (contDiffAt_prod q)]
    constructor
    · intro i hi
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_range] at hj
      by_cases he : j=0
      · subst j; simp only [term_zero,u,zero_mul]
      rw [hx _ (by omega),mul_zero]
    rw [Finset.sum_eq_single 1]
    · simpa using congr_arg (deriv (f a) 0 * ·) hy
    · intro b hb H; by_cases he : b=0
      · rw [he,term_zero,u,zero_mul]
      simp only [Finset.mem_range] at hb
      rw [hx _ (by omega),mul_zero]
    simp
end YM.CubicMatch
