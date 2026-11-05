import YM.Further.DENSE_MIXED_KERNELS.Shift
import YM.Next.FOUNDATIONS.Regular

/-!
# Mixed jets of held factors

No derivative of hard fine tests. Nonfactorial through order k (matches
`System.Forward`). A scale T costs T^j for j directions total, crucial
when many operands share the kernel. Actual derivatives in varying
(nonabelian) link increment charts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Finset Filter MeasureTheory Lattice RG Wilson
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {n : Side} {k j : ℕ} {E Y F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {U : Config G n} {f g : Config G n → E}
local notation "I" => Directions G n

namespace Rests
lemma reduce (h : Rests f k U) (hw : j ≤ k) : Rests f j U := ContDiffAt.of_le h (Nat.cast_le.mpr hw)
lemma tilt (h : Rests f k U) {l : List I} (hv : j+l.length ≤ k) : Rests (leftDerivs f l) j U :=
    Next.Foundations.leftDerivs_chart l _ (ContDiffAt.of_le h (Nat.cast_le.mpr (by omega)))
lemma has (h : Rests f (k+1) U) (a : I) : HasDerivAt (fun t : ℝ => f (increment U (t • a))) (leftDerivs f [a] U) 0 :=
    Next.Foundations.left_has a (l:=[]) (by simp) h
lemma plus (h : Rests f k U) (hh : Rests g k U) : Rests (fun x => f x + g x) k U := ContDiffAt.add h hh
lemma neg (h : Rests f k U) : Rests (fun x => -f x) k U := ContDiffAt.neg h
lemma modulate {g : Config G n → F} (h : Rests f k U) (hh : Rests g k U) (L : E →L[ℝ] F →L[ℝ] Y) :
    Rests (fun x => L (f x) (g x)) k U := ContDiffAt.clm_apply (L.contDiff.contDiffAt.comp _ h) hh

end Rests

lemma plus_left (hf : Rests f k U) (hg : Rests g k U) (l : List I) (hl : l.length ≤ k) :
    leftDerivs (fun x => f x + g x) l U = leftDerivs f l U + leftDerivs g l U := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih =>
    have he : l.length < k := hl
    refine (((Next.Foundations.left_has A he hf).add (Next.Foundations.left_has A he hg)).congr_of_eventuallyEq (f₁:=fun t =>
      leftDerivs (fun x => f x + g x) l (increment U (t • A))) ?_).deriv
    filter_upwards [rest_near hf A, rest_near hg A] with i h h' using ih h h' he.le

lemma negate_left (l : List I) : leftDerivs (fun x => -f x) l U = -leftDerivs f l U := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih => simp only [leftDerivs,ih,deriv.fun_neg]

lemma append_left (l s : List I) : leftDerivs f (l++s) U = leftDerivs (leftDerivs f s) l U := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih => simp only [List.cons_append,leftDerivs,ih]

lemma clm_left (L : E →L[ℝ] F) (hf : Rests f k U) (l : List I) (hl : l.length ≤ k) :
    leftDerivs (fun x => L (f x)) l U = L (leftDerivs f l U) := by
  induction l generalizing U with
  | nil => rfl
  | cons a l ih =>
    have he : l.length < k := hl
    refine ((L.hasFDerivAt.comp_hasDerivAt 0 (Next.Foundations.left_has a he hf)).congr_of_eventuallyEq (f₁:=fun t=>
      leftDerivs (fun x => L (f x)) l (increment U (t • a))) ?_).deriv
    filter_upwards [rest_near hf a] with t ht using ih ht he.le

lemma mul_one_step {g : Config G n → F} (h : Rests f (k+1) U) (hg : Rests g (k+1) U) (L : E →L[ℝ] F →L[ℝ] Y) (a : I) :
    leftDerivs (fun x => L (f x) (g x)) [a] U = L (leftDerivs f [a] U) (g U) + L (f U) (leftDerivs g [a] U) := by
  have hh := ((L.hasFDerivAt.comp_hasDerivAt 0 (h.has a)).clm_apply (hg.has a)).deriv
  simp only [comp_apply,zero_smul,increment_zero] at hh; exact hh

/-- Budget jet predicate for any chosen direction set; no implicit spatial
smoothness or support, this is at one chart center after changes. -/
structure Pitch (f : Config G n → E) (U : Config G n) (P : I → Prop) (k : ℕ) (M T : ℝ) : Prop where
  smooth : Rests f k U
  bounds : ∀ l : List I, l.length ≤ k → (∀ v∈l,P v) → ‖leftDerivs f l U‖ ≤ M*T^l.length

variable {M N T S : ℝ} {P : Directions G n → Prop}
namespace Pitch
lemma under (h : Pitch f U P k M T) (hj : j ≤ k) : Pitch f U P j M T :=
    ⟨h.smooth.reduce hj, fun l hl => h.bounds l (hl.trans hj)⟩
lemma cost (h : Pitch f U P k M T) : ‖f U‖ ≤ M := by simpa only [leftDerivs,List.length_nil,pow_zero,mul_one] using!
    (h.bounds [] (Nat.zero_le k) (by simp))
lemma pos (h : Pitch f U P k M T) : 0≤M := (norm_nonneg _).trans h.cost
lemma mono (h : Pitch f U P k M T) (hm : M ≤ N) (ht : 0 ≤ T) (hs : T ≤ S) : Pitch f U P k N S :=
    ⟨h.smooth, fun l hl he => (h.bounds l hl he).trans (mul_le_mul hm (pow_le_pow_left₀ ht hs _)
      (pow_nonneg ht _) (h.pos.trans hm))⟩
lemma tilt (h : Pitch f U P (k+1) M T) {a : I} (ha : P a) : Pitch (leftDerivs f [a]) U P k (M*T) T := by
  refine ⟨h.smooth.tilt le_rfl,fun l hl he => ?_⟩
  have hh (v : I) (hv : v∈l ++ [a]) : P v := by
    rcases List.mem_append.mp hv with h1|h2; exact he _ h1; simpa only [List.mem_singleton.mp h2]
  simpa only [append_left,List.length_append,List.length_singleton,pow_succ',mul_assoc] using!
    h.bounds (l++[a]) (by simp; omega) hh
lemma congr' (h : Pitch f U P k M T) (he : g ∘ increment U=ᶠ[𝓝 0] f ∘ increment U) : Pitch g U P k M T :=
  ⟨ContDiffAt.congr_of_eventuallyEq h.smooth he, fun l hl hh => by rw [left_eq l he]; exact h.bounds l hl hh⟩

lemma negate (h : Pitch f U P k M T) : Pitch (fun x => - f x) U P k M T := by
  refine ⟨h.smooth.neg, fun l hl hh => by rw [negate_left,norm_neg]; exact h.bounds l hl hh⟩
lemma plus (h : Pitch f U P k M T) (hh : Pitch g U P k N T) : Pitch (fun x => f x+g x) U P k (M+N) T := by
  refine ⟨h.smooth.plus hh.smooth,fun l hl hA => ?_⟩
  rw [plus_left h.smooth hh.smooth l hl,add_mul]
  exact (norm_add_le ..).trans (add_le_add (h.bounds l hl hA) (hh.bounds l hl hA))

lemma linear (hf : Pitch f U P k M T) (L : E →L[ℝ] F) {C : ℝ} (hc : ∀ z, ‖L z‖ ≤ C*‖z‖) (h : 0≤C) :
    Pitch (fun x => L (f x)) U P k (C*M) T := by
  refine ⟨L.contDiff.contDiffAt.comp _ hf.smooth,fun l hl he => ?_⟩
  rw [clm_left L hf.smooth l hl,mul_assoc]; exact (hc _).trans (mul_le_mul_of_nonneg_left (hf.bounds l hl he) h)

lemma bilinear {g : Config G n → F} (L : E →L[ℝ] F →L[ℝ] Y) (hf : Pitch f U P k M T) (hg : Pitch g U P k N S)
    {C : ℝ} (h : ∀ x y, ‖L x y‖ ≤ C*‖x‖*‖y‖) (hc : 0≤C) : Pitch (fun x => L (f x) (g x)) U P k (C*M*N) (T+S) := by
  induction k generalizing M N f g with
  | zero =>
    refine ⟨hf.smooth.modulate hg.smooth L,fun l hl hh => ?_⟩
    have he : l=[] := by cases l <;> simp_all
    subst l
    simp only [leftDerivs,List.length_nil,pow_zero,mul_one]
    exact (h _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hf.cost hc) hg.cost (norm_nonneg _) (mul_nonneg hc hf.pos))
  | succ k ih =>
    refine ⟨hf.smooth.modulate hg.smooth L, fun l hl he => ?_⟩
    have HF := hf.under (show k ≤ k+1 by omega)
    have HG := hg.under (show k ≤ k+1 by omega)
    cases l using List.reverseRecOn with
    | nil => exact (ih HF HG).bounds [] (by simp) he
    | append_singleton l a =>
      have hi := he a (by simp)
      let x c := L (leftDerivs f [a] c) (g c); let y c := L (f c) (leftDerivs g [a] c)
      have heq : (leftDerivs (fun x => L (f x) (g x)) [a]) ∘ increment U =ᶠ[𝓝 0] (fun c => x c+y c) ∘ increment U := by
        filter_upwards [rest_inside hf.smooth,rest_inside hg.smooth] with t hu ht using mul_one_step hu ht L a
      have H1 : Pitch x U P k (C*(M*T)*N) (T+S) := ih (hf.tilt hi) HG
      have H2 : Pitch y U P k (C*M*(N*S)) (T+S) := ih HF (hg.tilt hi)
      have hp : l.length ≤ k := by simpa only [List.length_append,List.length_singleton,Nat.add_le_add_iff_right] using hl
      rw [List.length_append,List.length_singleton, pow_succ,append_left,left_eq _ heq]
      exact ((H1.plus H2).bounds l hp fun v hv => he v (by simp [hv])).trans_eq (by ring)
lemma clm {f : Config G n → E →L[ℝ] F} (h : Pitch f U P k M T) (hg : Pitch g U P k N S) :
    Pitch (fun x => f x (g x)) U P k (M*N) (T+S) := by
  let L : (E→L[ℝ] F) →L[ℝ] E→L[ℝ] F := ContinuousLinearMap.id ℝ _
  simpa only [L,ContinuousLinearMap.id_apply,one_mul] using! bilinear L h hg (C:=1)
    (fun i v => by simpa only [L,ContinuousLinearMap.id_apply,one_mul] using i.le_opNorm v) zero_le_one

lemma real_mul {f g : Config G n → ℝ} (h : Pitch f U P k M T) (hg : Pitch g U P k N S) :
    Pitch (fun x => f x*g x) U P k (M*N) (T+S) := by
  simpa only [ContinuousLinearMap.mul_apply',one_mul] using! bilinear (ContinuousLinearMap.mul ℝ ℝ) h hg
    (C:=1) (fun i v => by simp) zero_le_one
lemma complex_mul {f g : Config G n → ℂ} (h : Pitch f U P k M T) (hg : Pitch g U P k N S) :
    Pitch (fun x => f x*g x) U P k (M*N) (T+S) := by
  simpa only [ContinuousLinearMap.mul_apply',one_mul] using! bilinear (ContinuousLinearMap.mul ℝ ℂ) h hg
    (C:=1) (fun i v => by simp) zero_le_one

lemma fixed (x : E) (ht : 0 ≤ T) : Pitch (fun _ => x) U P k ‖x‖ T := by
  have hv l W : leftDerivs (fun _ : Config G n => x) l W = if l=[] then x else 0 := by
    induction l generalizing W with
    | nil => simp [leftDerivs]
    | cons a l ih => simp [leftDerivs, ih]
  refine ⟨contDiffAt_const, fun l _ _ => ?_⟩
  rw [hv]; split
  next h => simp [h]
  next => rw [norm_zero]; positivity

lemma joint {ι : Type*} (s : Finset ι) {f : ι → Config G n → ℂ} {b t : ι → ℝ} (hf : ∀ i∈s,Pitch (f i) U P k (b i) (t i)) :
    Pitch (fun x => ∏ i∈s,f i x) U P k (∏ i∈s,b i) (∑ i∈s,t i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [prod_empty,sum_empty,norm_one] using! fixed (k:=k) (U:=U) (P:=P) (1:ℂ) (le_refl 0)
  | insert i s hi ih =>
    simpa only [Finset.prod_insert hi,Finset.sum_insert hi] using! complex_mul (hf i (mem_insert_self ..))
      (ih fun _ h => hf _ (mem_insert_of_mem h))
end Pitch
end YM.Further.DenseMixedKernels
