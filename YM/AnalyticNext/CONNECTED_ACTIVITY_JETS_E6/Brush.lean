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
import YM.Analysis.Polydisc
import YM.Bid.Fuels
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Work.A05.Read
import YM.Work.A07


/-!
# Tangent occupation budgets (for differentiated charges of T-vertices)

Actual multilinear operator norms, geometric growth factor only per order.
In particular a cost may be zero (test *all* derivatives vanish in guard).
Use to avoid paying for patch/layout and powers repeatedly on UND factors.
Use powers for `deriv` including exponent of marked line velocity etc,
with different magnifications (reanchor after assuming far). Fixed AFTER
choosing analytic order, still volume free. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function
open scoped Topology BigOperators ContDiff Classical
variable {E F G Y A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {ι : Type*} {k : ℕ} {d e u v w : ℝ} {f g : E→F} {h : E→G} {x : E}

abbrev normJ (i : ℕ) (f : E→F) x := ‖iteratedFDeriv ℝ i f x‖

structure Color (k : ℕ) (u : ℝ) (f : E→F) (x : E) : Prop where
  smooth : ContDiffAt ℝ (↑ k) f x
  inside (i : ℕ) : i≤k → normJ i f x ≤ u

structure Brush (k : ℕ) (u d : ℝ) (f : E→F) (x : E) : Prop where
  smooth : ContDiffAt ℝ (↑ k) f x
  pos : 0≤d
  order i : i ≤ k→ normJ i f x ≤ u*d^i
namespace Brush
variable (p : Brush k u d f x)
include p
lemma bound : ‖f x‖ ≤ u := by simpa only [normJ,pow_zero,mul_one,norm_iteratedFDeriv_zero] using p.order 0 (Nat.zero_le _)
lemma nonneg : 0 ≤ u := (norm_nonneg _).trans p.bound
lemma climb (hx : u ≤ v) (hh : d ≤ e) : Brush k v e f x := by
  refine ⟨p.smooth,p.pos.trans hh,fun i hi => (p.order i hi).trans ?_⟩; exact
    mul_le_mul hx (pow_le_pow_left₀ p.pos hh i) (pow_nonneg p.pos _) (p.nonneg.trans hx)
omit p
lemma offer : Brush k d 1 f x ↔ Color k d f x := by
  constructor
  · intro h; exact ⟨h.smooth, fun i hi => by simpa using h.order i hi⟩
  intro h; exact ⟨h.smooth,zero_le_one,fun i hi=> by simpa using h.inside i hi⟩
lemma certified (hd : 0≤d) (c : F) : Brush k ‖c‖ d (fun _ : E=>c) x := by
  refine ⟨contDiffAt_const,hd,?_⟩; rintro (_|i) hi
  · simp
  unfold normJ; rw [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; positivity
include p
lemma smaller {j : ℕ} (hj : j ≤ k) : Brush j u d f x := ⟨p.smooth.of_le (by exact_mod_cast hj),p.pos,
    fun i hi=> p.order i (hi.trans hj)⟩
lemma shimmy (q : g =ᶠ[𝓝 x] f) : Brush k u d g x := by
  refine ⟨p.smooth.congr_of_eventuallyEq q,p.pos,fun i hi => ?_⟩
  unfold normJ; rw [(q.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]; exact p.order i hi
lemma smul (c : ℝ) : Brush k (‖c‖*u) d (fun i=> c • f i) x := by
  refine ⟨p.smooth.const_smul _,p.pos,fun i hi=> ?_⟩
  unfold normJ; rw [iteratedFDeriv_const_smul_apply' (p.smaller hi).smooth, norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (p.order _ hi) (norm_nonneg _)
lemma gathering (q : Brush k v d g x) : Brush k (u+v) d (fun i=> f i+g i) x := by
  refine ⟨p.smooth.add q.smooth,p.pos,fun i hi=>?_⟩
  change ‖iteratedFDeriv ℝ i (f+g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (p.smaller hi).smooth (q.smaller hi).smooth, add_mul]
  exact (norm_add_le ..).trans (add_le_add (p.order i hi) (q.order i hi))
lemma opposite : Brush k u d (-f) x := by
  have hF := p.smul (-1)
  simpa only [norm_neg,norm_one,one_mul,neg_one_smul] using! hF
lemma separating (q : Brush k v d g x) : Brush k (u+v) d (fun i=> f i-g i) x := by
  simpa only [Pi.neg_apply,sub_eq_add_neg] using! (p.gathering q.opposite)
omit p in
lemma spree (s : Finset ι) (f : ι→E→F) (p : ι→ℝ) (hd : 0≤d) (he : ∀ i∈s, Brush k (p i) d (f i) x) :
    Brush k (∑ i∈s,p i) d (fun j=> ∑ i∈s,f i j) x := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; simpa only [norm_zero] using! certified (k:=k) hd (0:F)
  | insert i s hi h =>
    simp_rw [Finset.sum_insert hi]; exact (he i (Finset.mem_insert_self ..)).gathering (h fun j hj=> he j (Finset.mem_insert_of_mem hj))

private theorem tally (q : Brush k v e h x) {j : ℕ} (hj : j≤k) :
    ∑ i∈Finset.range (j+1), (j.choose i : ℝ)*normJ i f x*normJ (j-i) h x ≤ u*v*(d+e)^j := by
  rw [add_pow, Finset.mul_sum]; refine Finset.sum_le_sum (fun i hi=> ?_)
  rw [Finset.mem_range] at hi
  refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left (p.order i (by omega)) (Nat.cast_nonneg _))
    (q.order (j-i) (by omega)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg p.nonneg (pow_nonneg p.pos _)))) ?_
  apply le_of_eq; ring

lemma twins (q : Brush k v e h x) (B : F →L[ℝ] G →L[ℝ] Y) :
    Brush k (‖B‖*(u*v)) (d+e) (fun i=> B (f i) (h i)) x := by
  let a i := B (f i) (h i)
  have hh : ContDiffAt ℝ (↑k) a x := (B.contDiff.contDiffAt.comp x p.smooth).clm_apply q.smooth
  refine ⟨hh,add_nonneg p.pos q.pos,fun i hi=>?_⟩
  obtain ⟨s,hs,hx,hf⟩:= p.smooth.contDiffOn' le_rfl (by simp)
  obtain ⟨t,ht,hX,hg⟩ := q.smooth.contDiffOn' le_rfl (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at hf hg
  let Z := s∩t; have hZ : IsOpen Z := hs.inter ht; have hm : x∈Z := ⟨hx,hX⟩; have hu : UniqueDiffOn ℝ Z := hZ.uniqueDiffOn
  unfold normJ; rw [← iteratedFDerivWithin_eq_iteratedFDeriv hu (hh.of_le (by exact_mod_cast hi)) hm]
  apply (B.norm_iteratedFDerivWithin_le_of_bilinear (hf.mono (Set.inter_subset_left)) (hg.mono (Set.inter_subset_right))
    hu hm (by exact_mod_cast hi)).trans
  rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg B)
  apply le_trans _ (tally p q hi)
  apply le_of_eq; apply Finset.sum_congr rfl; intro j hj
  unfold normJ; rw [Finset.mem_range] at hj
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hu (p.smaller (by omega)).smooth hm,
    iteratedFDerivWithin_eq_iteratedFDeriv hu (q.smaller (by omega)).smooth hm]

omit p
variable [NormedRing A] [NormedAlgebra ℝ A]
lemma paints {f g : E→ A} (p : Brush k u d f x) (q : Brush k v e g x) :
    Brush k (u*v) (d+e) (fun i=> f i*g i) x := by
  apply (p.twins q (ContinuousLinearMap.mul ℝ A)).climb _ le_rfl
  apply mul_le_of_le_one_left (mul_nonneg p.nonneg q.nonneg); exact ContinuousLinearMap.opNorm_mul_le ..
lemma all_prod (s : Finset ι) (f : ι→E→ℝ) (g h : ι→ℝ) (he : ∀ i∈s, Brush k (g i) (h i) (f i) x) :
    Brush k (∏ i∈s,g i) (∑ i∈s,h i) (fun v=> ∏ i∈s, f i v) x := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty]; simpa only [norm_one] using! certified (k:=k) (le_refl 0) (1:ℝ)
  | insert i s hi hp => simp_rw [Finset.prod_insert hi,Finset.sum_insert hi]
                        exact (he _ (Finset.mem_insert_self ..)).paints (hp fun i hi=> he _ (Finset.mem_insert_of_mem hi))
end Brush
end YM.ConnectedActivityE6.Blaze
