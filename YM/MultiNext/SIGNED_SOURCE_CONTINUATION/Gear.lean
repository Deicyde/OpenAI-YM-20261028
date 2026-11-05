import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Texas

set_option warningAsError false

/-!
# JHs. Compose and take the actual Ftensor.
No loss in support exponent when the link-position comparison is paid;
not for winding stencil at growing period without the comparison!
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Lyre
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open Mom Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {d : ℕ}

private lemma local_gear (U : Config G n) {Y : Support n} (p : BudgetPoint) {f : Config G n → ℂ}
    (h : p.Regular Y f) {x : Directions G n} (he : Healthy p.threshold Y (increment U x)) :
    ContDiffAt ℝ (p.order : WithTop ℕ∞) (fun v : Directions G n => (f ∘ increment U) (x+v)) 0 := by
  let s := surge Y x
  obtain ⟨ha,hp⟩:= arisen Y x
  exact (((show s 0=0 from ha).symm ▸ h.smooth _ he).comp (f:=s) 0 (hp.of_le le_top)).congr_of_eventuallyEq
    (flowing Y x U h.sites)

lemma responsive (U : Config G n) {Y : Support n} (p : BudgetPoint) {f : Config G n→ℂ} (h : p.Regular Y f)
    {x : Directions G n} (he : Healthy p.threshold Y (increment U x)) :
    ContDiffAt ℝ (p.order: WithTop ℕ∞) (f ∘ increment U) x := by
  let s := f ∘ increment U
  have hh : ContDiffAt ℝ (p.order: WithTop ℕ∞) (fun v => s (x+v)) (x-x) := sub_self x |>.symm ▸ local_gear U p h he
  have hx := hh.comp (f:=fun v => v-x) x (contDiffAt_id.sub (contDiffAt_const (c:=x)))
  have h : (fun v => s (x+v)) ∘ (fun v => v-x) = s := funext fun v => congr_arg s (add_sub_cancel ..)
  rwa [h] at hx

lemma general (k : ℕ) (R : ℝ) (G : Gauge) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (n : Side) (Y : Support n) (P : BudgetPoint) (o : Site n) (x : Directions G n)
      (f : Config G n → ℂ) (U : Config G n) (c : ℝ) (v : Fin k → Directions G n) (a : Fin k → ℝ),
      k ≤ P.order → P.Regular Y f → Healthy P.threshold Y (increment U x) → P.supBounds o Y f c →
      (∀ i,needed Y i → ‖x i‖ ≤ R ∧ width P o i ≤ 1) →
      (∀ i,Sized (a i) (v i) P o) → ‖iteratedFDeriv ℝ k (f ∘ increment U) x v‖ ≤ C*(∏ i,a i)*c := by
  choose U' hU HU using fun i => lyre i G
  choose b hb Hb using fun i => bore G i R
  let books (i : OrderedFinpartition k) := U' i.length * ∏ j, b (i.partSize j-1)
  refine ⟨1+∑ i, books i, le_add_of_nonneg_right (sum_nonneg fun i _ => ?_),fun n Y P o x f V c v a he hF hV hc hX ha => ?_⟩
  · exact mul_nonneg (zero_le_one.trans (hU _)) (prod_nonneg fun j _ => zero_le_one.trans (hb _))
  let g : Directions G n → ℂ := f ∘ increment V
  let W := increment V x
  let p : Directions G n → ℂ := f ∘ increment W
  let C := surge Y x
  obtain ⟨hQ,hD⟩:=arisen Y x
  have hg := flowing Y x V hF.sites
  have hx := (hg.iteratedFDeriv ℝ k).eq_of_nhds
  change (iteratedFDeriv ℝ k (fun v => g (x+v)) (0:Directions G n))=iteratedFDeriv ℝ k (p ∘ C) 0 at hx
  have hPP : ContDiffAt ℝ (P.order:WithTop ℕ∞) p (C 0) := by rw [show C 0=0 from hQ]; exact hF.smooth _ hV
  rw [iteratedFDeriv_comp_add_left, add_zero, iteratedFDeriv_comp hPP
    (hD.of_le le_top) (Nat.cast_le.mpr he)] at hx
  change ‖iteratedFDeriv ℝ k g x v‖ ≤ _
  rw [hx,show C 0=0 from hQ,FormalMultilinearSeries.taylorComp,_root_.sum_apply]
  let t := ∏ i,a i
  have ht : 0 ≤ t := prod_nonneg fun i _ => (ha i).1
  simp_rw [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries]
  refine (norm_sum_le ..).trans (le_trans (sum_le_sum (g:=fun i => books i*t*c) fun i _ => ?_) ?_)
  · let Y' j := iteratedFDeriv ℝ (i.partSize j) C 0 (v ∘ i.emb j)
    let p' j := ∏ w,a (i.emb j w)
    have hj j : Sized (b (i.partSize j-1)*p' j) (Y' j) P o := by
      have hi (k : ℕ) (hk : k=i.partSize j) (v : Fin k → Directions G n) (a : Fin k → ℝ) (hA : ∀ i,Sized (a i) (v i) P o) :
          Sized (b (k-1)*∏ i,a i) (iteratedFDeriv ℝ k C 0 v) P o := by
        cases k
        · have he := i.partSize_pos j; omega
        simpa only [Nat.add_sub_cancel] using Hb _ n Y P o x v a hX hA
      exact hi _ rfl _ _ (fun j => ha _)
    change ‖iteratedFDeriv ℝ i.length p 0 Y'‖ ≤ _
    refine (HU i.length n P Y o f W c Y' _ (i.length_le.trans he) hV hF hc hj).trans_eq ?_
    unfold books p' t; rw [prod_mul_distrib,i.prod_sigma_eq_prod] -- order
    ring
  rw [← Finset.sum_mul,← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) ht) hc.1
end YM.MultiNext.SignedSource.Lyre
