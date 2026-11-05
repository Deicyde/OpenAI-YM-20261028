import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Lyres
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Mom

set_option warningAsError false

/-!
# Uniform chart conversion for the JHs estimate

Initiate Link chart at any position v (even logarithm-large possible
if exp v good). Quantitative receipt here will then be asked only in
‖v‖≤1 (or any *fixed* reserved R) on tested links and where stencil
position weights stay below 1. P.support must know this (applicability
delay tested before using, e.g. E B^8 cover cut), no claim it works
uniformly in wrapping tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Lyre
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open Mom Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable (G : Gauge) {n : Side} {d : ℕ}

def spin (x : G.Color × G.Color) := G.plog
  (G.mat (G.lieExp (x.1+x.2))* star (G.mat (G.lieExp x.1)))

def gust (v : G.Color) (x : G.Color) := spin G (v,x)

lemma wander : ∀ x : G.Color, gust G x 0 = 0 ∧ ContDiffAt ℝ ω (spin G) (x,0) ∧ ContDiffAt ℝ ω (gust G x) 0 := by
  intro x
  let f (x : G.Color × G.Color) := G.mat (G.lieExp (x.1+x.2))* star (G.mat (G.lieExp x.1))
  have hp : f (x,0)=1 := by simp only [f,add_zero]; exact G.mat_mul_star _
  have he : ContDiff ℝ ω f := (G.exp_jet.comp (contDiff_fst.add contDiff_snd)).mul (((starL ℝ:G.Mat≃L[ℝ]G.Mat).contDiff.comp (G.exp_jet.comp contDiff_fst)))
  have hh : ContDiffAt ℝ ω (spin G) (x,0) := ((show ContDiffAt ℝ ω G.plog (f (x,0)) from hp.symm ▸ G.plog_diff)).comp (f:=f) _ he.contDiffAt
  exact ⟨(congrArg G.plog hp).trans G.plog_one,hh,hh.comp (f:=fun v => (x,v)) _ (contDiff_const.prodMk contDiff_id).contDiffAt⟩

/-- Uniform, no link/period price. -/
lemma front (k : ℕ) (R : ℝ) : ∃ C : ℝ,1 ≤ C ∧ ∀ v : G.Color, ‖v‖ ≤ R → ∀ i ≤ k,∀ y : Fin i→G.Color,
    ‖iteratedFDeriv ℝ i (gust G v) 0 y‖ ≤ C * ∏ j, ‖y j‖ := by
  let X := G.Color × G.Color
  let b (v : G.Color) := (v,(0:G.Color)); let L := ContinuousLinearMap.inr ℝ G.Color G.Color
  have hc (i) : BddAbove ((fun v => ‖iteratedFDeriv ℝ i (spin G) (b v)‖) '' Metric.closedBall (0:G.Color) R) := by
    apply (isCompact_closedBall _ _).bddAbove_image
    refine continuous_iff_continuousAt.mpr (fun x => (( (wander G x).2.1.continuousAt_iteratedFDeriv (k:=i) le_top).norm.comp (f:=b)
      (show ContinuousAt b x by unfold b; fun_prop))) |>.continuousOn
  choose c H using hc
  have he : ∃ C : ℝ,1 ≤ C ∧ ∀ i ≤ k,c i ≤ C :=
    ((eventually_ge_atTop (1:ℝ)).and ((eventually_all_finset (Finset.range (k+1))).mpr fun i _ => eventually_ge_atTop (c i))).exists.imp
      (fun i hi => ⟨hi.1,fun k hk => hi.2 _ (mem_range.mpr (Nat.lt_succ_of_le hk))⟩)
  obtain ⟨C,hC,h⟩:=he
  refine ⟨C,hC,fun v hv i hi y => ?_⟩
  have ht : ‖iteratedFDeriv ℝ i (spin G) (b v)‖ ≤ C := (H i (Set.mem_image_of_mem _ (by simpa using hv))).trans (h i hi)
  have hx : ‖iteratedFDeriv ℝ i (spin G) (b v) (fun i => L (y i))‖ ≤ C*∏ i,‖L (y i)‖ :=
    ((iteratedFDeriv ℝ i (spin G) (b v)).le_opNorm _).trans (mul_le_mul_of_nonneg_right ht (prod_nonneg fun _ _ => norm_nonneg _))
  let f (x : X) := spin G (b v+x)
  have hf : ContDiffAt ℝ (i:WithTop ℕ∞) f 0 := by
    have hh : ContDiffAt ℝ ω (spin G) (b v+0) := by rw [add_zero]; exact (wander G v).2.1
    exact (hh.of_le le_top).comp (f:=fun x => b v+x) 0 (contDiffAt_const.add contDiffAt_id)
  rw [show gust G v=f ∘ L from funext (fun i => by unfold f gust; simp [b, L,show (v, (0:G.Color))+(0,i)=(v,i) from Prod.ext (add_zero _) (zero_add _)]), jets_linear L hf]
  unfold f; rw [iteratedFDeriv_comp_add_left, add_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simpa only [L,ContinuousLinearMap.inr_apply,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] using hx

variable {G}
lemma slip (v : G.Color) : ∀ᶠ t : G.Color in 𝓝 0, G.lieExp (v+t)=G.lieExp (gust G v t) * G.lieExp v := by
  let g (t : G.Color) := G.lieExp (v+t) * (G.lieExp v)⁻¹
  have h : Tendsto g (𝓝 0) (𝓝 1) := by
    rw [← show g 0=1 by simp [g]]; exact (show Continuous g by unfold g; fun_prop).continuousAt
  filter_upwards [h.eventually G.plog_right] with t ht
  unfold g at ht; rw [G.mat_mul,G.mat_inv] at ht; rw [gust,spin,ht]; group

def surge (Y : Support n) (v x : Directions G n) : Directions G n := fun i =>
    if needed Y i then gust G (v i) (x i) else 0

lemma flowing (Y : Support n) (v : Directions G n) (U : Config G n) {f : Config G n→ℂ} (h : LocalOn Y f) :
    (fun x => f (increment U (v+x))) =ᶠ[𝓝 (0:Directions G n)] fun x => f (increment (increment U v) (surge Y v x)) := by
  have hh (i : Edge (Site n)) : ∀ᶠ x : Directions G n in 𝓝 0, G.lieExp (v i+x i)=G.lieExp (gust G (v i) (x i))*G.lieExp (v i) :=
    (continuous_apply (A:=fun _ : Edge (Site n) => G.Color) i).continuousAt (x:=(0:Directions G n)) |>.eventually (slip _)
  filter_upwards [Filter.eventually_all.mpr hh] with x ht
  refine h _ _ (fun i hi hv => ?_)
  simp only [increment,surge,if_pos (show needed Y i from ⟨hi,hv⟩),Pi.add_apply,ht,mul_assoc]

lemma arisen (Y : Support n) (x : Directions G n) : surge Y x 0=0 ∧ ContDiffAt ℝ ω (surge Y x) 0 := by
  constructor
  · funext i; unfold surge; split
    next h => exact (wander G _).1
    rfl
  apply contDiffAt_pi.mpr; intro i; unfold surge; by_cases h:needed Y i
  · simp only [if_pos h]
    have he : ContDiffAt ℝ ω (gust G (x i)) ((0:Directions G n) i) := (wander G _).2.2
    exact he.comp (f:=fun x : Directions G n => x i) 0 (contDiffAt_apply _ _ _ _)
  simp only [if_neg h]; exact contDiffAt_const

variable (G)
lemma bore (k : ℕ) (R : ℝ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (n : Side) (X : Support n) (P : BudgetPoint) (o : Site n)
      (u : Directions G n) (v : Fin (k+1) → Directions G n) (c : Fin (k+1)→ℝ),
      (∀ i,needed X i → ‖u i‖ ≤ R ∧ width P o i ≤ 1) → (∀ i, Sized (c i) (v i) P o) →
      Sized (C*∏ i,c i) (iteratedFDeriv ℝ (k+1) (surge X u) 0 v) P o := by
  obtain ⟨M,hP,h⟩:=front G (k+1) R
  refine ⟨M,hP,fun n X P o u v c hi he => ⟨mul_nonneg (zero_le_one.trans hP) (prod_nonneg fun i _ => (he i).1),fun i => ?_⟩⟩
  let f : Directions G n →L[ℝ] G.Color := ContinuousLinearMap.proj i
  have hv := f.iteratedFDeriv_comp_left (i:=k+1) (arisen X u).2 le_top
  have hx := congrArg (fun z => (z : Tensor.T (Directions G n) G.Color (k+1)) v) hv
  change (iteratedFDeriv ℝ (k+1) (f ∘ surge X u) 0) v=(iteratedFDeriv ℝ (k+1) (surge X u) 0 v) i at hx
  rw [← hx]
  by_cases hh : needed X i
  · rw [show f ∘ surge X u=gust G (u i) ∘ f from funext fun x => if_pos hh, jets_linear f ((wander G (u i)).2.2.of_le le_top),
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    let r := width P o i
    have hr := (width_pos P o i).le
    have hy : ∏ j, ‖v j i‖ ≤ (∏ j,c j)*r := calc
      _ ≤ ∏ j, (c j*r) := prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => (he j).2 i)
      _ ≤ _ := by
        rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
        refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun j _ => (he j).1)
        rw [pow_succ]; exact mul_le_of_le_one_left hr (pow_le_one₀ hr (hi i hh).2)
    rw [mul_assoc]; exact (h _ (hi _ hh).1 _ le_rfl _).trans (mul_le_mul_of_nonneg_left hy (zero_le_one.trans hP))
  have hh : f ∘ surge X u=fun _ => 0 := funext fun x => if_neg hh
  rw [hh,iteratedFDeriv_fun_zero]; simp only [Pi.zero_apply,zero_apply,norm_zero]
  exact mul_nonneg (mul_nonneg (zero_le_one.trans hP) (prod_nonneg fun j _ => (he j).1)) (width_pos ..).le
end YM.MultiNext.SignedSource.Lyre
