import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import YM.UVExtension.Limits

/-! Use real coefficient Hilbert spaces to resolve the ambiguity of covariant lifting.
Bounded basis only; compactness to be used WITH step uniqueness. -/

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Filter Function Finset
open scoped Topology BigOperators InnerProductSpace Classical
variable {I : Type} {s : ℕ → ℕ} {a : ℝ}
abbrev Ortho (I : Type) := lp (fun _ : I => ℝ) 2
variable {K : Submodule ℝ (Ortho I)} {f g : ℕ → Ortho I} {x z : Ortho I}

structure HLimit (f : ℕ → Ortho I) (x : Ortho I) : Prop where
  bound : ∃ b, ∀ᶠ i in atTop, ‖f i‖ ≤ b
  hit (i : I) : Tendsto (fun n=> f n i) atTop (𝓝 (x i))

theorem HLimit.strong (h : Tendsto f atTop (𝓝 x)) : HLimit f x := by
  refine ⟨⟨‖x‖+1,h.norm.eventually (ge_mem_nhds (by linarith))⟩,fun i=> ?_⟩
  exact ((lp.lipschitzWith_one_eval (E:=fun _ : I => ℝ) 2 i).continuous.tendsto x).comp h

theorem HLimit.upon (h : HLimit f x) (hp : Tendsto s atTop atTop) : HLimit (f ∘ s) x :=
  ⟨let ⟨_,hh⟩ := h.bound; ⟨_,hp.eventually hh⟩, fun i => (h.hit i).comp hp⟩

theorem HLimit.add (h : HLimit f x) (hh : HLimit g z) : HLimit (f+g) (x+z) := by
  obtain ⟨a,ha⟩:= h.bound; obtain ⟨b,hb⟩:=hh.bound
  exact ⟨⟨a+b,(ha.and hb).mono fun i hp=> (norm_add_le _ _).trans (add_le_add hp.1 hp.2)⟩,fun i=> (h.hit i).add (hh.hit i)⟩

theorem HLimit.linear (h : HLimit f x) (y : ℝ) : HLimit (y • f) (y • x) := by
  obtain ⟨a,ha⟩ := h.bound
  exact ⟨⟨‖y‖*a,ha.mono fun i hi => by change ‖y • (f i)‖ ≤ _; rw [norm_smul]; gcongr⟩,fun i=> (h.hit i).const_mul y⟩

theorem HLimit.norm_le (h : HLimit f x) (he : ∀ᶠ i in atTop, ‖f i‖ ≤ a) : ‖x‖ ≤ a :=
    lp.norm_le_of_tendsto he (tendsto_pi_nhds.mpr h.hit)

theorem HLimit.price (h : HLimit f x) (z : Ortho I) : Tendsto (fun i=> inner ℝ z (f i)) atTop (𝓝 (inner ℝ z x)):= by
  obtain ⟨b,hb⟩:=h.bound
  have hi:=h.norm_le hb
  rw [Metric.tendsto_nhds]; intro ε he
  have hv : 0 < b+1 := by linarith [norm_nonneg x]
  obtain ⟨s,hs⟩:= ((lp.hasSum_single ENNReal.ofNat_ne_top z).eventually
    (Metric.ball_mem_nhds z (show 0 < ε/4/(b+1) by positivity))).exists
  let v : Ortho I := ∑ i ∈ s, lp.single 2 i (z i)
  have hw : ‖z-v‖*(b+1) < ε/4 := (lt_div_iff₀ hv).1 (by rw [← dist_eq_norm,dist_comm]; exact hs)
  have hz : Tendsto (fun n=> inner ℝ v (f n)) atTop (𝓝 (inner ℝ v x)) := by
    unfold v; simp_rw [sum_inner,lp.inner_single_left]
    exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.inner (h.hit i)
  filter_upwards [hb,Metric.tendsto_nhds.mp hz (ε/4) (by positivity)] with n hn ht
  calc
    _ ≤ dist (inner ℝ z (f n)) (inner ℝ v (f n))+dist (inner ℝ v (f n)) (inner ℝ v x)+dist (inner ℝ v x) (inner ℝ z x) := dist_triangle4 _ _ _ _
    _ ≤ ‖z-v‖*(b+1)+ε/4+‖z-v‖*(b+1) := by
      rw [dist_comm (inner ℝ v x) (inner ℝ z x)]
      refine add_le_add (add_le_add ?_ ht.le) ?_
      all_goals
        rw [dist_eq_norm, ← inner_sub_left]; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _))
    _ < ε := by linarith

theorem HLimit.normal (h : HLimit f x) (he : ∀ᶠ i in atTop, f i ∈ Kᗮ) : x ∈ Kᗮ :=
    fun i hi=> tendsto_nhds_unique (h.price i) (tendsto_const_nhds.congr' (he.mono fun _ hn=> (hn i hi).symm))

lemma Minimize (K : Submodule ℝ (Ortho I)) (x : Ortho I) (h : IsClosed (K : Set (Ortho I))) : ∃ z : Ortho I, ‖z‖≤‖x‖ ∧ z ∈ Kᗮ ∧ x-z ∈ K := by
  letI : CompleteSpace ↥K := h.completeSpace_coe
  refine ⟨Kᗮ.starProjection x, Kᗮ.norm_starProjection_apply_le x, ?_, ?_⟩
  exact Kᗮ.starProjection_apply_mem _
  rw [Submodule.starProjection_orthogonal_val]; simp

lemma hs_subseq [Countable I] (hf : ∀ n, ‖f n‖ ≤ a) : ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ x : Ortho I,HLimit (f ∘ s) x := by
  let R := Set.univ.pi fun _ : I => Metric.closedBall (0:ℝ) a
  have hr : ∀ n, ⇑(f n) ∈ R := fun n i _=> Metric.mem_closedBall.mpr <| by rw [dist_zero_right]; exact (lp.norm_apply_le_norm (by norm_num) _ _).trans (hf _)
  obtain ⟨g,hg,s,hs,hS⟩:= (isCompact_univ_pi (fun _ : I => isCompact_closedBall (0:ℝ) a)).tendsto_subseq hr
  let z := f∘s
  have hh : Bornology.IsBounded (Set.range z) := (Metric.isBounded_closedBall (x:=0) (r:=a)).subset (Set.range_subset_iff.mpr (fun i=> by rw [Metric.mem_closedBall,dist_zero_right]; exact hf _))
  let x : Ortho I := ⟨(g : PreLp (fun _ : I=> ℝ)),lp.memℓp_of_tendsto hh hS⟩
  exact ⟨s,hs,x,⟨a,Eventually.of_forall fun _=> hf _⟩,tendsto_pi_nhds.mp hS⟩
end YM.UVExtension.Projection
