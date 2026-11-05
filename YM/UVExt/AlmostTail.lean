import YM.UVExt.MetricLimit

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Set Function Lattice Laurent Wilson RG MeasureTheory
open scoped ContDiff Topology Classical Pointwise BigOperators InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {ι α γ : Type*} {F : Filter ι} [NeBot F] {L : α → ℝ} {f : α→E} {σ C : ℝ}

def Carries (C σ : ℝ) (L : α→ℝ) (f : α→E) : Prop := (∀ i, 0≤L i) ∧
    ∀ s : Finset α, ∑ i∈s, Real.exp (σ*L i)*‖f i‖ ≤ C

namespace Carries
variable (h : Carries C σ L f)
include h
lemma paid : SumBudget (fun x=> Real.exp (σ*L x)*‖f x‖) C := by
  have hz (x : α) : 0 ≤ Real.exp (σ*L x)*‖f x‖ := by positivity
  have hg := summable_of_sum_le hz h.2
  exact ⟨hz,hg,Summable.tsum_le_of_sum_le hg h.2⟩

lemma total (hs : 0<σ) : ∀ x, ‖f x‖ ≤ C := by
  intro x; have hv := h.2 ({x}:Finset α)
  simp only [Finset.sum_singleton] at hv
  exact (hv.trans' (show _≤ Real.exp (σ*L x)*‖f x‖ from le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (mul_nonneg hs.le (h.1 x))))) -- sum_simplifies first

lemma summable_norm (hs : 0 < σ) (A : ℝ) {g : α→γ} [NormedAddCommGroup γ] [CompleteSpace γ] (hg : ∀ i, ‖g i‖ ≤ A*Real.exp (σ/2*L i)*‖f i‖) : Summable (fun i=>‖g i‖) := by
  refine Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>le_trans (hg i) ?_) (h.paid.2.1.mul_left (max 0 A))
  rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right ..) (Real.exp_le_exp.mpr (by gcongr <;> first |exact h.1 _|linarith)) (by positivity) (by positivity)) (norm_nonneg _)

omit h
lemma sunk (E : Type*) [NormedAddCommGroup E] (hs : 0 < σ) (A : ℝ) (hA : 0 ≤ A) (hL : Tendsto L cofinite atTop) {ε : ℝ} (he : 0 < ε) :
    ∃ s : Finset α, ∀ f : α→E, Carries C σ L f → ∀ t : Finset α, Disjoint t s → ∑ i∈t, ‖f i‖*A*Real.exp (σ/2*L i) ≤ ε := by
  have hz := Real.tendsto_exp_atBot.comp (hL.const_mul_atTop_of_neg (show -(σ/2)<0 by linarith))
  have hf : ∀ᶠ i in cofinite, A*Real.exp (-(σ/2)*L i) ≤ ε/(max C 1) := (show Tendsto (fun i=> A*Real.exp (-(σ/2)*L i)) cofinite (𝓝 0) by simpa using hz.const_mul A).eventually (gt_mem_nhds (by positivity)) |>.mono fun _ hx=> hx.le
  let v := (Filter.eventually_cofinite.mp hf).toFinset
  have hv (i) (h : ε/max C 1 < A*Real.exp (-(σ/2)*L i)) : i∈v := by simpa only [v,Set.Finite.mem_toFinset,Set.mem_setOf_eq] using h.not_ge
  refine ⟨v,fun f h t ht=>?_⟩
  let c i := Real.exp (σ*L i)*‖f i‖
  calc
    _ ≤ ∑ i∈t, (ε / (max C 1))*c i := Finset.sum_le_sum fun i hi=> by
      calc
         _ = c i * (A*Real.exp (-(σ/2)*L i)) := by unfold c; rw [show σ/2*L i=σ*L i + -(σ/2)*L i by ring,Real.exp_add]; ring
         _ ≤ _ := by rw [mul_comm (ε/_)]; apply mul_le_mul_of_nonneg_left _ (by unfold c; positivity); by_contra! H; exact Finset.disjoint_left.mp ht hi (hv i H)
    _ = ε / (max C 1) * ∑ i∈t,c i := Finset.mul_sum .. |>.symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left ((h.2 _).trans (le_max_left C 1)) (by positivity : 0≤ε/(max C 1))).trans_eq (div_mul_cancel₀ _ (by positivity))
omit h

lemma limit {X : ι → α→E} {H : α→E} (ht : ∀ i, Carries C σ L (X i)) (H' : ∀ x, Tendsto (fun i=> X i x) F (𝓝 (H x))) :
    Carries C σ L H := ⟨fun i => (ht (Classical.choice (Filter.NeBot.nonempty F))).1 i,fun s=>le_of_tendsto (tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul (H' i |>.norm)) (Eventually.of_forall fun i => (ht i).2 _)⟩ -- F.nonempty

end Carries

lemma sumConvergence {u : ι → α→E} {b : α→E} (hu : ∀ i, Summable (u i)) (hb : Summable b)
    (h1 : ∀ x, Tendsto (fun i=> u i x) F (𝓝 (b x)))
    (h2 : ∀ ε : ℝ, 0< ε → ∃ s : Finset α, ∀ (t : Finset α) (i : ι), Disjoint t s → ‖∑ j∈t, u i j‖ ≤ ε) :
    Tendsto (fun i=> ∑' j,u i j) F (𝓝 (∑' j, b j)) := by
  apply Metric.tendsto_nhds.mpr; intro ε hε
  obtain ⟨s,hs⟩ := h2 (ε/3) (by positivity)
  have ht := tendsto_finsetSum s (fun j _ => h1 j)
  have he : ∀ i, ‖∑' (j : {j // j ∉ s}), u i j‖ ≤ ε/3 := by
    intro i; apply le_of_tendsto' (b:=ε/3) (((hu i).subtype (fun j=>j∉s) |>.hasSum).norm)
    intro t; have hx := hs (t.map (Function.Embedding.subtype (fun i=>i∉s))) i (by rw [Finset.disjoint_left]; simp; exact fun _ hx _=>hx)
    rwa [Finset.sum_map] at hx
  have Ht : ‖∑' (j:{j//j∉s}), b j‖ ≤ ε/3 := le_of_tendsto (hb.subtype (fun j=>j∉s) |>.hasSum.norm) (Eventually.of_forall fun t=> le_of_tendsto (x:=F) ((tendsto_finsetSum t (fun j _ => h1 j.val)).norm) (Eventually.of_forall fun i=> by
      have h := hs (t.map (Embedding.subtype (fun i=> i∉s))) i (by rw [Finset.disjoint_left]; simp; exact fun _ hx _=>hx)
      rwa [Finset.sum_map] at h))
  filter_upwards [ht.eventually (Metric.ball_mem_nhds _ (by positivity : 0<ε/3))] with i hi
  change dist (∑' j, u i j) (∑' j, b j) < ε
  change dist (∑ j∈s, u i j) (∑ j∈s, b j) < ε/3 at hi
  exact ((dist_triangle4 _ _ _ _).trans (show _ ≤ ε/3+dist (∑ j∈s, u i j) (∑ j∈s, b j) + ε/3 by
     refine add_le_add (add_le_add (by rw [dist_eq_norm, ←(hu i).sum_add_tsum_subtype_compl,add_sub_cancel_left]; exact he i) le_rfl) ?_
     rwa [dist_comm,dist_eq_norm,←hb.sum_add_tsum_subtype_compl,add_sub_cancel_left])).trans_lt (by linarith)

end YM.UVExt.Paths
