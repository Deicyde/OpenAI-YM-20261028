import YM.Progress.DIRECTED_RECIPE.Recipe
import YM.Progress.DIRECTED_RECIPE.Vacuum
import YM.Work.C13.Decay
import YM.Work.G07.Calculus


/-!
# A scalar without assuming it is continuous

Pay this part from the full `Q` curve, whose price is at *fixed period*.
No hypothesis here of Borel K arguments being continuous through their
masks. Kernel probabilities still sum over physical tags. In particular
noise at V is common with the actual estimate tasks. Proves positivity,
joint sup/norm comparison usability on these ancestor families at every
admitted parameter. No claim of analyticity or differentiability in β.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe
open Function Set RG Wilson Lattice RG.Shoot MeasureTheory Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}
section Block
variable {c f : Side} (S : StepData c f)

lemma penalty_cont : Continuous fun p : ℝ × G.El => S.penaltyWeight p.1 p.2 := by
  unfold StepData.penaltyWeight; fun_prop

lemma z_cont : Continuous fun β : ℝ => S.penaltyZ β G := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  let T := Icc (x-1) (x+1)
  obtain ⟨C,hC⟩ := (IsCompact.prod (s:=T) isCompact_Icc isCompact_univ).bddAbove_image
    ((penalty_cont S (G:=G)).norm.continuousOn)
  have he : ContinuousOn (fun β => S.penaltyZ β G) T := by
    refine continuousOn_of_dominated (μ:=G.probHaar) (F:=fun β => S.penaltyWeight β) (bound:=fun _ => C) ?_
      (fun y hy => Eventually.of_forall fun i => hC ⟨(y,i),⟨hy,mem_univ _⟩,rfl⟩) (integrable_const C) ?_
    · exact fun _ _ => (S.penaltyWeight_cont _).measurable.aestronglyMeasurable
    refine Eventually.of_forall fun i => Continuous.continuousOn ?_
    change Continuous ((fun p : ℝ × G.El => S.penaltyWeight p.1 p.2) ∘ fun b : ℝ => (b,i))
    exact (penalty_cont S).comp (continuous_id.prodMk continuous_const)
  have ht : x∈T := ⟨by linarith,by linarith⟩
  exact (he x ht).continuousAt (Icc_mem_nhds (by linarith) (by linarith))

lemma noise_banded : Continuous fun v : ℝ × (Config G c × Config G c) => S.noise v.1 v.2.1 v.2.2 := by
  unfold StepData.noise
  apply continuous_finsetProd
  intro k _
  refine Continuous.mul (Continuous.inv₀ ((z_cont S).comp continuous_fst) ?_) ?_
  · exact fun _ => (S.penaltyZ_pos _).ne'
  change Continuous ((fun p : ℝ × G.El => S.penaltyWeight p.1 p.2) ∘
    fun v : ℝ × (Config G c × Config G c) => (v.1, v.2.2 k * (v.2.1 k)⁻¹))
  exact (penalty_cont S).comp (by fun_prop)

lemma oneField (U : Config G f) : Continuous fun p : ℝ × Config G c => S.density p.1 U p.2 := by
  unfold StepData.density
  apply continuous_finsetSum
  intro i _
  refine Continuous.const_mul ?_ _
  change Continuous ((fun v : ℝ × (Config G c × Config G c) => S.noise v.1 v.2.1 v.2.2) ∘
    fun x : ℝ × Config G c => (x.1,(S.prediction U i,x.2)))
  exact (noise_banded S).comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))

/-- Compact real parameters suffice for this, no branching slack (for *V*
at output). -/
lemma across {T : Set ℝ} (hT : IsCompact T) (hS : S.patch.Branches S.kernel G) :
    ∃ C : ℝ, ∀ β∈T, ∀ U : Config G f, ∀ V, S.density β U V ≤ C := by
  obtain ⟨C,h⟩ := (IsCompact.prod hT isCompact_univ).bddAbove_image (noise_banded (G:=G) S).continuousOn
  refine ⟨C,fun β hb U V => ?_⟩
  calc
    _ ≤ ∑ t, S.likelihood U t * C := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (h ⟨(β,(S.prediction U i,V)),⟨hb,mem_univ _⟩,rfl⟩) (S.likelihood_pos _ _)
    _ = C := by rw [← Finset.sum_mul,S.chosen hS,one_mul]
end Block

lemma motion_eval {G : Gauge} {a : Levels G} {T : Set ℝ} {R : Recipe a}
    {N m p : ℕ} {Q : ℝ → Rep G (a.S.side m p)} (h : Curve (a.budget m) Q T)
    (hg : ∀ x∈T, Lives R N m p (Q x)) (hi : ∀ x∈T, Continuous (Q x).eval) :
    ContinuousOn (fun z : ℝ × Config G (a.S.side m p) => (Q z.1).eval z.2) (T ×ˢ univ) := by
  rintro ⟨x,U⟩ hx
  have hh := eval_varies hx.1 h (fun i hz => (hg i hz).valid) (fun i hz => (hg i hz).point)
    (fun i hz => (hg i hz).clip) (fun i hz => (hg i hz).path)
  let v := 𝓝[T] x ×ˢ 𝓝 U
  apply Metric.tendsto_nhds.mpr
  intro ε hp
  simp only [nhdsWithin_prod_eq, nhdsWithin_univ]
  filter_upwards [(show Tendsto Prod.fst v (𝓝[T] x) from tendsto_fst).eventually (hh (ε/2) (by linarith)),
    (Metric.tendsto_nhds.mp ((hi x hx.1).continuousAt.tendsto.comp (show Tendsto Prod.snd v (𝓝 U) from tendsto_snd))) (ε/2) (by linarith)] with i ht hv
  have he : dist ((Q i.1).eval i.2) ((Q x).eval i.2) ≤ ε/2 := by rw [dist_comm,dist_eq_norm]; exact ht i.2
  exact lt_of_le_of_lt (dist_triangle _ ((Q x).eval i.2) _) ((add_lt_add_of_le_of_lt he hv).trans_eq (by ring))

variable {a : Levels G} {T : Set ℝ} {R : Recipe a} {N m p : ℕ} {Q : ℝ → Rep G (a.S.side (m+1) p)}
variable (hT : IsCompact T) (h : Curve (a.budget (m+1)) Q T) (hv : ∀ x∈T, Lives R N (m+1) p (Q x))
variable (hc : ∀ x∈T, Continuous (Q x).eval)
include hT h hv hc

lemma passes_density : ContinuousOn
    (fun z : ℝ × Config G (a.S.side m p) => (a.clock.op m p).push (Q z.1).beta (Q z.1).eval z.2) (T ×ˢ univ) := by
  let f := a.S.side (m+1) p
  let c := a.S.side m p
  let S := a.clock.op m p
  let A x := (Q x).beta
  have hh := motion_eval h hv hc
  obtain ⟨C,hC⟩ := (hT.prod isCompact_univ).bddAbove_image hh.norm
  obtain ⟨E,hE⟩ := across S (hT.image_of_continuousOn h.beta) (a.blocks m p).branches
  let v : ℝ × Config G c → Config G f → ℝ := fun x U => S.density (A x.1) U x.2 • (Q x.1).eval U
  refine continuousOn_of_dominated (F:=v) (μ:=prior G f) (bound:=fun _ => max E 1 * C) (fun x hx => ?_)
    (fun x hx => Eventually.of_forall fun i => ?_) (integrable_const _) ?_
  · exact (StepData.push_slice (a.transition_mass ..) _ _
      (((Q _).envelope (hv x.1 hx.1).valid).integrable _)).aestronglyMeasurable
  · unfold v
    rw [norm_smul, Real.norm_of_nonneg (S.density_positive ..)]
    refine mul_le_mul ((hE _ ⟨x.1,hx.1,rfl⟩ i x.2).trans (le_max_left ..))
      (hC ⟨(x.1,i),⟨hx.1,mem_univ i⟩,rfl⟩) (norm_nonneg _) (le_max_of_le_right zero_le_one)
  refine Eventually.of_forall fun i => ?_
  have hg : ContinuousOn ((fun x : ℝ × Config G c => S.density x.1 i x.2) ∘
      fun x : ℝ × Config G c => (A x.1,x.2)) (T ×ˢ univ) := by
    apply ContinuousOn.comp ((oneField S i).continuousOn (s:=univ)) _ (mapsTo_univ _ _)
    exact (ContinuousOn.comp h.beta (continuous_fst.continuousOn (s:=T ×ˢ univ)) (fun _ h => h.1)).prodMk
      continuous_snd.continuousOn
  have hq : ContinuousOn ((fun x : ℝ × Config G f => (Q x.1).eval x.2) ∘
      fun x : ℝ × Config G c => (x.1,i)) (T ×ˢ univ) :=
    ContinuousOn.comp hh (continuous_fst.prodMk continuous_const).continuousOn (fun _ h => ⟨h.1,mem_univ i⟩)
  exact ContinuousOn.mul hg hq

lemma scalar_curve (hp : ∀ x∈T, 0 < (a.clock.op m p).push (Q x).beta (Q x).eval 1) :
    ContinuousOn (fun x => flatRate a m p (Q x)) T := by
  have ht : ContinuousOn (fun x => (a.clock.op m p).push (Q x).beta (Q x).eval 1) T := by
    change ContinuousOn ((fun z : ℝ × Config G (a.S.side m p) =>
      (a.clock.op m p).push (Q z.1).beta (Q z.1).eval z.2) ∘
      fun x : ℝ => (x, (1:Config G (a.S.side m p)))) T
    exact (passes_density hT h hv hc).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun _ h => ⟨h,mem_univ _⟩)
  exact ContinuousOn.div_const (ht.log fun x hx => (hp x hx).ne') _

end YM.Progress.DirectedRecipe
