import Mathlib.Analysis.Distribution.Support
import YM.Analysis.Quadrature
import YM.Distribution.Product


/-!
# Bring a tempered distribution across an ambient compact integral

Use uniform-on-tests DCT rather than assuming Bochner integral in a Banach
Schwartz space. Reusable in C14/16 operations & boosts. NO distribution
interchanging without a correctly oriented seminorm estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spark
open Function Set Filter MeasureTheory Measure Analysis Boundary Probe
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {U X : Type*} [MetricSpace U] [CompactSpace U] [BorelSpace₀ : MeasurableSpace U] [BorelSpace U]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

abbrev Air (n : ℕ) (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] := X [×n]→L[ℝ] ℂ

def jet (x : X) (n : ℕ) : Probe X →L[ℝ] Air n X := by
  let A : Probe X →ₗ[ℝ] Air n X := {
    toFun p := iteratedFDeriv ℝ n p x
    map_add' p q := iteratedFDeriv_add_apply (p.smooth n).contDiffAt (q.smooth n).contDiffAt
    map_smul' c p := iteratedFDeriv_const_smul_apply (p.smooth n).contDiffAt }
  refine ⟨A,continuous_of_continuousAt_zero A ?_⟩
  rw [ContinuousAt,map_zero]; apply Metric.tendsto_nhds.mpr
  intro ε he
  have ht : Continuous (size 0 n (U:=X)) := cont_size ..
  have hp := (ht.tendsto 0).eventually (gt_mem_nhds (show size 0 n (0:Probe X)<ε by simpa [size] using he))
  exact hp.mono fun i hi => lt_of_le_of_lt (by rw [dist_zero_right]; exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ i n x) hi

omit [FiniteDimensional ℝ X] in
@[simp] theorem Jet (x : X) (n : ℕ) (v : Probe X) : jet x n v=iteratedFDeriv ℝ n v x := rfl

variable (μ : Measure U) [IsFiniteMeasure μ]
variable (f : U → Probe X)

omit [FiniteDimensional ℝ X] in
lemma vig (C : X → ℂ) (he : Continuous f) (h : ∀ x, C x=∫ u : U, f u x∂μ) (n : ℕ) (x : X) :
    iteratedFDeriv ℝ n C x=∫ u : U, jet x n (f u)∂μ := by
  induction n generalizing x with
  | zero =>
    simp_rw [Jet, iteratedFDeriv_zero_eq_comp]; rw [Function.comp_apply,h]
    exact ((continuousMultilinearCurryFin0 ℝ X ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ n IH =>
    let q : Air (n+1) X ≃L[ℝ] (X→L[ℝ] Air n X) := (continuousMultilinearCurryLeftEquiv ℝ (fun _ => X) ℂ).toContinuousLinearEquiv
    let y (w : X) (u : U) := q (jet w (n+1) (f u))
    have hp (w : X) : Continuous (fun i => jet w n (f i)) := (jet w n).continuous.comp he
    have hu : Continuous (y x) := q.continuous.comp ((jet x _).continuous.comp he)
    have hk u p : HasFDerivAt (fun x => jet x n (f u)) (y p u) p := by
      have heq : y p u=fderiv ℝ (iteratedFDeriv ℝ n (f u)) p := by
        unfold y; rw [Jet,iteratedFDeriv_succ_eq_comp_left]; exact q.apply_symm_apply _
      rw [heq]; exact ((f u).smooth (n+1)|>.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)) p |>.hasFDerivAt
    have hb (u : U) (p : X) : ‖y p u‖ ≤ size 0 (n+1) (f u) := by
      unfold y q
      rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv,LinearIsometryEquiv.norm_map,Jet]
      exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (f u) (n+1) p
    haveI : TopologicalSpace.PseudoMetrizableSpace (X →L[ℝ] Air n X) := q.symm.toHomeomorph.isEmbedding.isInducing.pseudoMetrizableSpace
    have ht := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ:=μ) (x₀:=x) (F:=fun w i => jet w n (f i)) (F':=y) Filter.univ_mem
      (Eventually.of_forall fun w => (hp w).aestronglyMeasurable) ((hp x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      hu.aestronglyMeasurable (Eventually.of_forall (fun i w _ => hb i w)) ((Continuous.comp (cont_size ..) he).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Eventually.of_forall fun i w _ => hk i w)
    apply q.injective
    have hg : (∫ u : U,q (jet x (n+1) (f u)) ∂μ)=q (∫ u : U,jet x (n+1) (f u)∂μ) := @ContinuousLinearEquiv.integral_comp_comm U (Air (n+1) X) (X →L[ℝ] Air n X) _ μ ℝ _ _ _ _ _ _ _ q _
    rw [← hg]
    rw [iteratedFDeriv_succ_eq_comp_left,show iteratedFDeriv ℝ n C=(fun x => ∫ u, jet x n (f u)∂μ) from funext IH]
    exact (q.apply_symm_apply _).trans ht.fderiv

open Analysis.Quad

def gore (k : ℕ) : Probe X := ∑ i,(Quad.shrink U k).mass μ i • f ((Quad.shrink U k).tag i)

omit [FiniteDimensional ℝ X] in
lemma records (G : Probe X) (h : ∀ x, G x=∫ u : U, f u x∂μ) (ht : Continuous f) : Tendsto (gore μ f) atTop (𝓝 G) := by
  refine (Probe.tendN atTop _ _).2 fun i j ε he => ?_
  let Q (k : ℕ) := Quad.shrink U k
  let J (k : ℕ) := (Q k).map
  let g : U×U→ℝ := fun p => size i j (f p.1-f p.2)
  have hg : Continuous g := (cont_size ..).comp ((ht.comp continuous_fst).sub (ht.comp continuous_snd))
  obtain ⟨C,hC⟩ := hg.norm.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  -- P.bdl returns ‖ ‖ ...
  let L (k : ℕ) (u : U) := g (J k u,u)
  have ha k : AEStronglyMeasurable (L k) μ := (hg.stronglyMeasurable.comp_measurable ((Q k).meas_map.prodMk measurable_id)).aestronglyMeasurable
  have hv k : ∀ᵐ u∂μ, ‖L k u‖≤ C := Eventually.of_forall fun u => by simpa only [L,norm_norm] using! hC (J k u,u)
  have hh x k : jet x j (gore μ f k-G) =∫ u:U, jet x j (f (J k u)-f u)∂μ := by
    rw [map_sub, Jet x j G,vig μ f G ht h]
    let Z := fun u => jet x j (f u)
    have ht' : Continuous Z := (jet ..).continuous.comp ht
    obtain ⟨b,hb⟩ := ht'.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
    have he : Integrable (fun u => Z (J k u)) μ := .of_bound
      (ht'.stronglyMeasurable.comp_measurable (Q k).meas_map).aestronglyMeasurable b (Eventually.of_forall fun i => hb _)
    simp_rw [map_sub]; rw [integral_sub he (ht'.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    rw [show (∫ u, jet x j (f (J k u))∂μ)= _ from Quad.count (Q k) μ Z]
    simp only [gore,_root_.map_sum,map_smul];rfl
  have hm k : size i j (gore μ f k-G) ≤ ∫ u, L k u∂μ := by
    apply SchwartzMap.seminorm_le_bound ℂ i j
    · exact integral_nonneg fun u => apply_nonneg ..
    intro x
    rw [← Jet,hh,← Real.norm_of_nonneg (show 0 ≤ ‖x‖^i by positivity), ← norm_smul, ← integral_smul] 
    apply norm_integral_le_of_norm_le (Integrable.of_bound (ha k) C (hv k))
    refine Eventually.of_forall fun u => ?_
    rw [norm_smul,Real.norm_of_nonneg (show 0 ≤ ‖x‖^i by positivity)]
    exact SchwartzMap.le_seminorm ℂ i j _ _
  have HH x : g (x,x)=0 := by simp [g,Probe.size]
  have heq (u : U) : Tendsto (fun k => L k u) atTop (𝓝 0) := by
    rw [← HH u]
    exact hg.continuousAt.tendsto.comp (Quad.along u|>.prodMk_nhds tendsto_const_nhds)
  have ht := tendsto_integral_of_dominated_convergence (fun u : U => C) ha (integrable_const _) hv (Eventually.of_forall heq)
  simp only [integral_zero] at ht
  exact (ht.eventually (gt_mem_nhds he)).mono fun i hi => (hm i).trans_lt hi

omit [FiniteDimensional ℝ X] in
/-- interchange, receives any Distn. Orientation invariant (ℂ-linear). -/
theorem allowance (G : Probe X) (h : ∀ x, G x=∫ u : U, f u x∂μ) (ht : Continuous f) (F : Distn X) :
    F G=∫ x : U,F (f x)∂μ := by
  let L := (F.restrictScalars ℝ)
  have hg := F.continuous.comp ht
  obtain ⟨b,hb⟩ := hg.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  let R k := Quad.map (Quad.shrink U k)
  have he : Tendsto (fun k => ∫ x : U,F (f (R k x))∂μ) atTop (𝓝 _) :=
    tendsto_integral_of_dominated_convergence (fun u => b) (fun k => (hg.stronglyMeasurable.comp_measurable (Quad.meas_map _)).aestronglyMeasurable) (integrable_const _)
      (fun k => Eventually.of_forall fun x => hb (R k x)) (Eventually.of_forall fun x => hg.continuousAt.tendsto.comp (Quad.along x))
  refine tendsto_nhds_unique_of_eventuallyEq (F.continuous.continuousAt.tendsto.comp (records μ f G h ht)) he (Eventually.of_forall (fun k => ?_))
  change L (gore μ f k)=∫ x,F (f (R k x))∂μ
  rw [show (∫ x : U,F (f (R k x))∂μ)= _ from Quad.count (Quad.shrink U k) μ (F ∘ f)]
  simp only [gore,_root_.map_sum,map_smul]; rfl
end YM.Spark
