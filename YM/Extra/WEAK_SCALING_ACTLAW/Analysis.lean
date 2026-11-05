import YM.Extra.WEAK_SCALING_ACTLAW.Geometry
import YM.Work.B06

/-!
# Directional finite rows, continuous convergence and k-grid interpolation

Small weighted gradients (scale = size of a rescaled grid step, Torus
mesh refinements aren't performed here) and aligned-generic convergence
suffice on open sets. Used twice: first with coordinate transfer off the
tie sets; then, after the derivative fits, on full open separated windows
including collinear tests. Need also the matrix norms, not just univariate
partial derivatives at individual points.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Set Function Filter Extraction MeasureTheory
open scoped Topology ContDiff

section analysis
variable {ι A : Type*} [Fintype ι] {l : Filter A}

lemma multi_fitted {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : A → MultilinearMap ℂ V X) (g : MultilinearMap ℂ V X)
    (h : ∀ v, Tendsto (fun k => f k v) l (𝓝 (g v)))
    {u : A → ∀ i, V i} {x : ∀ i, V i} (hu : ∀ i, Tendsto (fun k => u k i) l (𝓝 (x i))) :
    Tendsto (fun k => f k (u k)) l (𝓝 (g x)) := by
  classical
  let B (i : ι) := Module.finBasis ℂ (V i)
  have he (F : MultilinearMap ℂ V X) (y : ∀ i, V i) : F y =
      ∑ a : ((i : ι) → Fin (Module.finrank ℂ (V i))), (∏ i, (B i).repr (y i) (a i)) • (F fun i => B i (a i)) := by
    have ht : (fun i => ∑ j, (B i).repr (y i) j • (B i) j) = y := funext fun i => (B i).sum_repr _
    conv_lhs => rw [← ht]
    rw [MultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun a _ => F.map_smul_univ _ _
  conv => arg 1; intro k; rw [he]
  rw [he g x]
  refine tendsto_finsetSum _ fun a _ => ?_
  refine (tendsto_finsetProd _ fun i _ => ?_).smul (h _)
  exact (((B i).coord (a i)).continuous_of_finiteDimensional.tendsto _).comp (hu i)

/-- Convergence of finite matrices suffices. -/
lemma norm_fit {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (f : E →ₗ[ℝ] X) (h : Injective f) {a : Y → E} {e : E} {s : Filter Y}
    (he : Tendsto (fun y => f (a y)) s (𝓝 (f e))) : Tendsto a s (𝓝 e) := by
  obtain ⟨g,hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr h)
  have hp (x : E) : g (f x)=x := LinearMap.congr_fun hg x
  have ht := (g.continuous_of_finiteDimensional.tendsto _).comp he
  simpa [comp_def,hp] using ht

variable {m n : ℕ}

lemma components (v : Points n) : v = ∑ i : Fin n × Axis, v i.1 i.2 • Points.direction i.1 i.2 := by
  apply Points.flatten.injective
  apply PiLp.ext
  rintro ⟨i,a⟩
  rw [map_sum]; simp [← Finset.univ_product_univ, Finset.sum_product, map_smul, Points.direction,
    PiLp.single_apply, apply_ite, ite_apply, Finset.sum_ite_irrel]

/-- Actual Fréchet norm convergence from coordinate-direction convergence. -/
lemma norm_fit_deriv {f : A → Points n →L[ℝ] ℂ} {g : Points n →L[ℝ] ℂ}
    (h : ∀ (i : Fin n × Axis), Tendsto (fun k => f k (Points.direction i.1 i.2)) l
        (𝓝 (g (Points.direction i.1 i.2)))) : Tendsto f l (𝓝 g) := by
  let p : (Points n →L[ℝ] ℂ) →ₗ[ℝ] ((Fin n × Axis) → ℂ) := LinearMap.pi fun i =>
    (ContinuousLinearMap.apply ℝ ℂ (Points.direction i.1 i.2)).toLinearMap
  refine norm_fit p ?_ (tendsto_pi_nhds.mpr h)
  intro u v e; ext1 x; rw [components x, map_sum,map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul,map_smul]; exact congrArg _ (congrFun e i)

lemma norm_fit_jet {f : A → Tensor.T (Points n) ℂ m} {g : Tensor.T (Points n) ℂ m}
    (h : ∀ v : Fin m → Fin n × Axis, Tendsto (fun k => f k (fun j => Points.direction (v j).1 (v j).2)) l
        (𝓝 (g fun j => Points.direction (v j).1 (v j).2))) : Tendsto f l (𝓝 g) := by
  let p : (Tensor.T (Points n) ℂ m) →ₗ[ℝ] ((Fin m → Fin n × Axis) → ℂ) := LinearMap.pi fun v =>
    (ContinuousMultilinearMap.apply ℝ _ ℂ (fun j => Points.direction (v j).1 (v j).2)).toLinearMap
  refine norm_fit p ?_ (tendsto_pi_nhds.mpr h)
  intro F G e; ext1 v
  change F.toMultilinearMap v = G.toMultilinearMap v
  rw [show v = _ from funext (fun i => components (v i)),MultilinearMap.map_sum,MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ => Eq.trans (F.map_smul_univ _ _) ?_
  exact (congrArg (fun z : ℂ => (_ : ℝ) • z) (congrFun e s)).trans (G.map_smul_univ _ _).symm

variable {X Y : Type*} [MetricSpace X] [NormedAddCommGroup Y]

/-- Local continuous convergence along stations. -/
def Follows (O : Set X) (F : ℕ → X → Y) (g : X → Y) : Prop := ∀ s : ℕ → ℕ, Tendsto s atTop atTop →
    ∀ x ∈ O, ∀ z : ℕ → X, Tendsto z atTop (𝓝 x) → Tendsto (fun i => F (s i) (z i)) atTop (𝓝 (g x))

lemma Follows.onCompact {F : ℕ → X → Y} {g : X → Y} {O K : Set X} (h : Follows O F g)
    (hK : IsCompact K) (he : K ⊆ O) (hg : ContinuousOn g K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ K, ‖F k x - g x‖ ≤ ε := by
  by_contra! ht
  choose s hs x hx hE using frequently_atTop.mp ht
  obtain ⟨y,hy,u,hu,hl⟩ := hK.tendsto_subseq hx
  have hp := h (s ∘ u) (tendsto_atTop_mono (fun i => hs (u i)) hu.tendsto_atTop) y (he hy) _ hl
  have hP := (hg y hy).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hl,Eventually.of_forall (fun i => hx (u i))⟩)
  have hw := ((hp.sub hP).norm).eventually (gt_mem_nhds (by simpa using hε : ‖g y - g y‖ < ε))
  obtain ⟨i,hi⟩ := hw.exists
  exact (hE (u i)).asymm hi

/-- Convergence only checked at generic samples aligned on the current coarse grid,
whose spacing h is expressed in the *rescaled* coordinates. -/
def Sampled (O : Set (Points n)) (h : ℕ → ℝ) (F : ℕ → Points n → ℂ) (g : Points n → ℂ) : Prop :=
    ∀ s : ℕ → ℕ, Tendsto s atTop atTop → ∀ x ∈ O, ∀ z : ℕ → Fin n → Lattice.Cover,
      Tendsto (fun i => tag (h (s i)) (z i)) atTop (𝓝 x) → (∀ᶠ i in atTop, tag (h (s i)) (z i) ∈ generic n) →
        Tendsto (fun i => F (s i) (tag (h (s i)) (z i))) atTop (𝓝 (g x))

lemma interpolate {O : Set (Points n)} (hO : IsOpen O) {h : ℕ → ℝ} (hp : ∀ k, 0 < h k)
    (hlim : Tendsto h atTop (𝓝 0)) {F : ℕ → Points n → ℂ} {g : Points n → ℂ}
    (hf : ∀ k x, x ∈ O → DifferentiableAt ℝ (F k) x) (hw : Sampled O h F g)
    (H : ∀ (j : Fin n × Axis), Follows O
      (fun k x => h k • (fderiv ℝ (F k) x (Points.direction j.1 j.2))) 0) : Follows O F g := by
  have he : Follows O (fun k x => h k • fderiv ℝ (F k) x) 0 :=
    fun s hs x hx z hz => norm_fit_deriv (fun j => H j s hs x hx z hz)
  intro s hs x hx z hz
  obtain ⟨δ,hδ,hd⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hx)
  let K := Metric.closedBall x δ
  let u (i : ℕ) := sample (h (s i)) (z i)
  let v (i : ℕ) := tag (h (s i)) (u i)
  let B : ℝ := 4*n*(2*n+1)+1
  have hB : 0<B := by dsimp [B]; positivity
  have hdist (i : ℕ) : dist (v i) (z i) ≤ B*h (s i) :=
    (sample_bound (hp (s i)) (z i)).trans (by dsimp [B]; linarith [hp (s i)])
  have hv : Tendsto v atTop (𝓝 x) := hz.congr_dist (squeeze_zero (fun _ => dist_nonneg)
    (fun i => (dist_comm _ _).trans_le (hdist i))
    (by simpa [comp_def] using ((hlim.comp hs).const_mul B)))
  refine (hw s hs x hx u hv (Eventually.of_forall (fun i => sample_clear (hp _) (z i)))).congr_dist ?_
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hw := hs.eventually (he.onCompact (isCompact_closedBall x δ) hd continuousOn_const
    (by positivity : 0<ε/(2*B)))
  filter_upwards [hz.eventually (Metric.closedBall_mem_nhds x hδ), hv.eventually (Metric.closedBall_mem_nhds x hδ),hw]
    with i hi hi' he
  have h' : 0 < h (s i) := hp _
  have he' y (hy : y ∈ K) : ‖fderiv ℝ (F (s i)) y‖ ≤ ε / (2*B) / h (s i) := by
    apply (le_div_iff₀' h').mpr
    have hi := he y hy
    rwa [Pi.zero_apply,sub_zero,norm_smul, Real.norm_eq_abs,abs_of_pos h'] at hi
  rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg,dist_eq_norm]
  calc
    ‖F (s i) (v i) - F (s i) (z i)‖ ≤ _ := (convex_closedBall x δ).norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => hf _ y (hd hy)) he' hi hi'
    _ ≤ (ε/(2*B) / h (s i))*(B*h (s i)) := by rw [← dist_eq_norm]; gcongr; exact hdist i
    _ = ε/2 := by field_simp
    _ < ε := half_lt_self hε

end analysis
end YM.Extra.WeakScaling
