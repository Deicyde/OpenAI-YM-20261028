import YM.Cells.Corrected
import YM.Ground.Spectrum

/-!
# Choose ANY responding ensemble with chosen chambers, unique a.e.

Countable family v_i whose SPANS of plant vectors are dense in each alpha
chamber, not dense as points. Use scalar DCT power limit of ground
norms. No separability postulated. -/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Cluster
open Set Function Filter MeasureTheory Measure Ground Word
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {V : Chamber S timeAxis}
variable (P : Spread V) (H : S.Hierarchy)

def amplitude (V : Chamber S timeAxis) (b : Future L timeAxis) := V.D.orthogonalProjectionOnto (V.GNS.plant b)
def current (S : Table L) (b : Future L timeAxis) (s : ℕ) := S.gram timeAxis (travel b (s:ℝ≥0)).val (travel b (s:ℝ≥0)).val

theorem magnitude (V : Chamber S timeAxis) (b : Future L timeAxis) (s : ℕ) : current S b s = ↑(‖V.flow.E (s:ℝ≥0) (V.GNS.plant b)‖^2) := by
  unfold current; rw [← V.GNS.measure, V.atBirth, inner_self_eq_norm_sq_to_K];norm_cast
lemma trail (V : Chamber S timeAxis) (b : Future L timeAxis) : Tendsto (current S b) atTop (𝓝 (↑(‖amplitude V b‖^2):ℂ)) := by
  rw [show current S b=(fun s : ℕ => ↑(‖V.flow.E (s:ℝ≥0) (V.GNS.plant b)‖^2)) from funext (magnitude V b)]
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp ((V.flow.emerges (V.GNS.plant b)).comp tendsto_natCast_atTop_atTop |>.norm.pow 2)

lemma side (V : Chamber S timeAxis) (b : Future L timeAxis) : inner ℂ V.omega0 (amplitude V b)=S.expect b.val := by
  unfold amplitude Chamber.omega0; simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  unfold Chamber.omega; rw [V.GNS.measure]; rfl

lemma fits (V : Chamber S timeAxis) (H : S.Basic) (b : Future L timeAxis) :
    ‖amplitude V b-S.expect b.val • V.omega0‖^2 = ‖amplitude V b‖^2-‖S.expect b.val‖^2 := by
  rw [norm_sub_sq (𝕜:=ℂ), norm_smul, show ‖V.omega0‖=1 from nil_norm V.GNS H,mul_one,inner_smul_right,← inner_conj_symm (amplitude V b),side,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [show ∀ i : ℝ, RCLike.re (K := ℂ) (↑i:ℂ)=i from fun _ => rfl]
  ring

variable {R : P.Resolution} {T : R.X → Table L} (D : ∀ i, Chamber (T i) timeAxis)

lemma track (b : L.Word) (p : distinct b) (x : R.X) (he : R.receives (T x) x) : (T x).expect b=R.character x (M P _ p) := he b p _ _ (Spread.Resolution.place_exists p).choose_spec.choose_spec
include H in
lemma champ (s : ℕ) (b : Future L timeAxis) (he : ∀ i, R.receives (T i) i) (hp : R.Out) :
    Continuous (fun i => current (T i) b s) ∧ (∫ i,current (T i) b s ∂R.μ)=current S b s := by
  let w := reflect (travel b (s:ℝ≥0)).val timeAxis ++ (travel b (s:ℝ≥0)).val
  have hh : distinct w := twoSides (travel b s).property (travel b s).property
  refine ⟨?_, R.barycenter T hp he H.translations _ hh⟩
  change Continuous (fun i => (T i).expect w); rw [show (fun i => (T i).expect w) = fun i => R.character i (M P _ hh) from funext fun i => track _ _ hh i (he i)]; exact hp.weak _

private lemma at_M (u : P.algebra) (h : R.Out) : (∫ i, ‖R.character i u‖^2 ∂R.μ)=‖u.val V.omega0‖^2 := by
  have he i : R.character i (star u*u)= ↑(‖R.character i u‖^2) := by
    rw [map_mul,map_star];change starRingEnd ℂ _ * _=_; rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  have ht := h.ground (star u*u); simp_rw [he,integral_complex_ofReal] at ht
  apply Complex.ofReal_injective; rw [ht,Complex.ofReal_pow]
  exact (ContinuousLinearMap.adjoint_inner_right u.val V.omega0 (u.val V.omega0)).trans (inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (u.val V.omega0))

include H P in
lemma exp_real (b : Future L timeAxis) (p : R.Out) (h : Steady V) (hv : ∀ i, R.receives (T i) i) (hp : ∀ i,(T i).Hierarchy) :
    ∀ᵐ i ∂R.μ, amplitude (D i) b = (T i).expect b.val • (D i).omega0 := by
  haveI := p.normalized
  let w (i : R.X) := ‖amplitude (D i) b‖^2
  have hw i : 0≤w i := sq_nonneg _
  let F s (i : R.X) := (current (T i) b s).re
  have hu k : Continuous (F k) := Complex.continuous_re.comp (champ P H k b hv p).1
  have ht i : Tendsto (fun j => F j i) atTop (𝓝 (w i)) := Complex.continuous_re.continuousAt.tendsto.comp (trail (D i) b)
  have he s : ∀ᵐ i ∂R.μ, ‖F s i‖ ≤ F 0 i := by
    apply Eventually.of_forall; intro i
    unfold F; rw [magnitude (D i),magnitude (D i),Complex.ofReal_re,Complex.ofReal_re, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (((D i).flow.norm_decrease ((D i).GNS.plant b)) (by exact_mod_cast Nat.zero_le s : ((0:ℕ):ℝ≥0)≤ (s:ℝ≥0))) 2
  have Hz := (hu 0).integrable_of_hasCompactSupport (μ := R.μ) (HasCompactSupport.of_compactSpace _)
  have hm := tendsto_integral_of_dominated_convergence (μ := R.μ) (F 0) (fun n => (hu n).aestronglyMeasurable) Hz he
    (f:= w) (Eventually.of_forall ht)
  have hf k : (∫ i, F k i ∂R.μ) = (current S b k).re := by
    rw [← (champ P H k b hv p).2]; exact (integral_re ((champ P H k b hv p).1.integrable_of_hasCompactSupport (μ:=R.μ) (HasCompactSupport.of_compactSpace _)))
  have hi : (∫ i, w i ∂R.μ)=‖amplitude V b‖^2 := by
    simp_rw [hf] at hm; exact tendsto_nhds_unique hm (Complex.continuous_re.continuousAt.tendsto.comp (trail V b))
  let k:= M P b.val b.property.1
  have HH i : (T i).expect b.val=R.character i k := track P _ b.property.1 i (hv i)
  let f (i : R.X) := w i- ‖R.character i k‖^2
  have H1 : Integrable w R.μ := ⟨aestronglyMeasurable_of_tendsto_ae _ (fun i : ℕ => (hu i).aestronglyMeasurable (μ:=R.μ))
    (Eventually.of_forall ht),hasFiniteIntegral_of_dominated_convergence Hz.2 he (Eventually.of_forall ht)⟩
  have H2 : Integrable (fun x => ‖R.character x k‖^2) R.μ := by simpa only [Pi.pow_def] using!  ((p.weak k).norm.pow 2).integrable_of_hasCompactSupport (μ := R.μ) (HasCompactSupport.of_compactSpace _)
  have Hz i : f i= ‖amplitude (D i) b-(T i).expect b.val • (D i).omega0‖^2 := by rw [fits (D i) (hp i).laws,HH]
  have hx : (∫ i,f i∂R.μ)=0 := by
    unfold f; rw [integral_sub H1 H2,at_M P k p, show k.val V.omega0=amplitude V b from almost P h b, hi,sub_self]
  have hh : ∀ᵐ i ∂R.μ, f i=0 := (integral_eq_zero_iff_of_nonneg (f:= f) (fun i => (Hz i).symm ▸ sq_nonneg _) (H1.sub H2)).1 hx
  filter_upwards [hh] with i hi; rw [Hz] at hi; exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa only [sq_eq_zero_iff] using hi))

abbrev horizon (V : Chamber S timeAxis) (i : ℕ → Future L timeAxis) := DenseRange (Finsupp.linearCombination ℂ
    (fun x => V.GNS.plant (i x)))

lemma lifts {P : Spread V} {R : P.Resolution} {T : R.X→Table L} (D : ∀ i, Chamber (T i) timeAxis) (f : ℕ→Future L timeAxis)
    (hp : ∀ i, horizon (D i) f) (H : S.Hierarchy) (h : Steady V) (hT : ∀ i,(T i).Hierarchy) (r : R.Out) (hr : ∀ i,R.receives (T i) i) :
    ∀ᵐ i ∂R.μ,(D i).UniqueHeat := by
  have hi := ae_all_iff.mpr (fun b : ℕ => exp_real P H D (f b) r h hr hT)
  filter_upwards [hi] with i hx
  let Q := D i
  let U : Submodule ℂ Q.D := Submodule.span ℂ {Q.omega0}
  have he : DenseRange (Q.D.orthogonalProjectionOnto ∘ Finsupp.linearCombination ℂ (fun x => (D i).GNS.plant (f x))) :=
    (show Surjective _ from fun p => ⟨_, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self p⟩).denseRange.comp (hp i) Q.D.orthogonalProjectionOnto.continuous
  have ht (x : ℕ→₀ℂ) : Q.D.orthogonalProjectionOnto (Finsupp.linearCombination ℂ (fun x => (D i).GNS.plant (f x)) x) ∈ U := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y X Y => simpa only [map_add] using! U.add_mem X Y
    | single j c =>
      simp_rw [Finsupp.linearCombination_single,map_smul]
      exact U.smul_mem _ ((Submodule.mem_span_singleton).2 ⟨_,(hx j).symm⟩)
  intro v
  suffices hx : v∈ U from (Submodule.mem_span_singleton).1 hx
  refine closure_minimal ?_ (show IsClosed (U : Set _) from (by unfold U; exact Submodule.closed_of_finiteDimensional _)) (he v)
  rintro _ ⟨x,rfl⟩; exact ht x
lemma selects (f : ℕ→Future L timeAxis) (hp : ∀ i, horizon (D i) f) (H : S.Hierarchy) (h : Steady V)
    (hT : ∀ i,(T i).Hierarchy) (r : R.Out) (hr : ∀ i,R.receives (T i) i) : ∃ i, (D i).UniqueHeat := by
  haveI := r.normalized
  exact (lifts D f hp H h hT r hr).exists
end YM.OS.Cluster
