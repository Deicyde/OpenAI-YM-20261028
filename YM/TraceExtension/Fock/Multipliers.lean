import YM.TraceExtension.Fock.Weyl

/-! Elementary L² polarization. Recover direction, not just magnitude, of a wave. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary
open scoped Topology NNReal ENNReal BigOperators ComplexOrder InnerProductSpace Classical

lemma cross_inner {V X Y : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (A B : V →ₗ[ℂ] X) (S T : V →ₗ[ℂ] Y)
    (h : ∀ x : V, inner ℂ (A x) (B x)=inner ℂ (S x) (T x)) (x y : V) :
    inner ℂ (A x) (B y)=inner ℂ (S x) (T y) := by
    have he := h (x+y); have hf := h (x+Complex.I • y)
    simp only [map_add,map_smul,inner_add_right,inner_add_left,inner_smul_right,inner_smul_left,h x,h y] at he hf
    rw [conj_I] at hf
    linear_combination (norm := (ring_nf; rw [Complex.I_sq]; ring)) he / 2 - Complex.I / 2 * hf

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
abbrev Two (μ : Measure X) := Lp ℂ 2 μ
lemma lp_inner (x y : Two μ) : inner ℂ x y = ∫ a, star (x a)*y a ∂μ := by
    rw [L2.inner_def]; congr! 1; ext a
    rw [RCLike.inner_apply,mul_comm]; rfl
lemma lp_weight_coe (x : Two μ) : Measurable (fun p => ENNReal.ofReal ‖x p‖^2) :=
    Measurable.pow_const ((Lp.stronglyMeasurable x).measurable.norm.ennreal_ofReal) _

lemma multiplier (f : X → ℂ) (hc : Measurable f) (hb : ∃ C : ℝ, ∀ i, ‖f i‖ ≤ C) (v : Two μ) : MemLp (fun i => f i*v i) 2 μ := by
    obtain ⟨C,h⟩ := hb
    refine ((Lp.memLp v).const_mul (C:ℂ)).mono (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable v)) ?_
    filter_upwards with i
    simp only [norm_mul,Complex.norm_real]
    rw [Real.norm_of_nonneg ((norm_nonneg _).trans (h i))]; gcongr; exact h _

def mult2 (μ : Measure X) (f : X → ℂ) (hc : Measurable f) (hb : ∃ C : ℝ, ∀ i, ‖f i‖ ≤ C) : Two μ →ₗ[ℂ] Two μ where
    toFun v := (multiplier f hc hb v).toLp _
    map_add' v w := by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (multiplier f hc hb (v+w)), Lp.coeFn_add v w,
          Lp.coeFn_add ((multiplier f hc hb v).toLp _) ((multiplier f hc hb w).toLp _), MemLp.coeFn_toLp (multiplier f hc hb v), MemLp.coeFn_toLp (multiplier f hc hb w)] with i hv hh hp hs hq
        rw [hv,hp,hh,Pi.add_apply,Pi.add_apply,hq,hs,mul_add]
    map_smul' t v := by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (multiplier f hc hb (t•v)), Lp.coeFn_smul t v,
          Lp.coeFn_smul t ((multiplier f hc hb v).toLp _), MemLp.coeFn_toLp (multiplier f hc hb v)] with i hv hh hp hs
        rw [hv,RingHom.id_apply,hp,hh,Pi.smul_apply,Pi.smul_apply,hs,smul_eq_mul,smul_eq_mul,mul_left_comm]

lemma mult_eq (f : X→ℂ) (hc hb) (v : Two μ) : (⇑(mult2 μ f hc hb v) : X→ℂ) =ᵐ[μ] f* v :=
    MemLp.coeFn_toLp (multiplier f hc hb v)

def modulus (x : Two μ) := μ.withDensity fun p => (‖x p‖ₑ)^2
instance modulus_finite (x : Two μ) : IsFiniteMeasure (modulus x) := by
    apply isFiniteMeasure_withDensity
    have ht := (Lp.memLp x).norm.integrable_sq.hasFiniteIntegral
    simpa only [HasFiniteIntegral, lt_top_iff_ne_top, ← ofReal_norm,norm_pow, norm_norm,ENNReal.ofReal_pow (norm_nonneg _)] using ht

omit [MeasurableSpace X] in
lemma mul_bound (f g : X → ℂ) (hc : ∃ C : ℝ, ∀ i, ‖f i‖≤C) (hd : ∃ C : ℝ, ∀ i, ‖g i‖ ≤ C) : ∃ C : ℝ, ∀ i, ‖star (f i) * g i‖ ≤ C := by
    obtain ⟨A,h⟩ := hc; obtain ⟨B,t⟩ := hd; refine ⟨A*B,fun i => ?_⟩
    rw [norm_mul,norm_star]; exact mul_le_mul (h i) (t i) (norm_nonneg _) ((norm_nonneg (f i)).trans (h i))
lemma square_scalar (z : ℂ) : star z*z= (↑(‖z‖^2):ℂ) := by rw [mul_comm,Complex.star_def,mul_conj,normSq_eq_norm_sq]
lemma mult_square (f g : X → ℂ) (hf hg hF hG) (x : Two μ) : inner ℂ (mult2 μ f hf hF x) (mult2 μ g hg hG x) =
    ∫ p, star (f p)*g p ∂modulus x := by
    rw [lp_inner,modulus,integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      filter_upwards [mult_eq f hf hF x, mult_eq g hg hG x] with i hi hj
      rw [hi,hj]; simp only [Pi.mul_apply,← ofReal_norm,← ENNReal.ofReal_pow (norm_nonneg _),ENNReal.toReal_ofReal (by positivity : 0≤‖x i‖^2),Complex.real_smul]
      rw [← square_scalar (x i),star_mul]; ring
    · simp_rw [← ofReal_norm]; exact lp_weight_coe x
    exact ae_of_all _ fun i => by finiteness
end YM.TraceExtension.Photons
