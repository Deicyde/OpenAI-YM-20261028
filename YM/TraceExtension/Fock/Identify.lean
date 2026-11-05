import YM.TraceExtension.Fock.Multipliers
import YM.TraceExtension.WilsonTrace

/-! Embedding in the free Fock system in wave function coordinates. `Nfl`
is on the vacuum matrix elements (computed with Weyl acting on vacuum),
no condition on unbounded field products in comparing theory. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical

/-- Symmetric transverse wave -/
structure PhysicalWave {m : ℕ} (x : Ambient m) : Prop where
    projects (n : ℕ) (s : Tags m n) (i : Fin n) : ∀ᵐ k∂photons n, x (insertP ⟨n,s⟩ k) =
      ∑ j : SpaceAxis, polarization (k i) (s i).2 j * x (insertP ⟨n,update s i ((s i).1,j)⟩ k)
    symmetric (n : ℕ) (s : Tags m n) (r : Equiv.Perm (Fin n)) : ∀ᵐ k∂photons n,
      x (insertP ⟨n,s ∘ r⟩ (k ∘ r)) = x (insertP ⟨n,s⟩ k)

variable {G : Gauge} {C : Family G} {a : Extraction.Order} {S : Table C.book}
    {F : Spec.Final C a S} {μ : Measure E4} {m n : ℕ} {U : F.action.operators.H →ₗᵢ[ℂ] Ambient m}

structure Comparison (F : Spec.Final C a S) (U : F.action.operators.H →ₗᵢ[ℂ] Ambient m) : Prop where
    ambient v : PhysicalWave (U v)
    unit : U F.action.operators.vacuum=vacuum m
    translates (v : F.action.operators.H) (b : E4) : ∀ᵐ x∂sumMeasure m,
      U (F.action.action.orbit.translation b v) x = Probe.plane (forward x) b * U v x

abbrev signal (F : Spec.Final C a S) (U : F.action.operators.H →ₗᵢ[ℂ] Ambient m) (f : Test4) : Ambient m := U (excitation F.action.operators (pinned F) f)

/-- `eq:nfl`, using compact smooth probes for Weyls. -/
def Nfl (F : Spec.Final C a S) (U : F.action.operators.H →ₗᵢ[ℂ] Ambient m) := ∀ (f : Test4) (h : TestList m),
    HasCompactSupport ⇑f → (∀ i, HasCompactSupport ⇑(h i)) →
    (∀ i, Probe.bar (h i)=h i) → (∀ i, Fields.causal f (h i)) →
    inner ℂ (coherent (-h)) (signal F U f)=inner ℂ (signal F U (Probe.bar f)) (coherent h)

lemma push_norm (X : Comparison F U) (v : F.action.operators.H) :
    F.action.momentum.diagonal v=(modulus (U v)).map forward := by
    apply Measure.ext_of_charFun; ext1 b
    rw [F.realization.qt.spectral,← U.inner_map_map,lp_inner,charFun_apply,
       integral_map measurable_forward.aemeasurable]
    swap
    · exact (show Continuous (fun y:E4 => Probe.plane y b) from by unfold Probe.plane; fun_prop).aestronglyMeasurable
    rw [modulus, integral_withDensity_eq_integral_toReal_smul _ (ae_of_all _ fun x => (by finiteness : (‖U v x‖ₑ)^2 < ⊤))]
    · apply integral_congr_ae; filter_upwards [X.translates v b] with x hx
      rw [hx]; change star (U v x)*(Probe.plane _ _*U v x)=_ • (Probe.plane _ _)
      rw [← ofReal_norm,← ENNReal.ofReal_pow (norm_nonneg _),ENNReal.toReal_ofReal (sq_nonneg _),Complex.real_smul,← square_scalar]; ring
    simp_rw [← ofReal_norm]; exact lp_weight_coe _

lemma modulus_plus (μ : Measure E4) [μ.HasTemperateGrowth] (f : Probe E4) : modulus (SchwartzMap.toLpCLM ℂ ℂ 2 μ (testPlus f))=μ.withDensity (fun i => (probeWeight f i:ℝ≥0∞)) := by
    unfold modulus; apply withDensity_congr_ae; filter_upwards [MemLp.coeFn_toLp (SchwartzMap.memLp (testPlus f) 2 μ)] with i hi
    rw [show SchwartzMap.toLpCLM ℂ ℂ 2 μ (testPlus f) i = _ from hi]; simp [probeWeight,enorm_eq_nnnorm]

def excitationLinear (F : Spec.Final C a S) (U : F.action.operators.H →ₗᵢ[ℂ] Ambient m) : Probe E4 →ₗ[ℂ] Ambient m :=
    U.toLinearMap.comp (F.action.operators.domain.subtype.comp ((LinearMap.applyₗ (R:=ℂ) F.action.operators.omega).comp
      (F.action.operators.field (pinned F))))
lemma excitationLinear_eval (f : Probe E4) : excitationLinear F U f = signal F U f := rfl

lemma bK (f : Probe E4) : ∃ C : ℝ, ∀ i, ‖f i‖ ≤ C := ⟨Probe.size 0 0 f,fun i => by simpa using SchwartzMap.le_seminorm ℂ 0 0 f i⟩

def mx (m) (f : Probe E4) := mult2 (sumMeasure m) (f ∘ forward) (f.continuous.measurable.comp measurable_forward) ⟨(bK f).choose,fun i => (bK f).choose_spec (forward i)⟩
def my (μ : Measure E4) (f : Probe E4) := mult2 μ f f.continuous.measurable (bK f)
def sy (μ : Measure E4) [μ.HasTemperateGrowth] := ((SchwartzMap.toLpCLM ℂ ℂ 2 μ).comp testPlus).toLinearMap
lemma cross_measure (X : Comparison F U) (h : TraceSpectrum F μ) (f g : Probe E4) (k l : Probe E4) :
    letI := h.upper
    inner ℂ (mx m k (signal F U f)) (mx m l (signal F U g))=
    inner ℂ (my μ k (sy μ f)) (my μ l (sy μ g)) := by
    haveI := h.upper
    refine cross_inner ((mx m k).comp (excitationLinear F U)) ((mx m l).comp (excitationLinear F U))
      ((my μ k).comp (sy μ)) ((my μ l).comp (sy μ)) ?_ f g
    intro x; simp only [LinearMap.comp_apply, excitationLinear_eval]; unfold mx my
    rw [mult_square,mult_square,show modulus (sy μ x) = _ from modulus_plus μ x,← h.core,push_norm X]
    rw [integral_map measurable_forward.aemeasurable]
    · rfl
    exact (show Continuous (fun p:E4 => star (k p)*l p) from by fun_prop).aestronglyMeasurable

lemma wave_compat (X : Comparison F U) (h : TraceSpectrum F μ) (f g : Probe E4) : ∀ᵐ x∂sumMeasure m,
    testPlus g (forward x) * signal F U f x = testPlus f (forward x)*signal F U g x := by
    haveI := h.upper
    let t (f g : Probe E4) := mx m (testPlus g) (signal F U f)
    let r (f g : Probe E4) := my μ (testPlus g) (sy μ f)
    have hp (f g q u) : inner ℂ (t f g) (t q u)=inner ℂ (r f g) (r q u) := cross_measure X h ..
    have hm (f g) : ⇑(r f g)=ᵐ[μ] ⇑(testPlus f) * testPlus g := by
      unfold r my; refine (mult_eq _ _ _ _).trans ?_
      rw [mul_comm]; exact Filter.EventuallyEq.mul (MemLp.coeFn_toLp (SchwartzMap.memLp (testPlus f) 2 μ)) EventuallyEq.rfl
    have he : r f g=r g f := Lp.ext ((hm f g).trans (by rw [mul_comm]; exact (hm g f).symm))
    have hE : t f g=t g f := by apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).1; simp only [inner_sub_left,inner_sub_right,hp,he,sub_self]
    have hx (f g) : ⇑(t f g) =ᵐ[sumMeasure m] (fun x => testPlus g (forward x)*signal F U f x) := mult_eq _ _ _ _
    exact (hx f g).symm.trans (by rw [hE]; exact hx g f)
end YM.TraceExtension.Photons
