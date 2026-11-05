import YM.EveryPhase.Surjective
import YM.EveryPhase.Pack
/-!
# Spectral calculus at E=0

Throughout use the full zero-energy projection, not assuming it equals
the projection on the vacuum line. Identify it using the OS semigroup
and the lifted spectral measure, and transport with the actual (now
surjective) attachment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Set Filter MeasureTheory Measure Boundary Probe Spec Next.BOUNDARY
open scoped Topology NNReal InnerProductSpace ComplexOrder ComplexConjugate

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {F : Final C f S} (L : Almanac F)

lemma reaches (i : F.α.space.X) : Surjective (L.J i) := by
  obtain ⟨Y,hY,h⟩ := (L.cards i).reveals
  obtain ⟨hv,hx⟩ := h _ (L.cores i).induced
  rw [← L.spins i] at hv
  exact onto (L.links i) hv (L.pantries i).adopted.laws.toSymmetric (L.pantries i).adopted.smooth
    (L.pantries i).present hx (hY.symm ▸ (L.cards i).corner)

open Spectral OS
variable {H : Hilbert}

def zeroE := {p : E4 | p timeAxis=0}
def aboveE := {p : E4 | 0 < p timeAxis}
lemma zeroE_m : MeasurableSet zeroE := isClosed_eq Mink.clock_cont continuous_const |>.measurableSet
lemma aboveE_m : MeasurableSet aboveE := (isOpen_lt continuous_const Mink.clock_cont).measurableSet

def boltz (s : ℝ≥0) (p : E4) : ℝ := Real.exp (- (s:ℝ) * p timeAxis)

lemma direct (T : OS.Semigroup H timeAxis) (x y : H) (s : ℝ≥0) :
    T.J 0 x y (Complex.I * ↑(s:ℝ))=inner ℂ x (T.E s y) := by
  unfold OS.Semigroup.J Semigroup.ray
  simp only [Complex.mul_re,Complex.I_re,zero_mul,Complex.I_im,Complex.ofReal_im,mul_zero,sub_zero,
    T.birth,ContinuousLinearMap.id_apply,T.unit.origin]
  simp [Complex.mul_im]

lemma boltzmann (T : OS.Semigroup H timeAxis) (x : H) (s : ℝ≥0) :
    inner ℂ x (T.E s x)= (↑(∫ p, boltz s p ∂T.ℚmeasure.diagonal x):ℂ) := by
  rw [← direct T x x s, T.heat 0 x (by simp [Paley.high]), ← integral_complex_ofReal]
  apply integral_congr_ae; filter_upwards with p
  rw [plane_zero, one_mul, show (((p timeAxis):ℂ)*(Complex.I*↑(s:ℝ)))*Complex.I= ↑(-(s:ℝ)*p timeAxis) from by
    push_cast; ring_nf; simp]
  exact (Complex.ofReal_exp _).symm

lemma boltz_int (μ : Measure E4) [IsFiniteMeasure μ] (h : ∀ᵐ p ∂μ, 0 ≤ p timeAxis) (s : ℝ≥0) :
    Integrable (boltz s) μ := by
  refine (integrable_const (1:ℝ)).mono (show Continuous (boltz s) from by unfold boltz; fun_prop).aestronglyMeasurable ?_
  filter_upwards [h] with i hi
  rw [Real.norm_eq_abs,boltz,abs_of_nonneg (Real.exp_pos _).le,norm_one, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr s.property) hi

lemma boltz_zero_atom (μ : Measure E4) [IsFiniteMeasure μ] (h : ∀ᵐ p ∂μ, 0 ≤ p timeAxis) :
    Tendsto (fun s => ∫ p, boltz s p ∂μ) atTop (𝓝 (μ.real zeroE)) := by
  classical
  rw [show μ.real zeroE=∫ p, zeroE.indicator (fun _ => (1:ℝ)) p ∂μ by rw [integral_indicator zeroE_m]; simp]
  apply tendsto_integral_filter_of_dominated_convergence (F:=boltz) (μ:=μ) (fun _ => (1:ℝ))
  · exact Eventually.of_forall fun s => (boltz_int μ h s).aestronglyMeasurable
  · refine Eventually.of_forall fun s => ?_
    filter_upwards [h] with i hi; rw [Real.norm_eq_abs,boltz,abs_of_nonneg (Real.exp_pos _).le,Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr s.property) hi
  · exact integrable_const 1
  filter_upwards [h] with p hp
  rcases hp.eq_or_lt with h|h
  · rw [indicator_of_mem (show p∈zeroE from h.symm)]
    unfold boltz; simp [← h]
  rw [indicator_of_notMem (show p∉zeroE from h.ne')]
  apply Real.tendsto_exp_atBot.comp
    ((tendsto_neg_atTop_atBot.comp (NNReal.tendsto_coe_atTop.mpr (tendsto_id (x := (atTop : Filter ℝ≥0))))).atBot_mul_const h)

theorem reflection_projection (T : OS.Semigroup H timeAxis) : T.orth=T.ℚmeasure.region zeroE := by
  have he (x : H) : inner ℂ x (T.orth x)=inner ℂ x (T.ℚmeasure.region zeroE x) := by
    rw [← T.ℚmeasure.at_pair zeroE_m]
    refine tendsto_nhds_unique_of_eventuallyEq (f:=fun s => inner ℂ x (T.E s x))
      (tendsto_const_nhds.inner (T.emerges x)) (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (boltz_zero_atom _ (T.bright x))) (Eventually.of_forall (boltzmann T x))
  have hh : T.orth.toLinearMap=(T.ℚmeasure.region zeroE).toLinearMap := (ext_inner_map ..).mp (fun v => by
    apply (starRingEnd ℂ).injective
    rw [inner_conj_symm, inner_conj_symm]; exact he v)
  ext1 x; exact LinearMap.congr_fun hh _

variable {X : Wightman S} {U : S.Rotation} {W : Surface S} {S₁ : Table C.book}
    {V : Chamber S₁ timeAxis} {J : X.operators.H →L[ℂ] V.H} {h : S.RealSpin}

/-- The actual real-time heat kernel H≥0 from the PVM; realized on the
whole boundary space. bHeat J V (diagonal identity below characterizes
this operator). -/
def bHeat (J : X.operators.H →L[ℂ] V.H) (s : ℝ≥0) : X.operators.H.Op :=
    J.adjoint.comp ((V.flow.E s).comp J)

lemma bHeat_pair (I : Attachment X V J) (H : FieldCore W U h X) (s : ℝ≥0) (x : X.operators.H) :
    inner ℂ x (bHeat J s x)=(↑(∫ p, boltz s p ∂X.momentum.diagonal x):ℂ) := by
  unfold bHeat; rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, I.measures H]
  exact boltzmann _ _ _

lemma bHeat_limit (I : Attachment X V J) (H : FieldCore W U h X) (x : X.operators.H) :
    Tendsto (fun s => bHeat J s x) atTop (𝓝 (X.momentum.region zeroE x)) := by
  have he := V.flow.emerges (J x)
  rw [reflection_projection,← I.projections H zeroE zeroE_m] at he
  have hJ (y : X.operators.H) : J.adjoint (J y)=y :=
    DFunLike.congr_fun (J.norm_map_iff_adjoint_comp_self.mp I.acts.scale) y
  have hp := (J.adjoint.continuous.continuousAt (x:=J (X.momentum.region zeroE x))).tendsto.comp he
  rw [hJ] at hp; exact hp

lemma bHeat_ground (I : Attachment X V J) (H : FieldCore W U h X) (x : X.operators.H) :
    (∀ s : ℝ≥0, bHeat J s x=x) ↔ X.momentum.region zeroE x=x := by
  constructor
  · intro hp
    exact tendsto_nhds_unique_of_eventuallyEq (bHeat_limit I H x) tendsto_const_nhds (Eventually.of_forall hp)
  intro hp s
  have hh : V.flow.orth (J x)=J x := by rw [reflection_projection, ← I.projections H _ zeroE_m,hp]
  have he : J x∈ V.flow.ground := V.flow.ground.starProjection_eq_self_iff.mp hh

  unfold bHeat
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,(V.flow.fixed _).1 he]
  exact DFunLike.congr_fun (J.norm_map_iff_adjoint_comp_self.mp I.acts.scale) x

lemma cave (H : FieldCore W U h X) (x : X.operators.H) : ∀ᵐ p ∂X.momentum.diagonal x, p ∈ Mink.cone := by
  suffices hh : X.momentum.diagonal x Mink.coneᶜ=0 from hh
  rw [X.momentum.null_pair Mink.closed_cone.measurableSet.compl, H.forward]; rfl

lemma residual (μ : Measure E4) [IsFiniteMeasure μ] (h : ∀ᵐ p ∂μ, 0 ≤ p timeAxis) (s : ℝ≥0) :
    (∫ p, boltz s p ∂μ)=μ.real zeroE + ∫ p in aboveE, boltz s p ∂μ := by
  classical
  have ht := boltz_int μ h s
  rw [← integral_add_compl zeroE_m ht]
  congr 1
  · calc
      _ = ∫ _ in zeroE, (1:ℝ) ∂μ := by
        apply setIntegral_congr_fun zeroE_m; intro p hp
        unfold boltz; rw [show p timeAxis=0 from hp]; simp
      _ = μ.real zeroE := by simp
  apply setIntegral_congr_set
  filter_upwards [h] with p hp
  apply propext
  change p timeAxis ≠ 0 ↔ 0 < p timeAxis
  exact ⟨fun h => hp.lt_of_ne (Ne.symm h),fun h => h.ne'⟩

lemma residual_pair (I : Attachment X V J) (H : FieldCore W U h X) (s : ℝ≥0)
    (x : X.operators.H) : inner ℂ x ((bHeat J s-X.momentum.region zeroE) x) =
      (↑(∫ p in aboveE, boltz s p ∂X.momentum.diagonal x):ℂ) := by
  rw [_root_.sub_apply, inner_sub_right, bHeat_pair I H,
    ← X.momentum.at_pair zeroE_m, residual _ ?h,Complex.ofReal_add,add_sub_cancel_left]
  exact (cave H x).mono fun p hp => ((Mink.cone_self _).mp hp).1
end YM.EveryPhase
