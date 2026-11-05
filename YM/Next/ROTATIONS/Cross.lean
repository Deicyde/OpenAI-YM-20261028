import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Axis.Matrix

/-!
# Cauchy estimates with two different weight tests

A non-sharp constant in the quadratic estimate suffices. Derived from actual PVM on
the SAME lowering for both clusters; no dominating-matrix hypothesis. No assertion of
global finiteness for undamped measures. Supports on the closed energy half-line.
-/
noncomputable section
namespace YM.Outer
open MeasureTheory Measure Filter Set Function Complex Boundary Probe Row OS Word
open scoped Topology InnerProductSpace ContDiff BigOperators NNReal ENNReal

private lemma density_aux {X : Type*} [MeasurableSpace X] (μ : Measure X) (g h : X→ℝ)
    (hg : Integrable g μ) (hh : Integrable h μ) (hc : ∀ s : Set X, MeasurableSet s → μ s < ⊤ → |∫ x in s,g x ∂μ| ≤ ∫ x in s,h x ∂μ) :
    ∀ᵐ x ∂μ, |g x| ≤ h x := by
  have he := ae_le_of_forall_setIntegral_le hg hh fun s hs hS => (le_abs_self _).trans (hc s hs hS)
  have hj := ae_le_of_forall_setIntegral_le hg.neg hh fun s hs hS => calc
    _ = -(∫ x in s,g x ∂μ) := integral_neg g
    _ ≤ |(∫ x in s,g x ∂μ)| := neg_le_abs _
    _ ≤ _ := hc s hs hS
  filter_upwards [he,hj] with x hx hp
  change -g x ≤ h x at hp
  exact abs_le.mpr ⟨by linarith,hx⟩

/-- Non-sharp (factor two). -/
private lemma density_bound {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X→ℂ) (h : X→ℝ)
    (hf : Integrable f μ) (hh : Integrable h μ) (hc : ∀ s : Set X, MeasurableSet s → μ s < ⊤ → ‖∫ x in s,f x ∂μ‖ ≤ ∫ x in s,h x ∂μ) :
    ∀ᵐ x ∂μ, ‖f x‖≤2*h x := by
  have he : ∀ᵐ x ∂μ, |(f x).re| ≤ h x := by
    refine density_aux μ _ _ hf.re hh fun s hs hS => ?_
    change |∫ x in s,RCLike.re (f x) ∂μ| ≤ _
    rw [integral_re hf.integrableOn]; exact (abs_re_le_norm _).trans (hc s hs hS)
  have hj : ∀ᵐ x ∂μ, |(f x).im| ≤ h x := by
    refine density_aux μ _ _ hf.im hh fun s hs hS => ?_
    change |∫ x in s,RCLike.im (f x) ∂μ| ≤ _
    rw [integral_im hf.integrableOn]; exact (abs_im_le_norm _).trans (hc s hs hS)
  filter_upwards [he,hj] with x hx hp
  calc _ ≤ _ := Complex.norm_le_abs_re_add_abs_im (f x)
       _ ≤ _ := (add_le_add hx hp).trans_eq (by ring)

private lemma weights {z : ℂ} {α β m a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hm : 0 ≤ m)
    (he : m^2≤a*b) (hu : 0<u) (hp : ∀ t : ℝ, 0<t → ‖z‖≤t*α+β/t) : ‖z‖*m ≤ u*(α*a)+(β*b)/u := by
  rcases eq_or_lt_of_le hm with rfl|hh; · simp; positivity
  have hz : 0 < a*b := lt_of_lt_of_le (by positivity) he
  have hy : 0<a := by
    apply lt_of_le_of_ne ha; rintro H
    rw [← H,zero_mul] at hz; exact (lt_irrefl _ hz)
  let t := u*a/m
  have ht : 0<t := by unfold t; positivity
  calc
    _ ≤ (t*α+β/t)*m := mul_le_mul_of_nonneg_right (hp t ht) hm
    _ = u*(α*a) + β/u*(m^2/a) := by dsimp only [t]; field_simp
    _ ≤ _ := by
      rw [show β*b/u=β/u*b by ring]
      have hi : m^2/a ≤ b := (div_le_iff₀ hy).mpr (by rwa [mul_comm])
      gcongr

section
open Spectral
variable {D : Hilbert} {X : Type*} [MeasurableSpace X] (P : PVM D X) (v w : D)
private def pm (f : X → ℂ) := (4:ℂ)⁻¹ * ∑ i : Fin 4,
    star (phase i) * (∫ p,f p ∂P.diagonal (v+phase i • w))

/-- PVM weighted Young inequality. -/
private lemma pm_bounds (f : X → ℂ) (a b : X → ℝ)
    (h : ∀ i : Fin 4, Integrable f (P.diagonal (v+phase i • w)))
    (ha : Integrable a (P.diagonal v)) (hb : Integrable b (P.diagonal w))
    (hc : ∀ᵐ x ∂P.diagonal v+P.diagonal w, 0 ≤ a x ∧ 0 ≤ b x ∧ ‖f x‖^2 ≤ a x*b x)
    (u : ℝ) (hu : 0<u) :
    ‖pm P v w f‖ ≤ u*(∫ x,a x ∂P.diagonal v)+(∫ x,b x ∂P.diagonal w)/u := by
  let μ := P.diagonal v+P.diagonal w
  let r (t : D) := fun x => ((P.diagonal t).rnDeriv μ x).toReal
  let p (i : Fin 4) := v+phase i • w
  let F (x : X) := (4:ℂ)⁻¹ * ∑ i : Fin 4, star (phase i)*(r (p i) x:ℂ)
  have ha' : P.diagonal v ≪ μ := (Measure.AbsolutelyContinuous.refl _).add_right _
  have hb' : P.diagonal w ≪ μ := by unfold μ; rw [add_comm]; exact (Measure.AbsolutelyContinuous.refl _).add_right _
  have hi (i) : P.diagonal (p i) ≪ μ := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hS => (P.null_pair hs _).mpr ?_
    rw [show p i= _ from rfl,map_add,map_smul, (P.null_pair hs v).mp (ha' hS),(P.null_pair hs w).mp (hb' hS)]; simp
  have hInt (t : D) (ht : P.diagonal t ≪ μ) : Integrable (r t) μ := by
    simpa [r] using (integrable_rnDeriv_smul_iff (ν:=μ) ht).2 (integrable_const (1:ℝ))
  have hI (i) : Integrable (fun x => star (phase i)*(r (p i) x:ℂ)) μ := ((hInt (p i) (hi i)).ofReal).const_mul _
  have hF : Integrable F μ := (integrable_finsetSum Finset.univ fun i _ => hI i).const_mul _
  have hEq s (hs : MeasurableSet s) : (∫ x in s,F x ∂μ) = inner ℂ v (P.region s w) := by
    unfold F
    rw [integral_const_mul,integral_finsetSum _ (fun i _ => (hI i).integrableOn)]
    simp_rw [integral_const_mul, integral_complex_ofReal]
    unfold r; simp_rw [Measure.setIntegral_toReal_rnDeriv (hi _) s, P.at_pair hs]
    exact identity (H:=D) (P.region s) v w
  have hz (t : ℝ) (ht : 0<t) : ∀ᵐ x ∂μ, ‖F x‖ ≤ t*r v x+r w x/t := by
    let g x := (t*r v x + r w x/t)/2
    have hj : ∀ᵐ x ∂μ, ‖F x‖ ≤ 2*g x := by
      refine density_bound μ _ g hF (((hInt v ha').const_mul t |>.add ((hInt w hb').div_const t)).div_const _)
        (fun s hs hS => ?_)
      rw [hEq s hs,show inner ℂ v (P.region s w)=inner ℂ (P.region s v) (P.region s w) by
        conv_rhs => lhs; arg 1;rw [← P.real hs]
        rw [ContinuousLinearMap.adjoint_inner_left,P.idempotent hs]]
      unfold g
      rw [integral_div,integral_add ((hInt v ha').const_mul t).integrableOn ((hInt w hb').div_const t).integrableOn,
        integral_const_mul,integral_div]
      unfold r
      rw [Measure.setIntegral_toReal_rnDeriv ha' s,Measure.setIntegral_toReal_rnDeriv hb' s,P.same hs,P.same hs]
      refine (norm_inner_le_norm ..).trans ?_
      rw [le_div_iff₀ (by norm_num)]
      apply sub_le_iff_le_add'.mp ?_
      rw [le_div_iff₀ ht]
      nlinarith [sq_nonneg (t*‖P.region s v‖-‖P.region s w‖)]
    filter_upwards [hj] with x hx
    exact hx.trans_eq (by dsimp only [g]; ring)
  have hall : ∀ᵐ x ∂μ, ∀ (t : ℚ), 0 < t → ‖F x‖ ≤ (t:ℝ)*r v x+r w x/t := by
    refine ae_all_iff.mpr fun t => ?_
    by_cases ht : 0 < t
    · filter_upwards [hz (t:ℝ) (by exact_mod_cast ht)] with x hx _; exact hx
    · exact .of_forall fun _ h => (ht h).elim
  have hA : Integrable (fun x => r v x*a x) μ := (integrable_rnDeriv_smul_iff ha').2 ha
  have hB : Integrable (fun x => r w x*b x) μ := (integrable_rnDeriv_smul_iff hb').2 hb
  have hh : (∫ x,F x*f x ∂μ) = pm P v w f := by
    have hw (i) : Integrable (fun x => ↑(r (p i) x)*f x) μ := (integrable_rnDeriv_smul_iff (hi i)).2 (h i)
    unfold F pm; simp_rw [mul_assoc,Finset.sum_mul,mul_assoc]
    rw [integral_const_mul,integral_finsetSum _ (fun i _ => (hw i).const_mul _)]
    congr 1; apply Finset.sum_congr rfl; intro i _; rw [integral_const_mul]; congr 1
    exact integral_rnDeriv_smul (f:=f) (hi i)
  rw [← hh]
  let m x := u*(r v x*a x)+(r w x*b x)/u
  calc
    _ ≤ ∫ x,m x ∂μ := by
      refine norm_integral_le_of_norm_le ((hA.const_mul u).add (hB.div_const u)) ?_
      filter_upwards [hc,hall] with x hx hi
      refine (norm_mul ..).trans_le (weights hx.1 hx.2.1 ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        (norm_nonneg _) hx.2.2 hu fun t h₀ => ?_)
      by_contra! hp
      have H : ContinuousAt (fun z : ℝ => z*r v x+r w x/z) t := by fun_prop (disch:=positivity)
      have he : {z | (0:ℝ)<z ∧ z*r v x+r w x/z < ‖F x‖}∈𝓝 t :=
        Eventually.and (lt_mem_nhds h₀) (H.eventually (gt_mem_nhds hp))
      obtain ⟨s,hs,⟨q,rfl⟩⟩ := mem_closure_iff_nhds.mp (Rat.denseRange_cast t) _ he
      have hk : (0:ℝ)<q ∧ (q:ℝ)*r v x+r w x/q < ‖F x‖ := hs
      exact hk.2.not_ge (hi q (by exact_mod_cast hk.1))
    _ = _ := by
      unfold m
      rw [integral_add (hA.const_mul u) (hB.div_const u),integral_const_mul,integral_div]
      unfold r
      simp_rw [MeasureTheory.integral_toReal_rnDeriv_mul ha',MeasureTheory.integral_toReal_rnDeriv_mul hb']
end

variable {G : Gauge} {L : Register G} {S : Table L} {i : Axis} (V : Chamber S i)

/-- Cauchy-Schwarz form sufficient even with atomic low energy.
Nonnegative/price inputs needed ONLY on `p i ≥ 0`. `t` is a global trade rate. -/
lemma cross_le (B A : Weight L) (f : E4 → ℂ) (hf : fits V B A f) (a b : E4 → ℝ)
    (ha : Integrable a (ν V B)) (hb : Integrable b (ν V A))
    (hh : ∀ p : E4, 0 ≤ p i → 0 ≤ a p ∧ 0 ≤ b p ∧ ‖f p‖^2 ≤ a p*b p)
    (t : ℝ) (ht : 0<t) :
    ‖cross V B A f‖ ≤ t*(∫ p,a p ∂ν V B)+(∫ p,b p ∂ν V A)/t := by
  obtain ⟨u,hU,hV⟩ := ((descends i B).and (descends i A)).exists
  let P := V.flow.ℚmeasure
  let D := Semigroup.descent i (-((u+u:ℝ≥0):ℝ))
  let v := root V B u
  let w := root V A u
  have hi (X : Weight L) (h : Lowered i X u) :
      ν V X = (P.diagonal (root V X u)).withDensity fun p => ↑(D p) := issued V _ _ h
  have hv : ν V B = (P.diagonal v).withDensity fun p => ↑(D p) := hi B hU
  have hw : ν V A = (P.diagonal w).withDensity fun p => ↑(D p) := hi A hV
  have hz (j) : ν V (combo B A j)=(P.diagonal (v+ Row.phase j • w)).withDensity fun p => ↑(D p) := by
    rw [hi _ (meets_air B A u hU hV j),route]
  unfold fits at hf
  simp_rw [hz] at hf
  let f' (p) := D p • f p
  let a' (p) := (D p:ℝ)*a p
  let b' (p) := (D p:ℝ)*b p
  have hd : Measurable D := Semigroup.measurable ..
  have h' (j) : Integrable f' (P.diagonal (v+Row.phase j • w)) := (integrable_withDensity_iff_integrable_smul hd).1 (hf j)
  have ha' : Integrable a' (P.diagonal v) := (integrable_withDensity_iff_integrable_smul hd).1 (hv ▸ ha)
  have hb' : Integrable b' (P.diagonal w) := (integrable_withDensity_iff_integrable_smul hd).1 (hw ▸ hb)
  have he : cross V B A f=pm P v w f' := by
    unfold cross pm
    simp_rw [hz, integral_withDensity_eq_integral_smul hd]; rfl
  have hx : ∀ᵐ p ∂P.diagonal v+P.diagonal w,0 ≤ a' p ∧ 0 ≤ b' p ∧ ‖f' p‖^2 ≤ a' p*b' p := by
    have hj : ∀ᵐ p : E4 ∂P.diagonal v+P.diagonal w, 0≤p i := ae_add_measure_iff.mpr ⟨V.flow.bright v,V.flow.bright w⟩
    filter_upwards [hj] with p hp
    obtain ⟨hx,hy,h⟩ := hh p hp
    refine ⟨mul_nonneg (D p).property hx,mul_nonneg (D p).property hy,?_⟩
    change ‖(D p:ℝ) • f p‖^2≤ (D p:ℝ)*a p*((D p:ℝ)*b p)
    rw [norm_smul, Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ ↑(D p) from (D p).property), mul_pow]
    exact (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq (by ring)
  rw [he,hv,hw, integral_withDensity_eq_integral_smul hd,integral_withDensity_eq_integral_smul hd]
  exact pm_bounds P v w f' _ _ h' ha' hb' hx t ht
end YM.Outer
