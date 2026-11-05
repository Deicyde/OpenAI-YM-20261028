import YM.RG08.Jetty.Praise
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! # Pull positive representation to addresses

Choose OnePoint compactification to work for all Test jets transformed by the
supplied positive exponential packet width. There's NO point mass left in this
formula from moving at Infinity. No proper test compact support needed, so use
for the polynomial evaluation normalization as is.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Jetty
open Function Set Topology MeasureTheory Filter
open scoped Topology BigOperators Classical
variable {I X:Type*}[Fintype I][TopologicalSpace X][T2Space X][LocallyCompactSpace X][MeasurableSpace X][BorelSpace X]
local instance : MeasurableSpace (OnePoint X):= borel _
local instance : BorelSpace (OnePoint X):= ⟨rfl⟩
abbrev Sky (X:Type*)[TopologicalSpace X]:=Air (OnePoint X)
abbrev Cloud (X I:Type*)[TopologicalSpace X]:=I→Sky X
abbrev push (X:Type*):X→OnePoint X:= (↑)
omit [T2Space X][LocallyCompactSpace X] in
lemma lands (μ:Measure (OnePoint X))[IsFiniteMeasure μ]:
 ∃ ν:Measure X, IsFiniteMeasure ν∧ν.real univ≤μ.real univ ∧
   ∀ f:Sky X, Integrable (f ∘ push X) ν ∧ (f OnePoint.infty=0 → (∫ x,f x ∂μ)=∫ x,f (push X x) ∂ν):=by
 have he:MeasurableEmbedding (push X):= OnePoint.isOpenEmbedding_coe.measurableEmbedding
 let ν:=Measure.comap (push X) μ
 have hv:IsFiniteMeasure ν:=by unfold ν; infer_instance
 refine ⟨ν,hv,?_,fun f=>?_⟩
 · change (ν Set.univ).toReal ≤ _
   rw [show ν Set.univ=μ (push X '' Set.univ) from he.comap_apply ..]
   exact measureReal_mono (subset_univ _)
 have hm:Measure.map (push X) ν=μ.restrict (Set.range (push X)):=he.map_comap μ
 refine ⟨he.integrable_map_iff.mp ?_,fun h=>?_⟩
 · rw [hm]; exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Set.range (push X)) (f:=f) (by
       intro x hx; induction x using OnePoint.rec
       · exact h
       · exact absurd (mem_range_self _) hx),← hm, he.integral_map]

def raised (f : C(X,ℝ))(h:Tendsto f (coclosedCompact X) (𝓝 0)):Sky X:= OnePoint.continuousMapMk f 0 h
omit [T2Space X][LocallyCompactSpace X][MeasurableSpace X][BorelSpace X] in
lemma raised_at (f:C(X,ℝ))(h)(x:X): raised f h (push X x)=f x:=rfl
omit [T2Space X][LocallyCompactSpace X][MeasurableSpace X][BorelSpace X] in
lemma raised_star (f:C(X,ℝ))(h): raised f h OnePoint.infty=0:=rfl
omit [T2Space X][LocallyCompactSpace X][MeasurableSpace X][BorelSpace X] in
lemma cloud_cap (f:Cloud X I){K:ℝ}(hK:0≤K)(h:∀ i (x:X), |f i (push X x)| ≤ K)(hv:∀ i, f i OnePoint.infty=0) : ‖f‖≤K:=by
 refine (pi_norm_le_iff_of_nonneg hK).mpr (fun i=> (ContinuousMap.norm_le _ hK).mpr (fun x=>?_))
 induction x using OnePoint.rec
 · rw [hv,norm_zero]; exact hK
 · exact (Real.norm_eq_abs _).trans_le (h ..)
omit [T2Space X][LocallyCompactSpace X][MeasurableSpace X][BorelSpace X] in
lemma cloud_at (f:Cloud X I)(i:I)(x:X): |f i (push X x)| ≤ ‖f‖:=by
 exact (Real.norm_eq_abs _).ge.trans ((ContinuousMap.norm_coe_le_norm ..).trans ((pi_norm_le_iff_of_nonneg (norm_nonneg f)).mp (le_refl _) i))

variable {T:Type*}[AddCommGroup T][Module ℝ T]
private def center (F:Cloud X I →L[ℝ] ℝ)(i:I): Sky X→ₗ[ℝ] ℝ:= F.toLinearMap.comp (LinearMap.single ℝ (fun _=>Sky X) i)
omit [T2Space X][LocallyCompactSpace X][MeasurableSpace X][BorelSpace X] in
private lemma changes (F:Cloud X I →L[ℝ] ℝ)(i:I)(f:Sky X):|center F i f|≤‖F‖*‖f‖:=by
 rw [←Real.norm_eq_abs]; apply (F.le_opNorm (LinearMap.single ℝ (fun _=>Sky X) i f)).trans
 apply mul_le_mul_of_nonneg_left _ (norm_nonneg F)
 change ‖Pi.single i (M:=fun _=>Sky X) f‖≤ _
 refine (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr (fun j=>?_)
 by_cases he:j=i
 · subst j; simp
 · simp [Pi.single_eq_of_ne he]

omit [T2Space X][LocallyCompactSpace X][MeasurableSpace X][BorelSpace X] in
private lemma centers (F:Cloud X I →L[ℝ] ℝ)(f:Cloud X I): F f = ∑ i,center F i (f i):=by
 refine Eq.trans ?_ (map_sum F (fun i=> LinearMap.single ℝ (fun _=>Sky X) i (f i)) _)
 apply congrArg (fun y:Cloud X I=> F y); ext j x; rw [Finset.sum_apply]; simp [LinearMap.single_apply, Pi.single]
 rw [Finset.sum_eq_single j (fun k _ hk=>by simp [update_of_ne (Ne.symm hk)]) (by simp)]; simp

/-- Present functional bounds on any linear test space, through a normalized family of jets vanishing at infinity. -/
theorem presentation (p:T→ₗ[ℝ] Cloud X I)(q:T→ₗ[ℝ] ℝ)(hp:Injective p)(h₀:∀ f i,p f i OnePoint.infty=0)
 {K:ℝ}(hK:0≤K)(hx:∀ f,|q f|≤K*‖p f‖):
 ∃ μ ν:I→Measure X, (∀ i, IsFiniteMeasure (μ i)∧IsFiniteMeasure (ν i)∧(μ i).real univ+(ν i).real univ≤K)∧
   ∀ f, (∀ i,Integrable (p f i ∘ push X) (μ i)∧ Integrable (p f i ∘ push X) (ν i))∧
     q f=∑ i,((∫ x,p f i (push X x) ∂μ i)-(∫ x,p f i (push X x) ∂ν i)):=by
 obtain ⟨F,hF,h⟩:= lift p hp q hK (fun f=>(Real.norm_eq_abs _).trans_le (hx f))
 have hi (i:I):∃ μ ν:Measure X,(IsFiniteMeasure μ∧IsFiniteMeasure ν∧μ.real univ+ν.real univ ≤K)∧
      ∀ f, Integrable (p f i ∘ push X) μ ∧ Integrable (p f i ∘ push X) ν ∧ center F i (p f i)=(∫ x,p f i (push X x) ∂μ)-(∫ x,p f i (push X x) ∂ν):=by
   obtain ⟨A,B,hA,hB,hy,hg⟩:=render (center F i) (norm_nonneg F) (changes F i)
   obtain ⟨μ,hμ,hv,h₁⟩:= lands A
   obtain ⟨ν,hν,hv',h₂⟩:= lands B
   refine ⟨μ,ν,⟨hμ,hν,(add_le_add hv hv').trans (hy.trans_le h)⟩,fun f=>⟨(h₁ _).1,(h₂ _).1,?_⟩⟩
   rw [hg,(h₁ _).2 (h₀ _ _),(h₂ _).2 (h₀ _ _)]
 choose μ ν hμ he using hi
 refine ⟨μ,ν,hμ,fun f=>⟨fun i=>⟨(he i f).1,(he i f).2.1⟩,?_⟩⟩
 rw [←hF,centers];exact Finset.sum_congr rfl fun i _=>(he i f).2.2
end YM.RG08.Jetty
