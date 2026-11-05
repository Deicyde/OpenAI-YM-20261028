import YM.RG08.Canon.Revolve
/-!
# Recentring through linear transports
Pull integration back with a determinant. Supplies simultaneous asymptotic
comparisons at fixed period without any alleged uniform termwise saddle
bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter Set Metric MeasureTheory YM.PertExtension.Series.Tested
open YM.PertExtension.Series.Radial YM.PertExtension.Chart RG08.Reflect
open scoped BigOperators Topology Real ContDiff Classical
variable (G : Gauge) (U : Type) [Fintype U]
variable {D : Precision.ChartRatio G}
local notation "E" => U → G.Color
local notation "Z" => (U → G.Color) × ℝ
local notation "T" => tangent G U
local notation "Ω" => physical G U

abbrev swing {W : Type*} [NormedAddCommGroup W][NormedSpace ℝ W](L : W≃L[ℝ]W) : ℝ := LinearMap.det L.toContinuousLinearMap.toLinearMap
lemma takeL (L : (E) ≃L[ℝ] (E)) (g : (E) →ℝ) : (∫ x,g x ∂T)=∫ x, |swing L| * g (L x)∂T := by
  let F:=L.toHomeomorph.toMeasurableEquiv
  rw [integral_const_mul, ← show (∫ x,g x ∂Measure.map L T)=(∫ y,g (L y) ∂T) from integral_map_equiv (μ:=T) F g]
  have hp : swing L≠0 := (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  rw [show Measure.map L T=(ENNReal.ofReal |(swing L)⁻¹|) • (T) from Measure.map_linearMap_addHaar_eq_smul_addHaar (T) hp, integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul,abs_inv]; field_simp

-- topological window; permit a germ identity only around the centered zero. Histories may choose different additive paths and determinant gauges.
abbrev track (L : ℝ → (E)≃L[ℝ](E)) (b : ℝ → E) (z : Z) : E := L z.2 z.1+b z.2
variable (L : ℝ → (U → G.Color)≃L[ℝ](U → G.Color)) (b : ℝ → (U→G.Color))
omit [Fintype U] in
lemma track_cont (hb : b 0=0) (hx : ContinuousAt (fun p:Z => L p.2 p.1) 0) (h : ContinuousAt b 0) : Tendsto (track G U L b) (𝓝 0) (𝓝 0) := by
  have hh : track G U L b (0:Z)=0 := by simp [track,hb]
  have ht : ContinuousAt (track G U L b) 0 := hx.add (h.comp (f:=Prod.snd) continuousAt_snd)
  have hp := ht.tendsto; rw [hh] at hp; exact hp
-- auxiliary queues use open identity chambers
lemma track_piece (hb:b 0=0)(h : ContinuousAt b 0)(hx : ContinuousAt (fun p:Z => (L p.2).symm p.1) 0) (s : Set (Z)) (hs : s∈𝓝 0) :
    ∃ d>0,∀ᶠ t : ℝ in 𝓝[>]0, ∀ x:E, track G U L b (t • plates G U x)∈ball 0 d → t • plates G U x ∈ s := by
  let f (p : Z) : Z := ((L p.2).symm (p.1-b p.2),p.2)
  have hm : f (0:Z)=0:= by simp [f,hb]
  have ht : ((𝓝 (0:Z)).Eventually (fun z=>f z∈s)) := by
    let g (p:Z):Z:=(p.1-b p.2,p.2); have hg : g 0=0:= by simp [g,hb]
    have hT : ContinuousAt f 0 := ((show ContinuousAt (fun p:Z=> (L p.2).symm p.1) (g 0) by rwa [hg]).comp (f:=g) ((continuousAt_fst.sub (h.comp (f:=Prod.snd) continuousAt_snd)).prodMk continuousAt_snd)).prodMk continuousAt_snd
    have hu := hT.tendsto; rw [hm] at hu; exact hu hs
  obtain ⟨d,hd,hh⟩:= Metric.mem_nhds_iff.mp ht
  refine ⟨d,hd,?_⟩
  filter_upwards [eventually_pos,eventually_top hd] with t H hv
  intro x he; let V:=track G U L b (t•plates G U x)
  rw [show t • plates G U x=f (V,t) from by simp [plates,V,track,f]]; refine hh (mem_ball_zero_iff.mpr ?_)
  rw [Prod.norm_def,max_lt_iff]; exact ⟨mem_ball_zero_iff.mp he,by simpa [abs_of_pos H] using hv⟩

lemma track_little (hb:b 0=0)(h : ContinuousAt b 0)(hx : ContinuousAt (fun p:Z => L p.2 p.1) 0) (d : ℝ) (hd : 0<d) (s : Set (U→G.El)) (hs : s∈𝓝 1) :
    ∃ ε>0, ∀ p:Z,p∈ball 0 ε→ track G U L b p ∈ball 0 d ∧ expLinks G U (track G U L b p)∈s := by
  have hu : Tendsto (expLinks G U) (𝓝 (0:E)) (𝓝 1) := by
    rw [← show expLinks G U 0=1 from funext fun _=> G.mat_lieExp_zero]; exact ((continuous_pi (show ∀ i:U,Continuous (fun x:E=>expLinks G U x i) from fun i=> G.lieExp_cont.comp (continuous_apply i))).continuousAt)
  have hp := track_cont G U L b hb hx h
  have H₁ : ∀ᶠ p in 𝓝 0,track G U L b p∈ball 0 d := hp (ball_mem_nhds _ hd)
  exact Metric.mem_nhds_iff.mp (H₁.and ((hu.comp hp) hs))

-- choose set for plates on the common slice. localization requires full disc z (incl t*z.2 not t) -- may include extra sets off the plate.
def stadium (r δ : ℝ)(A : ℝ→Set (U→G.El))(t : ℝ) : Set Z := disc t δ ∩ ({z : Z| z.2≠1} ∪
   {z : Z| (t • L t z.1 + b t) ∈ Metric.ball 0 r ∧ expLinks G U (t • L t z.1 + b t) ∈ A t})
lemma stadium_meas {A : ℝ→ Set (U → G.El)} {t : ℝ} (he : MeasurableSet (A t)) (r δ) : MeasurableSet (stadium G U L b r δ A t) := by
  refine (disc_meas ..).inter (((isOpen_ne_fun continuous_snd continuous_const).measurableSet).union ((isOpen_ball.measurableSet.preimage (by fun_prop)).inter (he.preimage (expLinks_meas.comp (by fun_prop)))))
set_option maxHeartbeats 350000 in
lemma stadium_take {A : ℝ→Set (U→G.El)} {r δ : ℝ} {s : Set (U→G.El)} (hx:s∈𝓝 1)(hδ:0<δ)(hr:0<r)(h : ContinuousAt (fun p:Z=> L p.2 p.1) 0) (hv : b 0=0)(ht : ContinuousAt b 0) :
    ∃ v>0,∀ (t:ℝ),s ⊆ A t → disc t v ⊆ stadium G U L b r δ A t := by
  obtain ⟨d,hd,H⟩:=track_little G U L b hv ht h r hr s hx
  refine ⟨min d δ,lt_min hd hδ,fun t he x hy=>?_⟩
  unfold PertExtension.Series.Radial.disc at hy; rw [Set.mem_preimage] at hy
  have hg : t • x∈Metric.ball 0 δ:= ball_subset_ball (min_le_right ..) hy
  change _ ∧ ((x.2≠1) ∨ ((t • L t x.1+b t)∈ball 0 r ∧ _))
  refine ⟨hg,?_⟩; apply or_iff_not_imp_left.mpr; intro hh
  have hx : x.2=1 := Classical.byContradiction hh
  have he' := H (t•x) ((ball_subset_ball (min_le_left ..)) hy); have hh : track G U L b (t•x)=t • L t x.1 + b t := by simp only [track,Prod.smul_fst,Prod.smul_snd,hx,smul_eq_mul,mul_one,map_smul]
  rw [hh] at he'; exact ⟨he'.1,he he'.2⟩
end YM.RG08.Canon
