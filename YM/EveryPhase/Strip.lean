import YM.EveryPhase.Killing
import YM.EveryPhase.Vitali

/-! # Integrated jump: strip derivatives -/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Metric Boundary Next.BOUNDARY Mink Complex Probe
open Work.C20
open scoped Topology BigOperators LineDeriv ContDiff

lemma compact_analytic_int {F G : ℂ → Space3 → ℂ} {A : Set ℂ} {p : ℂ} (hA : IsOpen A) (hp : p∈A)
    (hf : ContinuousOn F.uncurry (A ×ˢ univ)) (hg : ∀ x, ∀ z∈A, HasDerivAt (fun w => F w x) (G z x) z)
    {S : Set Space3} (hs : IsCompact S) (hz : ∀ z∈A, ∀ x, x∉S → F z x=0) :
    Integrable (G p) ∧ HasDerivAt (fun z => ∫ x, F z x) (∫ x, G p x) p := by
  have hm (z) (hv : z∈A) : Integrable (F z) := by
    have h : Continuous (F z) := continuousOn_univ.mp (hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => (show (z,x)∈A ×ˢ (univ:Set Space3) from ⟨hv,mem_univ _⟩)))
    exact h.integrable_of_hasCompactSupport (HasCompactSupport.intro hs (hz z hv))
  have hw : AEStronglyMeasurable (G p) := by
    classical
    let Y (s : ℂ) := if s∈A then fun x : Space3 => slope (fun z => F z x) p s else 0
    apply aestronglyMeasurable_of_tendsto_ae (f := Y) (𝓝[≠] p)
    · intro z
      unfold Y; split
      · next h =>
          simp only [slope_def_module]
          exact ((hm z h).aestronglyMeasurable.sub (hm p hp).aestronglyMeasurable).const_smul ((z-p)⁻¹)
      exact aestronglyMeasurable_zero
    filter_upwards with x
    refine (hg x p hp).tendsto_slope.congr' ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hA.mem_nhds hp)] with i hi; simp [Y,hi]
  obtain ⟨d,hd,hB⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds hp)
  let r := d/3
  have hr : 0<r := by unfold r; positivity
  have hb : closedBall p (r+r) ⊆ A :=
    (closedBall_subset_ball (by unfold r; linarith)).trans hB
  classical
  obtain ⟨M,hM⟩ := ((isCompact_closedBall p (r+r)).prod hs).bddAbove_image (hf.norm.mono (Set.prod_mono hb (subset_univ _)))
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := G) (bound := S.indicator fun _ => M/r)
    (ball_mem_nhds p hr) ((show ∀ᶠ i in 𝓝 p, i∈A from hA.mem_nhds hp).mono (fun i hi => (hm i hi).aestronglyMeasurable))
    (hm _ hp) hw ?_ ((integrable_indicator_iff hs.measurableSet).mpr (integrableOn_const hs.measure_ne_top)) ?_
  · filter_upwards with x z hv
    have hh : closedBall z r ⊆ closedBall p (r+r) := fun k hk =>
      (dist_triangle k z p).trans (add_le_add hk (ball_subset_closedBall hv))
    have hq := hb (hh (mem_closedBall_self hr.le))
    by_cases hx : x∈S
    · rw [Set.indicator_of_mem hx,← (hg x z hq).deriv,
        ← Complex.cderiv_eq_deriv hA (fun k hk => (hg x k hk).differentiableAt.differentiableWithinAt) hr (hh.trans hb)]
      exact Complex.norm_cderiv_le hr (fun w hy => hM ⟨(w,x),⟨hh (sphere_subset_closedBall hy),hx⟩,rfl⟩)
    have he : G z x=0 := ((hg x z hq).congr_of_eventuallyEq (show (fun _ => (0:ℂ)) =ᶠ[𝓝 z] (fun u => F u x) from
      (show ∀ᶠ i in 𝓝 z, i∈A from hA.mem_nhds hq).mono fun y hy => (hz y hy x hx).symm)).unique (hasDerivAt_const z _)
    simp [hx,he]
  filter_upwards with x z hv
  exact hg x z (hb (closedBall_subset_closedBall (show r≤r+r by linarith) (ball_subset_closedBall hv)))

variable {G : Gauge} {L : Register G} {S U : Table L} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D} {n : ℕ}
  {P : DiffPlan S} {H : S.RealSpin} {F : Waves S}

def waveT (Z : W.Aurora D) (K : Killing) (v : Fin n → S.Union) (T : S.Stress)
    (j : Fin (n+1)) (a : Axis) (x : SpacePoints n) (u : Times n) (z : ℂ) (r : Space3) := tide Z K j v T a (lodge j x u r z)

def harbors (Z : W.Aurora D) (K : Killing) (v : Fin n → S.Union) (T : S.Stress)
    (g : Probe Space3) (j : Fin (n+1)) (x : SpacePoints n) (u : Times n) (z : ℂ) :=
    ∫ r, g r * waveT Z K v T j timeAxis x u z r

def drift (g : Probe Space3) (i : SpaceAxis) := (∂_{needle i} g)
lemma drift_at (g : Probe Space3) (i : SpaceAxis) (r) : drift g i r=fderiv ℝ g r (needle i) := SchwartzMap.lineDerivOp_apply_eq_fderiv ..
lemma drift_compact (g : Probe Space3) (hg : HasCompactSupport ⇑g) (i : SpaceAxis) : HasCompactSupport ⇑(drift g i) := by
  refine IsCompact.of_isClosed_subset hg (isClosed_tsupport _) (closure_minimal ?_ (isClosed_tsupport _))
  intro x hx
  by_contra h
  apply hx
  rw [drift_at,fderiv_of_notMem_tsupport ℝ h]; simp

def docks (Z : W.Aurora D) (K : Killing) (v : Fin n → S.Union) (T : S.Stress)
    (g : Probe Space3) (j : Fin (n+1)) (x : SpacePoints n) (u : Times n) (z : ℂ) :=
    ∑ i : SpaceAxis, ∫ r, drift g i r * waveT Z K v T j i.castSucc x u z r

lemma waveT_cont {A : Type*} [TopologicalSpace A] {s : Set A} {x : A → SpacePoints n}
    {u : A → Times n} {z : A → ℂ} {r : A → Space3}
    (j : Fin (n+1)) (hx : ContinuousOn x s) (hu : ContinuousOn u s) (hz : ContinuousOn z s)
    (hr : ContinuousOn r s) (hh : ∀ p∈s, hole j (u p) (z p) ∈ strict (n+1))
    (K : Killing) (v : Fin n → S.Union) (T : S.Stress) (a) (hZ : Z.FullBody F) :
    ContinuousOn (fun p => waveT Z K v T j a (x p) (u p) (z p) (r p)) s := by
  let f := fun p => lodge j (x p) (u p) (r p) (z p)
  have hw := (hx.prodMk hu).prodMk (hr.prodMk hz)
  have hc : ContinuousOn f s := by
    change ContinuousOn ((fun p : (SpacePoints n × Times n) × (Space3 × ℂ) => lodge j p.1.1 p.1.2 p.2.1 p.2.2) ∘
      (fun p => ((x p, u p),(r p,z p)))) s
    exact (lodge_cont j).comp_continuousOn hw
  have he : MapsTo f s (tube (n+1)) := fun p hp => laid_inside _ (hh p hp)
  change ContinuousOn (tide Z K j v T a ∘ f) s
  exact (tide_analytic K j v T a hZ).continuousOn.comp hc he

lemma harbors_cont {A : Type*} [TopologicalSpace A] {s : Set A} {x : A → SpacePoints n}
    {u : A → Times n} {z : A → ℂ}
    (j : Fin (n+1)) (hx : ContinuousOn x s) (hu : ContinuousOn u s) (hz : ContinuousOn z s)
    (hh : ∀ p∈s, hole j (u p) (z p) ∈ strict (n+1))
    (K : Killing) (v : Fin n → S.Union) (T : S.Stress) (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hZ : Z.FullBody F) :
    ContinuousOn (fun p => harbors Z K v T g j (x p) (u p) (z p)) s := by
  have hm : MapsTo Prod.fst (s ×ˢ (univ:Set Space3)) s := fun p hp => hp.1
  refine continuousOn_integral_of_compact_support hg ?_ (fun p w _ ht => ?_)
  · exact (g.continuous.comp continuous_snd).continuousOn.mul
      (waveT_cont j (hx.comp continuous_fst.continuousOn hm) (hu.comp continuous_fst.continuousOn hm)
        (hz.comp continuous_fst.continuousOn hm) continuous_snd.continuousOn (fun p hp => hh p.1 hp.1) K v T timeAxis hZ)
  change g w * _=0
  rw [image_eq_zero_of_notMem_tsupport ht,zero_mul]

lemma integral_harbors (A : Set ℂ) (hA : IsOpen A) (p) (hp : p∈A) (j : Fin (n+1))
    (x : SpacePoints n) (u : ℂ → Times n) (z : ℂ → ℂ) (hu : ContinuousOn u A) (hz : ContinuousOn z A)
    (hh : ∀ t∈A, hole j (u t) (z t) ∈ strict (n+1))
    (K : Killing) (v : Fin n → S.Union) (T : S.Stress) (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hZ : Z.FullBody F)
    (f : ℂ → Space3 → ℂ) (hf : ∀ w∈A, ∀ r, HasDerivAt (fun y => waveT Z K v T j timeAxis x (u y) (z y) r) (f w r) w) :
    HasDerivAt (fun w => harbors Z K v T g j x (u w) (z w)) (∫ r, g r*f p r) p := by
  have hm : MapsTo Prod.fst (A ×ˢ (univ:Set Space3)) A := fun p hp => hp.1
  refine (compact_analytic_int hA hp (F:=fun w r => g r*waveT Z K v T j timeAxis x (u w) (z w) r)
    (G:=fun w r => g r*f w r) ?_ (fun x p hp => (hf p hp x).const_mul _) hg (fun p _ w ht => ?_)).2
  · exact (g.continuous.comp continuous_snd).continuousOn.mul (waveT_cont j continuousOn_const
      (hu.comp continuous_fst.continuousOn hm) (hz.comp continuous_fst.continuousOn hm)
      continuous_snd.continuousOn (fun p hp => hh p.1 hp.1) K v T timeAxis hZ)
  rw [image_eq_zero_of_notMem_tsupport ht,zero_mul]

lemma harbors_hol (A : Set ℂ) (hA : IsOpen A) (j : Fin (n+1))
    (x : SpacePoints n) (u : ℂ → Times n) (z : ℂ → ℂ) (hu : DifferentiableOn ℂ u A) (hz : DifferentiableOn ℂ z A)
    (hh : ∀ t∈A, hole j (u t) (z t) ∈ strict (n+1))
    (K : Killing) (v : Fin n → S.Union) (T : S.Stress) (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hZ : Z.FullBody F) :
    DifferentiableOn ℂ (fun p => harbors Z K v T g j x (u p) (z p)) A := fun p hp => by
  let f := fun w r => deriv (fun y => waveT Z K v T j timeAxis x (u y) (z y) r) w
  apply (integral_harbors A hA p hp j x u z hu.continuousOn hz.continuousOn hh K v T g hg hZ f ?_).differentiableAt.differentiableWithinAt
  intro w hw r
  exact (((tide_analytic K j v T timeAxis hZ) _ (laid_inside _ (hh w hw))).differentiableAt.comp w
    ((lodge_hol j x r).differentiableAt.comp w ((hu.prodMk hz).differentiableAt (hA.mem_nhds hw)))).hasDerivAt

lemma waveT_smooth (K : Killing) (v : Fin n → S.Union) (T : S.Stress) (j : Fin (n+1))
    (x : SpacePoints n) (u : Times n) (z : ℂ) (h : hole j u z∈strict (n+1)) (a : Axis) (hZ : Z.FullBody F) :
    ContDiff ℝ ∞ (waveT Z K v T j a x u z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  change ContDiffAt ℝ ∞ (tide Z K j v T a ∘ fun r => lodge j x u r z) r
  exact ((((tide_analytic K j v T a hZ) (lodge j x u r z) (laid_inside _ h)).restrictScalars (𝕜 := ℝ)).contDiffAt).comp r
    (lodge_smooth j x u z).contDiffAt

lemma waveT_space (K : Killing) (v : Fin n → S.Union) (T : S.Stress) (j : Fin (n+1))
    (x : SpacePoints n) (u : Times n) (z : ℂ) (h : hole j u z∈strict (n+1)) (a : Axis) (hZ : Z.FullBody F) (r : Space3) (i : SpaceAxis) :
    fderiv ℝ (waveT Z K v T j a x u z) r (needle i) =
      fderiv ℂ (tide Z K j v T a) (lodge j x u r z) (wickSlice _ (Points.direction j i.castSucc)) := by
  have he := ((tide_analytic K j v T a hZ) (lodge j x u r z) (laid_inside _ h)).differentiableAt.hasFDerivAt
  have ht := ((waveT_smooth K v T j x u z h a hZ).differentiable (by simp)).differentiableAt (x:=r)
  refine HasDerivAt.unique (ht.hasFDerivAt.hasLineDerivAt (needle i)) ?_
  refine HasFDerivAt.comp_hasDerivAt_of_eq (f := fun t : ℝ => lodge j x u (r+t • needle i) z)
    0 (he.restrictScalars ℝ) (lodge_r j x u r z i) ?_
  simp

lemma harbors_speed (K : Killing) (j : Fin (n+1)) (v : Fin n → S.Union) (T : S.Stress)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g)
    (hT : Table.Conserved P H T) (hu : U.Hierarchy) (hs : S.Symmetric) (hi : P.Inclusions S)
    (hd : P.Derivatives U) (hF : F.Region U) (hZ : Z.FullBody F) (x : SpacePoints n) (u : Times n) (z : ℂ)
    (h : hole j u z∈strict (n+1)) :
    HasDerivAt (harbors Z K v T g j x u) (-I*docks Z K v T g j x u z) z := by
  let A := hole j u ⁻¹' strict (n+1)
  have hp : IsOpen A := (open_strict _).preimage (show Continuous (hole j u) from
    (hole_hol j).continuous.comp (continuous_const.prodMk continuous_id))
  let f := fun w r => fderiv ℂ (tide Z K j v T timeAxis) (lodge j x u r w) (realPartL _ (Points.direction j timeAxis))
  have hf (w) (hw : w∈A) (r) : HasDerivAt (fun z => waveT Z K v T j timeAxis x u z r) (f w r) w :=
    ((tide_analytic K j v T timeAxis hZ) _ (laid_inside _ hw)).differentiableAt.hasFDerivAt.comp_hasDerivAt w (lodge_z j x u r w)
  refine (integral_harbors A hp z h j x (fun _ => u) id continuousOn_const continuousOn_id (fun _ h => h) K v T g hg hZ f hf).congr_deriv ?_
  let w (i : SpaceAxis) := waveT Z K v T j i.castSucc x u z
  let WX (i : SpaceAxis) (r) := fderiv ℝ (w i) r (needle i)
  have hm (r) : f z r=I* ∑ i : SpaceAxis, WX i r := by
    have he := tide_div K j v T hT hu hs hi hd hF hZ (lodge j x u r z) (laid_inside _ h)
    rw [Fin.sum_univ_castSucc] at he
    change (∑ i : SpaceAxis, fderiv ℂ _ _ _)+ fderiv ℂ _ _ (wickSlice _ (Points.direction j timeAxis))=0 at he
    simp_rw [← waveT_space K v T j x u z h _ hZ] at he -- rewrites only castSucc
    rw [wick_dir, map_smul] at he
    change (∑ i, WX i r) + wick timeAxis*f z r=0 at he
    rw [wick,if_pos rfl] at he
    rw [eq_neg_of_add_eq_zero_left he]; simp [← mul_assoc]
  have he i : ContDiff ℝ ∞ (w i) := waveT_smooth K v T j x u z h _ hZ
  have hw i : Continuous (WX i) := ((he i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hi i : Integrable (fun r => g r*WX i r) := (g.continuous.mul (hw i)).integrable_of_hasCompactSupport hg.mul_right
  have hb i : (∫ r, g r*WX i r)= -(∫ r, drift g i r*w i r) := by
    have hq : Integrable (fun r => drift g i r*w i r) := ((drift g i).continuous.mul (he i).continuous).integrable_of_hasCompactSupport
      (drift_compact g hg i).mul_right
    simp_rw [drift_at] at hq ⊢
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hq (hi i)
      ((g.continuous.mul (he i).continuous).integrable_of_hasCompactSupport hg.mul_right)
      (fun _ _ => g.differentiableAt) (fun r _ => (he i).differentiable (by simp) r)
  change (∫ r, g r*f z r)=-I*docks Z K v T g j x u z
  simp_rw [hm, show ∀ r, g r*(I*∑ i, WX i r)=I*∑ i : SpaceAxis,g r*WX i r from fun r => by rw [← Finset.mul_sum,mul_left_comm]]
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]; simp_rw [hb]; simp [docks,w]
end YM.EveryPhase.Stress
