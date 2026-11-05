import YM.WilsonBulk.Build.Ring
import YM.WilsonBulk.Slice.Coupon
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Exact relative real Jacobians on chart germs

GENERAL transport regular nonlinear rooted quotient, constant spectator.
Extends Work.F05.Jacobian (compact testing at variable point). To avoid
contending with basis det costs, place measure on private chart by pushing
probability's tangent volume, and prove convergence through that measure
on both charts. (Volume rather than probability normal in charts!)
No realm size assumption; no near-uniformity. REAL germs fixed collar only.
Used to render `levy_grain`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Atelier
open Function Filter Lattice RG Wilson Precision Exterior Tree
open Sheet
open Work.F05 (toll load load_eq load_cont load_pos order_exposed)
open MeasureTheory Measure Metric Set
open scoped Topology Classical ENNReal BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f} {P : Bed}
  {ι κ E : Type} [Fintype ι] [Fintype κ]

-- point comparison with compact weights (generic local) avoiding explicit abs cert
section
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
lemma birthTest {f g : E→ℝ} {x : E} {s : Set E} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (h : 0≤g x) (hs : s ∈ 𝓝 x) (he : ∀ C : Set E, IsCompact C→ C⊆s → (∫⁻ z in C, ENNReal.ofReal (f z) ∂μ)≤∫⁻ z in C, ENNReal.ofReal (g z) ∂μ) : f x ≤ g x := by
  by_contra! hu
  obtain ⟨a,ha,hb⟩:= exists_between hu
  obtain ⟨b,hb',hc⟩:= exists_between hb
  have h₁ : ∀ᶠ z in 𝓝 x,z∈s ∧ g z<a ∧ b<f z := (show ∀ᶠ z in 𝓝 x,z∈s from hs).and ((hg.eventually (gt_mem_nhds ha)).and (hf.eventually (lt_mem_nhds hc)))
  obtain ⟨r,hr,h⟩ := nhds_basis_closedBall.mem_iff.mp h₁
  let C := closedBall x r; have hv y (hy : y∈C) : y∈s∧ g y<a ∧ b<f y := h hy
  have hi : IsCompact C := isCompact_closedBall ..
  have hm : μ C≠0 := (lt_of_lt_of_le (isOpen_ball.measure_pos μ ⟨x, mem_ball_self hr⟩) (measure_mono ball_subset_closedBall)).ne'
  apply (he C hi (fun y hy=> (hv y hy).1)).not_gt
  calc _ ≤ ∫⁻ _ in C, ENNReal.ofReal a ∂μ := setLIntegral_mono' hi.measurableSet fun i hz=> ENNReal.ofReal_le_ofReal (hv i hz).2.1.le
       _ < ∫⁻ _ in C, ENNReal.ofReal b ∂μ := by
          simp only [lintegral_const,restrict_apply_univ]; apply ENNReal.mul_lt_mul_left hm hi.measure_lt_top.ne; exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (show 0≤a by linarith)).mpr hb'
       _ ≤ _ := setLIntegral_mono' hi.measurableSet fun i hz=> ENNReal.ofReal_le_ofReal (hv i hz).2.2.le
end

namespace Coursing
variable (G) (F L : Coursing ι S)

abbrev Enter (G : Gauge) (ι : Type) := Tabletop (LegsT G ι)
def wellness : Measure (Enter G ι) := (volume : Measure (AxisChart G F.tree)).map (F.dress G).symm
instance is_add : IsAddHaarMeasure (wellness G F) := by unfold wellness; apply ContinuousLinearEquiv.isAddHaarMeasure_map
lemma exercises : MeasurePreserving (F.dress G) (wellness G F) volume := by
  let e := F.dress G; have he : Measurable e:= e.continuous.measurable; refine ⟨he,?_⟩
  unfold wellness; rw [Measure.map_map he e.symm.continuous.measurable]; change Measure.map (e ∘ e.symm) _ = _; rw [show e ∘ e.symm=id from funext fun v=>e.apply_symm_apply v,Measure.map_id]
lemma exercises_another : MeasurePreserving (L.dress G) (wellness G F) volume := by
  rw [show ((L.dress G):Enter G ι→ _) = (Work.F05.index (F.label.symm.trans L.label) ∘ F.dress G) from funext fun i=> dress_reindex G F L i]
  exact (Work.F05.index_preserves _).comp (exercises ..)
def shiftPrice (b : Enter G ι) := (Homeomorph.addRight b).trans (F.dress G).toHomeomorph
lemma shift_paid (b : Enter G ι) : MeasurePreserving (shiftPrice G L b) (wellness G F) volume := (exercises_another G F L).comp (measurePreserving_add_right _ _)
lemma bill_price_compact (J : ChartRatio G) (hh : LocalRatio J) (b : Enter G ι) (s : Set (Enter G ι)) (h : IsCompact s)
    (he : s ⊆ (shiftPrice G L b) ⁻¹' Work.F05.parcel L.tree J) :
    let f := Work.F05.exposure L.tree 0 ∘ (shiftPrice G L b); L.tree.order G (f '' s) = ∫⁻ z in s, ENNReal.ofReal (load L.tree J (shiftPrice G L b z)) ∂wellness G F := by
  intro f; unfold f; rw [image_comp,order_exposed L.tree hh 0 _ (h.image (shiftPrice G L b).continuous) (image_subset_iff.mpr he)]
  exact ((shift_paid G F L b).setLIntegral_comp_emb (shiftPrice G L b).measurableEmbedding (fun y=>ENNReal.ofReal (load L.tree J y)) s).symm
variable (R : Carries G S) (J : ChartRatio G)
-- germ can be at PER POINT in chart and no common size required.
def privateGate (b d : Enter G ι) (T : Enter G ι → Enter G ι) (x : Enter G ι) : Prop :=
  ContDiffAt ℝ ω T x ∧ shiftPrice G F b x∈ Work.F05.parcel F.tree J ∧ shiftPrice G L d (T x)∈ Work.F05.parcel L.tree J ∧
    Work.F05.exposure L.tree 0 (shiftPrice G L d (T x))= R.slit F.tree L.tree (Work.F05.exposure F.tree 0 (shiftPrice G F b x))
lemma privateFee (hh : LocalRatio J) (b d : Enter G ι) (T : Enter G ι → Enter G ι) (x : Enter G ι)
    (hx : ∀ᶠ y in 𝓝 x, privateGate G F L R J b d T y) :
    toll F.tree J (shiftPrice G F b x)=|(fderiv ℝ T x).det| * toll L.tree J (shiftPrice G L d (T x)) := by
  let A:= shiftPrice G F b; let B:= shiftPrice G L d; let p:= load F.tree J ∘ A; let q:= load L.tree J ∘ B
  let g z:=|(fderiv ℝ T z).det| * q (T z); let s : Set (Enter G ι) := {y|privateGate G F L R J b d T y}
  let μ:= wellness G F
  have hp:= hx.self_of_nhds
  have hw:= hp.1; have h₁ : ContinuousAt p x:= (load_cont F.tree hh hp.2.1).comp A.continuous.continuousAt
  have h₂ : ContinuousAt g x := (ContinuousLinearMap.continuous_det.continuousAt.comp (hw.fderiv_right (m:=ω) le_top).continuousAt).abs.mul (((load_cont L.tree hh hp.2.2.1).comp (f:=B) B.continuous.continuousAt).comp hw.continuousAt)
  have H (C : Set (Enter G ι)) (hC : IsCompact C) (he : C⊆s) : (∫⁻ z in C, ENNReal.ofReal (p z) ∂μ)=∫⁻ z in C, ENNReal.ofReal (g z) ∂μ := by
    let f:= Work.F05.exposure F.tree 0 ∘ A; let h:= Work.F05.exposure L.tree 0 ∘ B; let t:= R.slit F.tree L.tree
    have hv (i : Enter G ι) (hi : i∈C) : privateGate G F L R J b d T i:= he hi
    have hd i (hi : i∈C) := ((hv i hi).1.differentiableAt (by simp))
    have ha i (hi : i∈C) : h (T i)=t (f i):= (hv i hi).2.2.2
    let X := T '' C
    have hk : IsCompact X := hC.image_of_continuousOn fun i hi=> (hd i hi).continuousAt.continuousWithinAt
    have him : h '' X=t '' (f '' C) := by unfold X; rw [← image_comp,← image_comp]; apply EqOn.image_eq; exact fun z h=>ha z h
    have H : Continuous h := (Work.F05.exposure_continuous L.tree).comp (f:=fun i=>(0,B i)) (continuous_const.prodMk B.continuous)
    have Hn := (R.pass_paid F.tree L.tree).measure_preimage (s:= h '' X) ((hk.image H).measurableSet.nullMeasurableSet)
    rw [show (R.slit F.tree L.tree) ⁻¹' (h '' X)= f '' C by rw [him]; exact t.injective.preimage_image _] at Hn
    have hi : InjOn T C := fun y hy z hz hh' => A.injective (Work.F05.exposure_inj F.tree hh 0 (hv y hy).2.1 (hv z hz).2.1 (t.injective ((ha y hy).symm.trans ((congr_arg h hh').trans (ha z hz)))))
    calc _ = F.tree.order G (f '' C) := (bill_price_compact G F F J hh b _ hC (fun z h=> (hv z h).2.1)).symm
         _ = L.tree.order G (h '' X) := Hn
         _ = ∫⁻ z in X, ENNReal.ofReal (q z) ∂μ := bill_price_compact G F L J hh d X hk (image_subset_iff.mpr fun i hi=> (hv i hi).2.2.1)
         _ = ∫⁻ z in C, ENNReal.ofReal |(fderiv ℝ T z).det| * ENNReal.ofReal (q (T z)) ∂μ := lintegral_image_eq_lintegral_abs_det_fderiv_mul (wellness G F) hC.measurableSet (fun z hz=> (hd z hz).hasFDerivAt.hasFDerivWithinAt) hi _
         _ = _ := by simp only [g, ENNReal.ofReal_mul (abs_nonneg _)]
  have hpx : 0≤p x := (load_pos F.tree hh hp.2.1).le
  have he : p x=g x := le_antisymm (birthTest (wellness G F) (s:=s) h₁ h₂ (mul_nonneg (abs_nonneg _) (load_pos L.tree hh hp.2.2.1).le) hx fun C hC hD=> (H C hC hD).le) (birthTest (wellness G F) (s:=s) h₂ h₁ hpx hx fun C hC hD=> (H C hC hD).symm.le)
  apply mul_left_cancel₀ (pow_ne_zero (Fintype.card F.tree.Free) hh.scale.ne'); unfold p g q Function.comp at he
  rw [load_eq,load_eq,← Work.F05.free_card F.tree L.tree,mul_left_comm |(fderiv ℝ T x).det|] at he
  exact he
end Coursing
end YM.WilsonBulk.Atelier
