import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.ColumnL

/-!
# Fluid symmetry under block gauge at V

At any fundamental calibration. J invariant follows from true LocalRatio
by compact detection (F05 method). -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Hues
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll  
open  Ursell Trees    Metric Set
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {L : Side} {Ñ : ChartRatio G}
private lemma detects {E : Type} [MetricSpace E] [MeasureSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)]
    [Measure.IsOpenPosMeasure (volume : Measure E)] [ProperSpace E] {x : E} {s : Set E}
    {F H : E → ℝ} (hs : s ∈ 𝓝 x) (he : ∀ C : Set E, IsCompact C → C ⊆ s →
      (∫⁻ y in C, ENNReal.ofReal (F y)) = ∫⁻ y in C, ENNReal.ofReal (H y))
    (hF : ContinuousAt F x) (hH : ContinuousAt H x) (hp : 0 ≤ F x) : H x ≤ F x := by
  by_contra! hn
  obtain ⟨a,ha,hb⟩ := exists_between hn
  obtain ⟨b,hab,hb'⟩ := exists_between hb
  have hN : ∀ᶠ y in 𝓝 x, y∈s ∧ F y < a ∧ b < H y :=
    (show ∀ᶠ y in 𝓝 x, y∈s from hs).and ((hF.eventually (gt_mem_nhds ha)).and (hH.eventually (lt_mem_nhds hb')))
  obtain ⟨d,hd,h⟩ := nhds_basis_closedBall.mem_iff.mp hN
  let C := closedBall x d
  have hu (y : E) (hy : y ∈ C) : y∈s ∧ F y < a ∧ b < H y := h hy
  have hv : IsCompact C := isCompact_closedBall x d
  have hw : 0 < volume C := lt_of_lt_of_le
    (isOpen_ball.measure_pos volume ⟨x,mem_ball_self hd⟩) (measure_mono ball_subset_closedBall)
  refine (he C hv (fun y hy => (hu y hy).1)).not_lt ?_
  calc
    _ ≤ ∫⁻ (_ : E) in C, ENNReal.ofReal a := setLIntegral_mono' hv.measurableSet (fun y hy =>
          ENNReal.ofReal_le_ofReal (hu y hy).2.1.le)
    _ < ∫⁻ (_ : E) in C, ENNReal.ofReal b := by
          simp only [lintegral_const, Measure.restrict_apply_univ]
          exact ENNReal.mul_lt_mul_left hw.ne' hv.measure_lt_top.ne
            ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hp.trans ha.le)).mpr hab)
    _ ≤ _ := setLIntegral_mono' hv.measurableSet (fun y hy =>
          ENNReal.ofReal_le_ofReal (hu y hy).2.2.le)

def skew (p : G.El) : G.Color≃ₗᵢ[ℝ] G.Color := by
  let f : G.Color→ₗᵢ[ℝ] G.Color := ⟨G.adjoint p,G.norm_adjoint p⟩
  refine LinearIsometryEquiv.ofSurjective f (fun x=> ⟨G.adjoint p⁻¹ x,?_⟩)
  change G.adjoint p (G.adjoint _ x)=_; rw [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one]


lemma keyship (h : LocalRatio Ñ) (v : G.El) (x : G.Color) (hk : x∈Metric.ball 0 Ñ.radius) :
    Ñ.J (skew v x)=Ñ.J x := by
  let F p:= Ñ.scale*Ñ.J p; let s:=Metric.ball (0:G.Color) Ñ.radius
  let f:=skew v
  let g := (Homeomorph.mulLeft v).trans (Homeomorph.mulRight v⁻¹)
  have hv x : G.lieExp (f x)=g (G.lieExp x) := Channel.exp_adjoint ..
  have hp : s ∈ 𝓝 x := isOpen_ball.mem_nhds hk
  have hg : MeasurePreserving g G.probHaar G.probHaar := (measurePreserving_mul_right G.probHaar v⁻¹).comp
      (measurePreserving_mul_left G.probHaar v)
  have hf u (hx : u∈s) : f u∈s := by unfold s at *; unfold f; simpa using hx
  have ht (C : Set G.Color) (hp : IsCompact C) (hs : C⊆s) : (∫⁻ y in C, ENNReal.ofReal (F y))= G.probHaar (G.lieExp '' C) := by
    have hx : MeasurableSet (G.lieExp '' C) := (hp.image G.lieExp_cont).measurableSet
    have hh : G.lieExp ⁻¹' (G.lieExp '' C) ∩s=C := by
      refine Subset.antisymm (fun x ⟨h',hg⟩=>?_) (fun x hy=> ⟨mem_image_of_mem _ hy,hs hy⟩)
      obtain ⟨y,hy,hh⟩:=h'; exact h.inject (hs hy) hg hh ▸ hy
    have hr := h.actual
    have hw : G.probHaar (G.lieExp '' C)=(G.probHaar.restrict (G.lieExp '' s)) (G.lieExp '' C) := by
      rw [Measure.restrict_apply hx, inter_eq_left.mpr (Set.image_mono hs)]
    rw [hw, ← hr,Measure.map_apply G.lieExp_cont.measurable hx, withDensity_apply _ (G.lieExp_cont.measurable hx), Measure.restrict_restrict (G.lieExp_cont.measurable hx), hh]
  have hh (C : Set G.Color) (hp : IsCompact C) (hs : C⊆s) : (∫⁻ y in C, ENNReal.ofReal (F y))=∫⁻ y in C, ENNReal.ofReal (F (f y)) := by
    let Y:= f '' C
    have ht':f ⁻¹' Y=C := f.injective.preimage_image _
    have hX := f.measurePreserving.setLIntegral_comp_preimage_emb f.toHomeomorph.measurableEmbedding (fun i=> ENNReal.ofReal (F i)) Y
    rw [ht'] at hX; rw [hX, ht C hp hs,ht Y (hp.image f.continuous) (image_subset_iff.mpr (fun u hx=> hf u (hs hx))),
      show G.lieExp '' Y=g '' (G.lieExp '' C) by unfold Y; rw [← image_comp,← image_comp, show G.lieExp ∘ f=g ∘ G.lieExp from funext hv]]
    have hm := hg.measure_preimage (s:=g '' (G.lieExp '' C)) (( (hp.image G.lieExp_cont).image g.continuous).measurableSet.nullMeasurableSet)
    rw [g.injective.preimage_image] at hm; exact hm
  have hu : ContinuousAt F x := continuousAt_const.mul (h.germ _ hk).continuousAt
  have hk' : ContinuousAt (F ∘ f) x :=
      (ContinuousAt.comp (f:=f) (g:=F) (continuousAt_const.mul (h.germ _ (hf _ hk)).continuousAt) f.continuous.continuousAt)
  have hm : F (f x)=F x := le_antisymm (detects (H:=F ∘ f) hp hh hu hk' (mul_nonneg h.scale.le (h.pos x hk).le))
    (detects (F:=F∘ f) hp (fun A h hz=> (hh A h hz).symm) hk' hu (mul_nonneg h.scale.le (h.pos _ (hf x hk)).le))
  exact mul_left_cancel₀ h.scale.ne' hm
end YM.ConnectedActivityE6.Hues
