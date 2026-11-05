import YM.RG08.Prism.Glow
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ratio
import YM.Work.F05.Jacobian

/-!
# Real Haar toll on *any* approved local symmetry of the slice, even with directed link
 permutation or membership switches. E unmasked. Adapted the compact-window argument from
 baseline F05 Jacobian to arbitrary analytic moves and any fixed externals. I only. Keep
 volume receipts exactly. This version based at coarse zero (unscaled!) and same tree each end.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Slate
open Filter Function MeasureTheory Lattice Exterior Wilson RG Precision Work.F05 Set YM.Next.SectorChange Tree
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S: Ratio c f}(B:Forest S){Z:ChartRatio G}

structure House (U:Forest S) where
 arrow : U.Slice G→ B.Slice G
 sound : Injective arrow
 cost : MeasurePreserving arrow (U.order G) (B.order G)

def witness (P:ChartRatio G)(L:House B (G:=G) B)(side:AxisChart G B→AxisChart G B):Set (AxisChart G B) := {y| y ∈ parcel B P ∧ side y∈parcel B P ∧ ContDiffAt ℝ ω side y ∧ exposure B 0 (side y)= L.arrow (exposure B 0 y) }
lemma validFee {L:House B (G:=G) B}{x:AxisChart G B}{X: AxisChart G B→ AxisChart G B}(hs :witness B Z L X∈ 𝓝 x)(h:LocalRatio Z):
 toll B Z x= toll B Z (X x) * |(fderiv ℝ X x).det|:=by
 let W:=witness B Z L X
 have ht:= show x∈W from mem_of_mem_nhds hs
 let H:=fun y=>load B Z (X y) * |(fderiv ℝ X y).det|
 let F:=load B Z
 obtain ⟨hG,hT,hO,-⟩: x∈parcel B Z ∧ X x∈parcel B Z ∧ ContDiffAt ℝ ω X x∧ _ :=ht
 have hF:ContinuousAt F x:=load_cont B h hG
 have he: ContinuousAt H x:= (((load_cont B h hT).comp hO.continuousAt).mul (ContinuousLinearMap.continuous_det.continuousAt.comp (hO.fderiv_right (m:=ω) (by simp)).continuousAt).abs)
 let E:=exposure (G:=G) B 0
 have hu (s:Set (AxisChart G B))(hc:IsCompact s)(hx:s⊆W): ∫⁻ y in s, ENNReal.ofReal (F y) = ∫⁻ y in s, ENNReal.ofReal (H y):=by
    have hv y (hy:y∈s):y∈parcel B Z ∧ X y∈parcel B Z ∧ ContDiffAt ℝ ω X y ∧ E (X y)=L.arrow (E y) :=hx hy
    have hD y (hy:y∈s):HasFDerivAt X (fderiv ℝ X y) y:= ((hv y hy).2.2.1.differentiableAt (by simp)).hasFDerivAt
    have hm:InjOn X s:=fun a ha b hb Hab=> exposure_inj B h 0 (hv a ha).1 (hv b hb).1 <| L.sound (((hv a ha).2.2.2.symm.trans (congrArg E Hab)).trans (hv b hb).2.2.2)
    have hV:IsCompact (X '' s):=hc.image_of_continuousOn (fun i hi=> (hD _ hi).continuousAt.continuousWithinAt)
    have hE:Continuous E:=(exposure_continuous B).comp (f:=fun v=>(0,v)) (continuous_const.prodMk continuous_id)
    have hhx:E '' (X '' s)=L.arrow '' (E '' s):=by
      rw [image_image,image_image];ext z;constructor <;> rintro ⟨i,hi,rfl⟩ <;> refine ⟨i,hi,?_⟩
      · exact (hv i hi).2.2.2.symm
      exact (hv i hi).2.2.2
    have hh: (B.order G) (E '' s)=(B.order G) (E '' (X '' s)):=by
       have hi:= L.cost.measure_preimage ((hV.image hE).measurableSet.nullMeasurableSet (μ:=B.order G))
       rw [hhx,L.sound.preimage_image] at hi
       exact hi.trans (congrArg (B.order G) hhx.symm)
    rw [← Work.F05.order_exposed B h 0 s hc (fun x h=> (hv x h).1),hh,order_exposed B h 0 (X '' s) hV (by rintro _ ⟨i,hi,rfl⟩;exact (hv i hi).2.1)] -- F opaque
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hc.measurableSet (fun i hi=>(hD i hi).hasFDerivWithinAt) hm (fun y=>ENNReal.ofReal (F y))] -- g argument?
    apply setLIntegral_congr_fun hc.measurableSet;intro y hy
    dsimp only; rw [mul_comm];exact (ENNReal.ofReal_mul (load_pos B h (hv y hy).2.1).le).symm
 have Hs:F x=H x:= le_antisymm (price_le_of_caps hs he hF (mul_nonneg (load_pos B h hT).le (abs_nonneg _)) (fun i hi hv=> (hu i hi hv).symm)) (price_le_of_caps hs hF he (load_pos B h hG).le hu)
 unfold H F at Hs;rw [load_eq, load_eq, mul_assoc] at Hs;exact mul_left_cancel₀ (pow_ne_zero _ h.scale.ne') Hs
-- External sockets move on the same unit chart. Freeze before fderiv determinant.
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
lemma network (L:X → House B (G:=G) B)(M:X→AxisChart G B→AxisChart G B)(h:LocalRatio Z)
    (hx:ContDiffAt ℝ ω (uncurry M) 0)(hv:M 0 0=0)
    (he:∀ᶠ z:X×AxisChart G B in 𝓝 0, exposure B 0 (M z.1 z.2)= (L z.1).arrow (exposure B 0 z.2)):
    ∀ᶠ z:X×AxisChart G B in 𝓝 0,toll B Z z.2=toll B Z (M z.1 z.2)* |(fderiv ℝ (M z.1) z.2).det|:=by
 have hs :∀ᶠ z:X×AxisChart G B in 𝓝 0,z.2∈ witness B Z (L z.1) (M z.1):=by
    have hg:Tendsto (uncurry M) (𝓝 0) (𝓝 0):=by simpa only [Prod.fst_zero,Prod.snd_zero,hv,uncurry] using hx.continuousAt.tendsto
    have hy:=hg.eventually (parcel_zero B h)
    filter_upwards [hy, (continuous_snd.tendsto (0:X×AxisChart G B)).eventually (parcel_zero B h),hx.eventually (by simp),he] with z hh hn hj he
    exact ⟨hn,hh,hj.comp (f:=fun y=>(z.1,y)) (g:=uncurry M) z.2 (contDiffAt_const.prodMk contDiffAt_id),he⟩
 filter_upwards [eventually_eventually_nhds.mpr hs] with z hz
 refine validFee B (L:=L z.1) ?_ h
 have ht:Tendsto (fun y : AxisChart G B=> (z.1,y)) (𝓝 z.2) (𝓝 z):=continuousAt_const.tendsto.prodMk_nhds tendsto_id
 exact ht.eventually hz
end YM.RG08.Slate
