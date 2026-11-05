import YM.FullVolume.Relay.Charged
import YM.FullVolume.Relay.Halo
/- At fixed period and level, analytic absolute normalization. E-Charts at true histories. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open PhysicalNext.Repeat PhysicalNext.Repeat.Muse PhysicalNext.Repeat.Pass
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}{c : Side}
open UniformSpace FullVolume Paint Paint.Tower Beam PaidBeam
lemma logOrbit (S:Price G c) (T:Team S){K:Beam (World T)}{F:sun→ Home T} (hv: ‖K‖ ≤1)(ht:∀ s:sun, World.ready ((F s):Completion (Home T))=Beam.read _ s K): Feel (fun i=> (observe T (F i)).additive S.p) (Fintype.card (Site c) * S.b):=by
    let P': Home T →L[ℝ] World T:= show Home T →L[ℝ] Completion (Home T) from Completion.toComplL
    let f : Home T→ Config G c→ ℝ := fun x=> (observe T x).additive S.p
    have he : DenseRange P':= Completion.denseRange_coe; have hx : Isometry P':= Completion.coe_isometry
    let w:ℝ:= Fintype.card (Site c)*S.b; have hw:0≤w:=mul_nonneg (Nat.cast_nonneg _) (S.b0.le)
    let Q:=Tint ℝ (Config G c); have hp(x:Home T)(U): ‖f x U‖≤ w *‖x‖:= (volumeE (observe T x) (Urns.qualifies x le_rfl) U).trans_eq (by unfold w; ring)
    let E(x:Home T):=Tint.wear (⟨f x,memℓp_infty ⟨_,Set.forall_mem_range.mpr (hp x)⟩⟩: lp (fun _:Config G c=>ℝ) ⊤)
    have hQ(x:Home T): ‖E x‖≤ w * ‖x‖:=lp.norm_le_of_forall_le (f:=Tint.cast (E x)) (mul_nonneg hw (norm_nonneg _)) (hp x)
    have hh(x:Home T): Dominated (Activities.regularOccurrence (observe T x) S.p):= Activities.ESeries (Urns.qualifies x le_rfl)
    have hl(x:Home T): (observe T x).reg=(observe T 0).reg:=rfl
    have h₁ :∀ x y:Home T,E (x+y)=E x+E y:=by
        intro x y; apply Tint.liftEqual; intro i
        let A':=observe T; change f (x+y) i=f x i+f y i
        unfold f Activities.additive; rw [← ((hh x).summable i).tsum_add ((hh y).summable i)]
        apply tsum_congr; intro j; unfold Activities.regularOccurrence; simp_rw [hl]; by_cases hv:Healthy S.p.threshold ((observe T 0).reg j).support i
        · simp_rw [masked_eq _ _ _ _ hv]; rfl
        simp [masked_ne _ _ _ _ hv]
    have h₂ (u:ℝ)(x:Home T): E (u • x)=u • E x:=by
        apply Tint.liftEqual; intro i; change f (u • x) i=u* f x i
        unfold f Activities.additive; rw [← tsum_mul_left]; apply tsum_congr; intro j; unfold Activities.regularOccurrence; simp_rw [hl]; by_cases hv:Healthy S.p.threshold ((observe T 0).reg j).support i
        · simp_rw [masked_eq _ _ _ _ hv]; rfl
        simp [masked_ne _ _ _ _ hv]
    let L:Home T →ₗ[ℝ] Q:= { toFun:=E, map_add':=h₁,map_smul':=h₂ }
    let U:= (L.mkContinuous w hQ).extend P'; have ha: ‖U‖≤ w:= (Amp.liftB P' hx he _).trans (ContinuousLinearMap.opNorm_le_bound _ hw hQ); let F' s:=Beam.read _ s K; have hS:PaidBeam F' 1:= ⟨K,hv,fun _=>rfl⟩
    have hF:= PaidBeam.transit U (map_sub _) hw (U.le_of_opNorm_le ha) F' hS; rw [mul_one] at hF
    have hD(s): P' (F s)= F' s:= ht s
    refine ⟨fun s=> U (F' s),fun s i=>?_ ,hF⟩
    dsimp only; rw [← hD];unfold U; rw [ContinuousLinearMap.extend_eq _ he hx.isUniformInducing]; rfl
lemma kinetic_tip (P: BudgetPoint) (W:RG.Clip) {y σ C: ℝ}(h:0≤y) (p: PathData G) (hp:p.Bounds W σ C y) (U:Config G c): ‖p.inChannels W P 0 U‖ ≤ Fintype.card (Site c) * PathData.loopsPrice P 0 C y:=by
    have hz(i:Signed): |p.principal W P 0 (pull i 0 U)| ≤ (Fintype.card (Site c):ℝ) * PathData.loopsPrice P 0 C y:=by simpa using p.volume_price W P 0 le_rfl (pull i 0 U) hp
    have hh : Nonempty Signed:=inferInstance; let z:ℝ:= Fintype.card Signed; have hv:0<z:=Nat.cast_pos.mpr Fintype.card_pos
    unfold PathData.inChannels; change |z⁻¹*_| ≤ _; rw [abs_mul,abs_of_pos (inv_pos.mpr hv)]
    apply le_trans (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs ..|>.trans (Finset.sum_le_sum (fun i _=>hz i))) (inv_nonneg.mpr hv.le));simp only [sum_const,card_univ,nsmul_eq_mul]; rw [inv_mul_cancel_left₀ hv.ne']
end YM.FullVolume.Nectar
#print axioms YM.FullVolume.Nectar.logOrbit
#print axioms YM.FullVolume.Nectar.kinetic_tip
