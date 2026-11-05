import YM.OPE.Orbits.Payroll

/-! Uniform fixed port geometry and rotation prices. Only their positions and finite bases (not the hierarchy) are changed throughout a comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Set Filter Extraction MeasureTheory Table
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
attribute [local instance] measO borelO YM.Work.A15.compact_ortho
local instance hμ : IsProbabilityMeasure haar := by unfold haar; apply IsProbabilityMeasure.mk; apply Measure.haarMeasure_self

variable {G:Gauge} {B:Register G}{S:Table B}{P:DiffPlan S}{X:S.Rotation}{ρ:S.RealSpin}{I J L:Type}[Fintype I][Fintype J]
    {A:L→ℝ}{φ:Filter L}{a b c u:ℝ}(hA:Tendsto A φ atTop) {x:L→I→ E4}{y:L→ J→ E4}{o:L→E4}
    {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]

include hA in
lemma compact_pricing {f:Ortho→E}(hf:Continuous f)(k:L→Ortho):RateLE φ A (fun i=> f (k i)) 0:=by
    obtain ⟨r,hr⟩:=isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
    exact RateLE.absBound r hA (Eventually.of_forall fun i=>hr _ (mem_univ _))
include hA in
lemma loaded_rate (Q:Prescription P)(hX:X.Laws P ρ)(m:ℕ)(i:Mode P)(k:L→Ortho): RateLE φ A (fun j=>X.act _ (k j) (Q.loaded i m)) 0:= compact_pricing hA (hX.spin _ _) k
include hA in
lemma turn_port_rate (hX:X.Laws P ρ)(e:Exterior B)(k:L→ Ortho)(j:Fin e.n): RateLE φ A (fun i=>turnsPort X (k i) e j) 0:= by refine compact_pricing (f:=fun q:Ortho=> X.act (expo e j) q (fields S e j)) hA ?_ k; exact hX.spin ..

variable {W K:Type*}[NormedAddCommGroup W][NormedSpace ℝ W] [MeasurableSpace K] [Nonempty K] {μ:Measure K}[hμ':IsProbabilityMeasure μ]
lemma price_integral (f:L→ K→W)(hf:∀ k:L→K, RateLE φ A (fun i=> f i (k i)) b): RateLE φ A (fun i=>∫ k,f i k ∂μ) b:=by
    intro a ha
    filter_upwards [universalize (p:=fun i k=>‖f i k‖ ≤ Real.exp (a*A i)) (fun k=>hf k a ha)] with i hi
    simpa only [Measure.real,measure_univ,hμ'.measure_univ,ENNReal.toReal_one,mul_one] using (norm_integral_le_of_norm_le_const (Eventually.of_forall hi): ‖_‖ ≤ _*μ.real univ)

lemma eventually_dock (Q:Prescription P) (ho:Tendsto (fun i:L=> away (x i) (o i)) φ (𝓝 (0:I→E4))) (hk:∀ᶠ s in φ,Injective (x s))(n:ℕ): ∀ᶠ j in φ, orbitMargin Q n (x j) (o j):=by
    have hh(j:Mode P)(e:Exterior B)(h:e∈ (Q.sheet j).support)(u:Fin e.n)(v:I):∀ᶠ p in φ,‖x p v-o p‖ < ‖bearing e u‖:= by
        have hx:Tendsto (fun q=>x q v-o q) φ (𝓝 0):=(continuous_apply v).tendsto _ |>.comp ho
        exact hx.eventually (p:=fun s:E4=>‖s‖<‖bearing e u‖) (ContinuousAt.eventually_lt (f:=fun s:E4=>‖s‖) (by fun_prop) continuousAt_const (by simpa only [norm_zero] using norm_pos_iff.mpr (Ne.symm ((beside_distinct.mp (bearing_clear e)).2.2 () u))))
    filter_upwards [(eventually_all_finset (bands P n)).mpr (fun j hj=>(eventually_all_finset (Q.sheet j).support).mpr fun e he=>eventually_all.mpr fun u=> eventually_all.mpr (fun v=> hh j e he u v)),hk] with i hi hk j hj k e he
    refine beside_distinct.mpr ⟨(away_inject _ _ |>.mpr ((Ortho.motion k).injective.comp hk)),(beside_distinct.mp (bearing_clear e)).2.1,fun v u=>?_ ⟩
    have hv:‖away (Ortho.move k ∘ x i) (Ortho.move k (o i)) v‖=‖x i v-o i‖:=congr_arg norm (show _= Ortho.motion k (x i v-o i) from (map_sub (Ortho.motion k) _ _).symm) |>.trans (LinearIsometryEquiv.norm_map _ _)
    exact fun h=> ((hi j hj e he u v)).ne ((hv.symm.trans (congr_arg norm h)))

include hA in
lemma shrinking_port [φ.NeBot](e:Exterior B)(k:L→Ortho) :
    Kept φ A 0 (fun i=>swung e (k i) (o i)) ∧ Intervals φ A 0 (fun p=>sole (o p)) (fun i=>swung e (k i) (o i)):=by
   apply swings_kept (y:=fun _=>bearing e) hA k ?_ ?_ (fun _ _=>rfl)
   · intro b hb; have hbound(i j)(v:i≠j): 0 < ‖bearing e i-bearing e j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr ((beside_distinct.mp (bearing_clear e)).2.1.ne v)) -- remove x
     exact eventually_all.mpr (fun i=>eventually_all.mpr fun j=> eventually_all.mpr (fun he=> ((RateLE.exp (-b) hA).tends (neg_neg_of_pos hb) hA).eventually (gt_mem_nhds (hbound i j he))))
   intro b hb; exact eventually_all.mpr fun ⟨⟩=>eventually_all.mpr (fun i=> ((RateLE.exp (-b) hA).tends (neg_neg_of_pos hb) hA).eventually (gt_mem_nhds (show 0 < ‖sole (0:E4) ()-bearing e i‖ from norm_pos_iff.mpr (sub_ne_zero.mpr ((beside_distinct.mp (bearing_clear e)).2.2 () i)))))
end YM.OPE.Orbits
