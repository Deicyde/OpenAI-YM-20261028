import YM.OPE.Orbits.Words

/-! Smooth compact-parameter integrations used by the covariant detectors.
No differentiability in a coordinate on the compact group itself is presumed.
Instead use an auxiliary point in an ambient normed space. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Set Filter MeasureTheory Extraction Table Word
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
universe u
variable {α Y: Type*}{X E:Type u}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
    [NormedAddCommGroup Y][NormedSpace ℝ Y]
    [NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
    [MeasurableSpace α]{μ:Measure α}[IsFiniteMeasure μ]{p:α→Y}{K:Set Y}{O:Set X}
omit [NormedSpace ℝ Y] [NormedSpace ℝ E] [CompleteSpace E] in
lemma local_bound {f:X×Y→ E}{x:X} (hf:∀ z∈O ×ˢ K,ContinuousAt f z) (hp:IsCompact K) (ho:IsOpen O) (hx:x∈O) : ∃ c:ℝ,∀ᶠ y:X in 𝓝 x,y∈O ∧ ∀ b∈K,‖f (y,b)‖ ≤ c:=by
    obtain ⟨ε,hε,ht⟩:= Metric.mem_nhds_iff.mp (ho.mem_nhds hx)
    have hw: Metric.closedBall x (ε/2) ⊆ O:= (Metric.closedBall_subset_ball (half_lt_self hε)).trans ht
    obtain ⟨c,hc⟩:=((isCompact_closedBall x (ε/2)).prod hp).exists_bound_of_continuousOn (f:=f) (fun _ h=> (hf _ ⟨hw h.1,h.2⟩).continuousWithinAt)
    exact ⟨c,(show ∀ᶠ a in 𝓝 x,a∈Metric.closedBall x (ε/2) from Metric.closedBall_mem_nhds x (half_pos hε)).mono (fun y hy => ⟨hw hy,fun b hb=>hc (y,b) ⟨hy,hb⟩⟩)⟩
local instance : MeasurableSpace Y := borel Y
local instance : BorelSpace Y:= ⟨rfl⟩
omit [NormedSpace ℝ Y] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ X] [IsFiniteMeasure μ] in
lemma in_parameters {f:X×Y→E} (hK:IsCompact K)(hw:∀ a,p a∈K)(hp:AEMeasurable p μ) (hf:∀ z∈O ×ˢ K,ContinuousAt f z) {x:X}(hx:x∈O): AEStronglyMeasurable (fun a:α=>f (x,p a)) μ:=by
    haveI : CompactSpace K:= isCompact_iff_compactSpace.mp hK
    have h := (continuousOn_iff_continuous_restrict (s:=K)).mp (show ContinuousOn (fun y:Y=>f (x,y)) K from fun b hb=>
         ((hf _ (mk_mem_prod hx hb)).comp_of_eq (continuous_const.prodMk continuous_id|>.continuousAt) rfl).continuousWithinAt)
    exact h.comp_aestronglyMeasurable ((hp.subtype_mk (s:=K) (hfs:=hw)).aestronglyMeasurable)
lemma parametrize_smooth_nat (k:ℕ){f:X×Y→ E} (hf:∀ z∈O ×ˢ K,ContDiffAt ℝ (k:WithTop ℕ∞) f z)(ho:IsOpen O)(hK:IsCompact K)(hw:∀ a,p a∈K)(hp:AEMeasurable p μ) : ContDiffOn ℝ k (fun x=>∫ a:α,f (x,p a) ∂μ) O:= by
   have h1(x) (hx:x∈O):AEStronglyMeasurable (fun a:α=>f (x,p a)) μ:=
      in_parameters hK hw hp (fun z hz=>(hf z hz).continuousAt) hx
   induction k generalizing E with
   | zero=>
         rw [Nat.cast_zero,contDiffOn_zero]; intro x hx; apply ContinuousAt.continuousWithinAt; obtain ⟨C,hC⟩:= local_bound (fun z hz=> (hf z hz).continuousAt) hK ho hx
         exact continuousAt_of_dominated (bound:=fun _=>C) ((show ∀ᶠ x' in 𝓝 x, x'∈O from ho.mem_nhds hx).mono h1) (hC.mono (fun y hy=> Eventually.of_forall fun a=>hy.2 _ (hw a))) (integrable_const _) (Eventually.of_forall fun a => (hf _ (mk_mem_prod hx (hw a))).continuousAt.comp_of_eq (continuous_id.prodMk continuous_const).continuousAt rfl)
   | succ k ih =>
       let D (z:X×Y) := fderiv ℝ (fun x:X=> f (x,z.2)) z.1
       have hd(z)(hz:z∈O ×ˢ K):ContDiffAt ℝ (k:WithTop ℕ∞) D z := by
           let u (q:X×Y)(x:X):=(x,q.2)
           have ht:ContDiffAt ℝ (↑((k+1):ℕ): WithTop ℕ∞) (Function.uncurry u) (z,z.1):= contDiffAt_snd.prodMk (contDiffAt_snd.comp _ contDiffAt_fst)
           have he:= ((show ContDiffAt ℝ (↑((k+1):ℕ): WithTop ℕ∞) f (Function.uncurry u (z,z.1)) from hf z hz)).comp (z,z.1) ht
           exact ContDiffAt.fderiv (f:=fun q:X×Y=>f ∘ u q) (x₀:=z) (g:=Prod.fst) (show ContDiffAt .. from he) contDiffAt_fst (by simp) -- inspect
       have h2 (x:X)(hx:x∈O): AEStronglyMeasurable (fun a:α=>D (x,p a)) μ :=in_parameters hK hw hp (fun z hz=>(hd z hz).continuousAt) hx
       have hd' (x:X)(hx:x∈O):HasFDerivAt (fun y=>∫ a:α,f (y,p a) ∂μ) (∫ a:α,D (x,p a) ∂μ) x:=by
           obtain ⟨c,hc⟩:= local_bound (fun z hz=>(hf z hz).continuousAt) hK ho hx
           obtain ⟨b,hb⟩:= local_bound (fun z hz=> (hd z hz).continuousAt) hK ho hx
           apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F':=fun x a=>D (x,p a)) (bound:=fun _=>b) (s:={y | y∈O ∧ ∀ q∈K, ‖D (y,q)‖ ≤ b}) hb ((show ∀ᶠ x' in 𝓝 x, x'∈O from ho.mem_nhds hx).mono h1)
              (.of_bound (h1 x hx) c (Eventually.of_forall (fun a=>((mem_of_mem_nhds hc).2 (p a) (hw a))))) (h2 x hx)
              (Eventually.of_forall fun a y hy => hy.2 _ (hw a)) (integrable_const _) (Eventually.of_forall fun a y hy=> ?_)
           apply (((hf _ (mk_mem_prod hy.1 (hw a))).comp (f:=fun y=>(y,p a)) _ (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)).hasFDerivAt
       rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_fderiv_of_isOpen ho]; refine ⟨fun y hy=>(hd' y hy).differentiableAt.differentiableWithinAt,by simp,fun y hy=>?_⟩
       exact ((ih hd h2) y hy).congr_of_eventuallyEq (EventuallyEq.filter_mono ((show ∀ᶠ x in 𝓝 y, x∈O from ho.mem_nhds hy).mono (fun x hx=>(hd' x hx).fderiv)) nhdsWithin_le_nhds) (hd' y hy).fderiv
end YM.OPE.Orbits
