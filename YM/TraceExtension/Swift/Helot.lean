import YM.TraceExtension.Swift.Griff
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Dome
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Set Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Matrix
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory
open PhysicalNext.JointLoad.Heir
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {n:Side}{Z Y X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
    [NormedAddCommGroup Z][NormedSpace ℝ Z]{k:ℕ} {V:Type}[TopologicalSpace V] [SecondCountableTopology V][CompactSpace V][MeasurableSpace V][OpensMeasurableSpace V] (μ: Measure V)[IsProbabilityMeasure μ]
variable [FiniteDimensional ℝ X] (F: X→Y→Z) (t:V→Y)(x:X) (hx:∀ i:V,ContDiffAt ℝ k (Function.uncurry F) (x,t i))(ht:Continuous t)
namespace Ebon
include ht hx
lemma course : Planned.AtomRegular.Covered μ (fun v i=> F i (t v)) k x:=by
    let Q:={y:X × Y| ContDiffAt ℝ k (uncurry F) y}; have hQ:IsOpen Q:= isOpen_iff_mem_nhds.mpr fun y hy=> (show ContDiffAt ℝ k (uncurry F) y from hy).eventually (by simp)
    obtain ⟨A,B,hA,hB,h,hb,H⟩:= generalized_tube_lemma (isCompact_singleton (x:=x)) (isCompact_range ht) hQ (show {x}×ˢ Set.range t⊆ Q from by rintro ⟨w,q⟩ ⟨hv,i,rfl⟩; exact (show w=x from hv).symm ▸ hx i)
    obtain ⟨e,he,hp⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (hA.mem_nhds (h (Set.mem_singleton _))); let W:= flip F
    have hl(y:X × V)(hy:y.1∈A)(j:ℕ)(hj:j≤k) : ContinuousAt (fun z:X×V=> docked W j (z.1,t z.2)) y:=by
       apply ContinuousAt.comp (g:=docked W j) (f:=fun z:X× V=>(z.1,t z.2))
       · exact docked_cont (f:=W) (H ⟨hy,hb (mem_range_self ..)⟩) hj
       exact (continuous_fst.prodMk (ht.comp continuous_snd)).continuousAt
    let P:= Set.prod (closedBall x e) (Set.univ: Set V)
    choose! C hC using fun j:ℕ=>fun hj:j≤k=> ((isCompact_closedBall ..).prod (isCompact_univ (X:=V))).exists_bound_of_continuousOn (s:=P) (show ContinuousOn (fun z:X× V=>docked W j (z.1,t z.2)) P from (fun p hh=> (hl _ (hp hh.1) _ hj).continuousWithinAt))
    refine ⟨ball x e,isOpen_ball,mem_ball_self he,(fun _=> ∑ i∈ Finset.range (k+1), |C i|),⟨Eventually.of_forall (fun p x hh=> ?_),fun j hj y hy=> ?_,integrable_const _,Eventually.of_forall (fun i y hy j hj=>?_)⟩⟩
    · exact ContDiffAt.comp (n:=(k:ℕ∞ω)) (g:=uncurry F) (f:=fun y:X=>(y,t p)) x (H ⟨hp (ball_subset_closedBall hh),hb (mem_range_self ..)⟩) (contDiffAt_id.prodMk contDiffAt_const)
    · refine (continuous_iff_continuousAt.mpr fun z:V=> show ContinuousAt (fun i:V=> iteratedFDeriv ℝ j (fun x=>F x (t i)) y) z from ( (hl (y,z) (hp (ball_subset_closedBall hy)) j hj).comp (f:=fun z:V=>(y,z)) (continuousAt_const.prodMk continuousAt_id))).aestronglyMeasurable
    exact (hC _ hj (y,i) ⟨ball_subset_closedBall hy,mem_univ _⟩).trans ((le_abs_self _).trans (Finset.single_le_sum (s:= Finset.range (k+1)) (f:=fun j=>|C j|) (fun j _=>abs_nonneg (C j)) (Finset.mem_range.mpr (by omega))))
lemma fond [CompleteSpace Z] (C:ℝ)(he:∀ i,Through k (fun y=> F y (t i)) x C) : Through k (fun x=> ∫ v,F x (t v) ∂μ) x C:=by
    obtain ⟨p,hp,hv,b,h⟩:= course μ F t x hx ht
    refine ⟨h.germ hp hv,fun i hi=>?_⟩
    rw[show iteratedFDeriv ℝ i (fun x=> ∫ v,F x (t v) ∂μ) x =_ from (h.less hi).differentiate hp hv]; exact le_trans (norm_integral_le_of_norm_le_const (Eventually.of_forall (fun i'=> (he i').pay _ hi))) (by simp)
end Ebon
end YM.Trace.Swift
