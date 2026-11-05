import YM.PertExtension.OrbTree
import YM.Wilson.Law
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Module.WeakDual

/-! Normalized Wilson law on inversion quotient and exact elimination of paths
through a tree **on gauge-invariant integrals**. Probability Haar once per
unoriented inversion orbit. Leave just the common global gauge unfixed. No
Faddeev–Popov factor on this slice, including with the inversion convention.
(Measures used at finite regulators only.) -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace YM.PertExtension.Orb
open Set Function MeasureTheory Wilson Lattice Filter
open scoped Topology Matrix.Norms.Frobenius NNReal ENNReal BigOperators Classical

private def haar (G : Gauge)(I : Type) [Fintype I] := Measure.pi fun _ : I=>G.probHaar
local notation "Haar" => haar
private instance (G : Gauge)(I : Type)[Fintype I]:IsProbabilityMeasure (Haar G I) := by unfold haar;infer_instance

section Split
variable {I K : Type*} [Fintype I] [MeasurableSpace K]
variable (μ : Measure K)[SigmaFinite μ](p : I→Prop)
local notation "L" => {x:I//p x}
local notation "M" => {x:I//¬p x}
local notation "π₁" => (Measure.pi fun _ : L=>μ)
local notation "π₂" => (Measure.pi fun _ : M=>μ)
private def assembly (x : (L → K) × (M → K)) (e : I) := if h:p e then x.1 ⟨e,h⟩ else x.2 ⟨e,h⟩
private lemma assembly_meas : Measurable (assembly (K:=K) p) := by
  apply measurable_pi_lambda; intro e; unfold assembly;split<;>fun_prop
private lemma assembly_map : MeasurePreserving (assembly p) ((π₁).prod π₂) (Measure.pi fun _ : I=>μ) := by
  have hf := assembly_meas (K:=K) p
  refine ⟨hf,Eq.symm ?_⟩; apply Measure.pi_eq; intro t ht
  rw [Measure.map_apply hf (MeasurableSet.univ_pi ht)]
  have he : assembly p ⁻¹' (Set.pi univ t) = (Set.pi univ (fun i:L=>t i)) ×ˢ ((Set.pi univ (fun i:M=>t i))) := by
    ext ⟨x,y⟩
    simp only [Set.mem_prod, Set.mem_pi,mem_preimage,mem_univ,true_implies]
    exact ⟨fun h=>⟨fun i=> by simpa only [assembly,dif_pos i.property] using h (↑i),fun i=> by simpa only [assembly,dif_neg i.property] using h (↑i)⟩,
      fun ⟨h1,h2⟩ i=>by unfold assembly;split
                        next h=>exact h1 ⟨i,h⟩
                        next h=>exact h2 ⟨i,h⟩⟩
  rw [he,Measure.prod_prod,Measure.pi_pi,Measure.pi_pi]; exact Fintype.prod_subtype_mul_prod_subtype p (fun i=>μ (t i))

omit [MeasurableSpace K] μ in
@[fun_prop] private lemma assembly_cont [TopologicalSpace K] : Continuous (assembly (K:=K) p) := by apply continuous_pi; intro e; unfold assembly; split <;> fun_prop
end Split

section GaugeEliminate
variable (G : Gauge){n : Side}

@[fun_prop] private lemma split_cont : Continuous (fun x : (Trees n → G.El) × (Cotree n → G.El)=>splitLink x.1 x.2) := by
  apply continuous_pi;intro i; unfold splitLink;split <;> fun_prop
private lemma split_map : MeasurePreserving (fun x=>(splitLink x.1 x.2)) ((haar G (Trees n)).prod (haar G (Cotree n))) (haar G (OEdge n)) := by
  exact assembly_map G.probHaar (Branch (n:=n))

@[fun_prop] lemma lift_cont : Continuous (liftLinks (K:=G.El) (n:=n)) := by
  apply continuous_pi; intro i; unfold liftLinks;split<;>fun_prop
@[fun_prop] lemma fresh_cont (b : Trees n→G.El) : Continuous (fresh b) := by apply continuous_pi; intro i; unfold fresh; fun_prop
@[fun_prop] lemma fresh_meas (b : Trees n→G.El) : Measurable (fresh b) := by apply measurable_pi_lambda; intro i; unfold fresh; fun_prop
lemma rotated (b : Trees n → G.El): MeasurePreserving (fresh b) (Haar G (Cotree n)) (Haar G (Cotree n)) :=
    measurePreserving_pi _ _ (fun i=> (measurePreserving_mul_right _ _).comp (measurePreserving_mul_left _ _))

lemma average_eq {V : Type*}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
    (O : Config G n → V)(h : Continuous O) (he : Even n.val)
    (hu : ∀ t : Site n → G.El, (∀ x,t (-x)=t x) → ∀ u, O (gauge t u) = O u) :
    (∫ u,O (liftLinks u) ∂Haar G (OEdge n)) = ∫ v,O (links (fun _=>1) v) ∂Haar G (Cotree n) := by
  let f := fun x : ((Trees n→G.El)×(Cotree n→G.El))=>O (links x.1 x.2);let F:=fun v=>O (links (fun _=>1) v)
  have hf : Continuous f:=(h.comp (lift_cont G)).comp (split_cont G)
  have h0 : Continuous F:=show Continuous (f ∘ (fun v : Cotree n→G.El => (1,v))) from hf.comp (continuous_const.prodMk continuous_id)
  let m:=(Haar G (Trees n)).prod (Haar G (Cotree n))
  calc
    (∫ u,O (liftLinks u) ∂Haar G (OEdge n))=∫ x, f x ∂m := by
      rw [← MeasurePreserving.map_eq (split_map G (n:=n))]
      exact integral_map ((assembly_meas Branch).aemeasurable) ((h.comp (lift_cont G)).aestronglyMeasurable)
    _ = ∫ b,∫ u, f (b,u) ∂Haar G (Cotree n) ∂Haar G (Trees n) := integral_prod _ (hf.integrable_of_hasCompactSupport <| .of_compactSpace f)
    _ = ∫ _,∫ u, F u ∂Haar G (Cotree n) ∂Haar G (Trees n) := by
      apply integral_congr_ae (Eventually.of_forall ?_); intro b
      have heq u : f (b,u)=F (fresh b u):=(hu _ (frame_neg b) (links b u)).symm.trans (congr_arg O (alignment he ..))
      simp_rw [heq]; nth_rw 2 [← (rotated G b).map_eq];exact (integral_map ((fresh_meas G b).aemeasurable) h0.aestronglyMeasurable).symm
    _ = ∫ v,O (links (fun _=>1) v) ∂Haar G (Cotree n) := by simp [F]
end GaugeEliminate
end YM.PertExtension.Orb
