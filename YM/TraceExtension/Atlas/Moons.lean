import YM.TraceExtension.Atlas.Chalk
import YM.Work.A05
import YM.Work.A15
import Mathlib.Topology.Baire.LocallyCompactRegular
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Set Filter Analysis Table
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
open MeasureTheory Measure
lemma point_uniform {I V:Type*}[Group I][TopologicalSpace I][IsTopologicalGroup I][CompactSpace I][T2Space I][NormedRing V]
    (f:ℕ→ I→* V)(hv:∀ i,Continuous (f i))(g:I→V)(h:∀ x,Tendsto (fun i=> f i x) atTop (𝓝 (g x))) : ∃ C:ℝ, ∀ i x, ‖f i x‖ ≤ C:=by
    classical
    let A (k:ℕ):= ⋂ i:ℕ,{x:I| ‖f i x‖ ≤ (k:ℝ)}
    have he:BaireSpace I:=inferInstance; have hX(x:I): ∃ k:ℕ,x∈A k:=by
        obtain ⟨v,hv⟩:= (h x).norm.bddAbove_range
        exact ⟨⌈v⌉₊, mem_iInter.mpr (fun i=> le_trans (hv (mem_range_self i)) (Nat.le_ceil v))⟩
    obtain ⟨d,t,ht⟩:= nonempty_interior_of_iUnion_of_closed (f:=A) (fun i=> isClosed_iInter (fun i=> isClosed_le (hv i).norm continuous_const)) (Set.eq_univ_of_forall (fun x=> mem_iUnion.mpr (hX x)))
    let X(x:I):= (fun y=>t*x⁻¹*y) ⁻¹' interior (A d)
    obtain ⟨S,hS⟩:= isCompact_univ.elim_finite_subcover X (fun x=> isOpen_interior.preimage (continuous_const.mul continuous_id)) (Set.univ_subset_iff.mpr (Set.eq_univ_of_forall (fun i=> mem_iUnion.mpr ⟨i,show i∈X i from by simp [X,mul_assoc,ht]⟩)))
    let C:= S.sup (fun x=> (hX (t*x⁻¹)⁻¹).choose)
    refine ⟨C*(d:ℝ),fun i x=>?_⟩
    obtain ⟨p,hp,hk⟩:= Set.mem_iUnion₂.mp (hS (mem_univ x))
    let z:=t*p⁻¹
    have hi:z*x∈A d:=interior_subset hk
    have hA : ‖f i z⁻¹‖ ≤ (C:ℝ):= le_trans (show ‖_‖ ≤ ((hX z⁻¹).choose:ℝ) from Set.mem_iInter.mp (hX z⁻¹).choose_spec i) (by exact_mod_cast Finset.le_sup (s:=S) (f:=fun v=> (hX (t*v⁻¹)⁻¹).choose) hp)
    calc ‖f i x‖ = ‖f i z⁻¹ * f i (z*x)‖:=by rw[← map_mul,inv_mul_cancel_left]
         _ ≤ _:= (norm_mul_le ..).trans (mul_le_mul hA (Set.mem_iInter.mp hi i) (norm_nonneg _) (Nat.cast_nonneg _))

attribute [local instance] Work.A15.compact_ortho
local instance : MeasurableSpace Ortho := borel Ortho
local instance : BorelSpace Ortho := ⟨rfl⟩
local instance : SecondCountableTopology Ortho:=by
   haveI : SecondCountableTopology M4:= inferInstanceAs (SecondCountableTopology (Axis → Axis → ℝ))
   exact inferInstanceAs (SecondCountableTopology ↥((Matrix.unitaryGroup Axis ℝ:Set M4)))
def allO : TopologicalSpace.PositiveCompacts Ortho:=⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
def μO:= Measure.haarMeasure allO
instance : μO.IsHaarMeasure:=by unfold μO; infer_instance
instance : IsProbabilityMeasure μO:=⟨@Measure.haarMeasure_self Ortho _ _ _ _ _ allO⟩

section
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][NormedSpace ℝ E][IsScalarTower ℝ ℂ E][CompleteSpace E]
local notation "V0"=> (E →L[ℂ] E)
def meanO (f g:Ortho→* (E→L[ℂ] E)) : V0:=∫ x,f x*g x⁻¹ ∂μO
lemma underO (f g:Ortho→* (E→L[ℂ] E))(hf:Continuous f)(hg:Continuous g) (v:Ortho): f v*meanO f g=meanO f g*g v:=by
   let k(x:Ortho):= f x*g x⁻¹
   have ht:Continuous k:= hf.mul (hg.comp continuous_inv)
   have hh: Integrable k μO:= ht.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   let P:= (ContinuousLinearMap.mul ℂ V0|>.flip) (g v); let Q:= ContinuousLinearMap.mul ℂ V0 (f v)
   have he: Q (meanO f g)=∫ x,f v*k x ∂μO:= (Q.integral_comp_comm hh).symm
   change Q (meanO f g)=P (meanO f g); rw[he]; rw [show P (meanO f g)=_ from (P.integral_comp_comm hh).symm]; conv_rhs => rw [← integral_mul_left_eq_self (fun i=> P (k i)) v]
   apply integral_congr_ae; filter_upwards with x; change f v*k x=k (v*x)*g v; unfold k
   rw [← mul_assoc,map_mul, mul_assoc _ (g _) (g v), ← map_mul, mul_inv_rev, ← map_mul, mul_assoc,inv_mul_cancel,mul_one]
lemma meanO_value(f g:Ortho→* (E→L[ℂ] E))(hf:Continuous f)(hg:Continuous g)(v:E): meanO f g v=∫ x,(f x*g x⁻¹) v∂μO:= ((ContinuousLinearMap.apply ℂ E v).integral_comp_comm ((hf.mul (hg.comp continuous_inv)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm

lemma eventualMeanO(f:ℕ→Ortho→* V0) (hf:∀ i,Continuous (f i))(g:Ortho→* V0)(hg:Continuous g)(ht:∀ x,Tendsto (fun i=> f i x) atTop (𝓝 (g x))): Tendsto (fun i=> meanO (f i) g) atTop (𝓝 (1: V0)):=by
   have he:∀ x:Ortho,g x*g x⁻¹=1:=fun x=>by rw [← map_mul,mul_inv_cancel,map_one]
   have hv:(1:V0)=meanO g g:=by simp [meanO,he]
   obtain ⟨c,hc⟩:= point_uniform f hf g ht
   rw [hv]; unfold meanO; let U(x:Ortho):= c*‖g x⁻¹‖
   apply tendsto_integral_of_dominated_convergence U
   · intro i; exact ((hf i).mul (hg.comp continuous_inv)).aestronglyMeasurable
   · exact (continuous_const.mul (hg.comp continuous_inv|>.norm)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   · exact fun i=> ae_of_all _ fun x=> (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (hc ..) (norm_nonneg _))
   exact ae_of_all _ fun x=> (ht x).mul_const _
end
end YM.Trace.Pilot
