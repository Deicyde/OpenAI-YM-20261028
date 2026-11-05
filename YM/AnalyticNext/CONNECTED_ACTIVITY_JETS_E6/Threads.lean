import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Ford
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood

/-!
# Normalized tags, products
No meas space imposed on tags. F decomposition reads physical ar. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {Ω κ ι : Type} [Fintype ι]

namespace Pond
section
variable [MeasurableSpace Ω] [Nonempty Ω] (μ : ι → Measure Ω) [hμ : ∀ i, IsProbabilityMeasure (μ i)]
variable (S : Finset κ) (Z : κ → Finset ι)
private def snatch (X : Finset ι) (z : ι→Ω) := fun i:↥X=> z i.val
private def replenish (X : Finset ι) (z : ↥X→Ω) := fun i:ι=> if h : i∈X then z ⟨i,h⟩ else Classical.arbitrary _
omit [Fintype ι] [MeasurableSpace Ω] in
private lemma returns (X : Finset ι) (z : ↥X→Ω) : snatch X (replenish X z)=z := by ext j; simp [snatch,replenish]
omit [Fintype ι] [Nonempty Ω] in
private lemma nmeas (X : Finset ι) : Measurable (snatch (Ω:=Ω) X) := by unfold snatch; fun_prop
omit [Fintype ι] in
private lemma rmeas (X : Finset ι) : Measurable (replenish (Ω:=Ω) X) := by
  apply measurable_pi_lambda; intro i; unfold replenish; split_ifs
  · fun_prop
  exact measurable_const
include μ
omit [Nonempty Ω] in
private lemma caught (X : Finset ι) : MeasurePreserving (snatch X) (Measure.pi μ)
    (Measure.pi (fun i=> μ i.val)) := by convert! measurePreserving_fst.comp (measurePreserving_piEquivPiSubtypeProd μ (fun i=>i∈X))
omit [Nonempty Ω] in
private lemma slide (X Y : Finset ι) (h : Disjoint X Y) : MeasurePreserving (fun z : ι→Ω=> (snatch X z,snatch Y z))
    (Measure.pi μ) ((Measure.pi (fun i : ↥X=> μ i.val)).prod (Measure.pi (fun i : ↥Y=> μ i.val))) := by
  have hg : IndepFun (snatch (Ω:=Ω) X) (snatch Y) (Measure.pi μ) :=
    (iIndepFun_pi (μ:=μ) (X:=fun _ z=>z) (fun i=> aemeasurable_id)).indepFun_finset X Y h (fun i=> measurable_pi_apply _)
  have hp := IndepFun.map_prod_eq_prod_map_map (nmeas X).aemeasurable (nmeas Y).aemeasurable hg
  rw [(caught μ X).map_eq, (caught μ Y).map_eq] at hp; exact ⟨(nmeas X).prodMk (nmeas Y),hp⟩

lemma marched (h : (S:Set κ).PairwiseDisjoint Z) (f : κ → (ι→Ω) → ℝ) (hf : ∀ i∈S, Measurable (f i))
    (hg : ∀ i∈S,∀ x y, (∀ j∈Z i,x j=y j) → f i x=f i y) :
    (∫ u, ∏ i∈S,f i u ∂Measure.pi μ)= ∏ i∈S, ∫ u, f i u ∂Measure.pi μ := by
  suffices H : ∀ V : Finset κ, V⊆ S → (∫ u, ∏ i∈V,f i u ∂Measure.pi μ)= ∏ i∈V, ∫ u,f i u ∂Measure.pi μ by
    exact H S (Finset.Subset.refl _)
  intro V; induction V using Finset.induction_on with
  | empty => intro; simp
  | @insert i v hi ih =>
    intro hx
    have hu := (subset_insert i v).trans hx; have hs : i∈ S := hx (mem_insert_self ..)
    let Y := v.biUnion Z
    simp_rw [prod_insert hi]; rw [← ih hu]; refine indexed_prod (caught μ (Z i)) (caught μ Y) (slide μ _ _ ?_) (replenish _) (replenish _)
      (rmeas _) (rmeas _) (returns _) (returns _) (f:=f i) ?_ (g:=fun x=> ∏ j∈v,f j x) ?_
      (hf _ hs) (Finset.measurable_fun_prod _ fun j hj=> hf _ (hu hj))
    · refine Finset.disjoint_left.mpr fun z hz ha=> ?_
      obtain ⟨j,hj,ha⟩ := mem_biUnion.mp ha
      exact Finset.disjoint_left.mp (h hs (hu hj) fun H=>hi (H.symm ▸ hj)) hz ha
    · exact fun x y hH=> hg _ hs x y fun j hj=> congr_fun hH ⟨j,hj⟩
    exact fun x y hH=> prod_congr rfl fun j hj => hg _ (hu hj) x y fun i hk=> congr_fun hH ⟨i, mem_biUnion.mpr ⟨j,hj,hk⟩⟩
end

section
variable [Fintype Ω] [Nonempty Ω]

def likely {ι : Type} [Fintype ι] (z : ι→ℝ) := (Fintype.card ι:ℝ)⁻¹*∑ i, z i

private lemma choice_kernel (X : Finset ι) (f g : (ι→Ω)→ℝ)
    (hf : ∀ (u v : ι→Ω), (∀ i∈X,u i=v i) → f u=f v)
    (hg : ∀ (u v : ι→Ω), (∀ i,i∉X→ u i=v i) → g u=g v) :
    likely (fun u=> f u*g u)=likely f*likely g := by
  let e:=Equiv.piEquivPiSubtypeProd (fun i=> i∈X) (fun _=> Ω)
  let F:= fun u=> f (e.symm (u,fun _=> Classical.arbitrary _)); let G:= fun v=> g (e.symm ((fun _=>Classical.arbitrary _),v))
  have he i j : f (e.symm (i,j))=F i := hf _ _ fun a ha => by
    change ((if h:a∈X then i _ else _))=(if h:a∈X then i _ else _); rw [dif_pos ha, dif_pos ha]
  have hh i j : g (e.symm (i,j))=G j := hg _ _ fun a ha=> by
    change ((if h:a∈X then _ else j _))=(if h:a∈X then _ else j _); rw [dif_neg ha,dif_neg ha]
  let A := ↥X→Ω; let B := (Subtype fun i => i∉X)→Ω
  have hp : (Fintype.card (ι→Ω):ℝ)= Fintype.card A * (Fintype.card B:ℝ) := by rw [Fintype.card_congr e,Fintype.card_prod]; norm_cast
  have hv (z : (ι→Ω)→ℝ) : ∑ u,z u= ∑ i : A,∑ j : B,z (e.symm (i,j)) := by rw [← Equiv.sum_comp e.symm z,Fintype.sum_prod_type]
  have hb : (Fintype.card B:ℝ) ≠ 0 := by unfold B; positivity
  have ha : (Fintype.card A:ℝ) ≠ 0 := by unfold A; positivity
  unfold likely; simp_rw [hp,hv]; simp_rw [he,hh,← Finset.mul_sum,sum_const,card_univ,nsmul_eq_mul,← Finset.sum_mul,← Finset.mul_sum]
  field_simp

lemma jurisdictions (S : Finset κ) (X : κ → Finset ι) (h : (S:Set κ).PairwiseDisjoint X) (f : κ → (ι→Ω) → ℝ)
    (he : ∀ i∈S,∀ x y,(∀ j∈X i,x j=y j) → f i x=f i y) : likely (fun x=> ∏ i∈S,f i x) =∏ i∈S,likely (f i) := by
  induction S using Finset.induction_on with
  | empty => simp [likely]
  | @insert i v hi ih =>
    simp_rw [prod_insert hi]; rw [← ih (h.subset (subset_insert ..)) (fun i hh => he i ((subset_insert ..) hh))]
    refine choice_kernel (X i) _ _ (he i (mem_insert_self ..)) ?_
    exact fun x y hH=> prod_congr rfl fun j hj=> he _ ((subset_insert ..) hj) x y fun a ha=> hH a (fun hx=> Finset.disjoint_left.mp
      (h (mem_insert_self ..) ((subset_insert ..) hj) fun H=>hi (H.symm ▸ hj)) hx ha)
end
end Pond
end YM.ConnectedActivityE6
