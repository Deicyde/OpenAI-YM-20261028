import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pond

/-!
# Frobenius Cylinder bills. same marginal on overlapping endpoints
Use with independently spaced Supports; even if empty sets,
subdivisions can't pay repeatedly. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel  Footprint Raw ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {Ω E F : Type*}

def confined (t : Ω → E) (f : Ω → ℝ) := ∀ u v, t u=t v → f u=f v

namespace Pond
section prod
variable [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
variable {μ : Measure Ω} {ν : Measure E} {σ : Measure F} {m : Ω→E} {n : Ω→F} {f g : Ω→ℝ}

lemma reception (he : MeasurePreserving m μ ν) (f : E→ℝ) (hf : Measurable f) :
    (∫ u,f (m u) ∂μ)=∫ e,f e ∂ν := by rw [← he.map_eq, integral_map he.measurable.aemeasurable hf.aestronglyMeasurable]

lemma gathered (l : E→Ω) (h : Measurable l) (he : MeasurePreserving m μ ν) (hx : RightInverse l m)
    (hg : confined m f) (hf : Measurable f) : (∫ u,f u ∂μ) =∫ i,f (l i) ∂ν := by
  have hv u : f u=(f ∘ l) (m u) := hg u _ (hx _).symm
  refine (integral_congr_ae (ae_of_all μ hv)).trans (reception he _ (hf.comp h))

lemma indexed_prod [SFinite ν] [SFinite σ] (hl : MeasurePreserving m μ ν) (hk : MeasurePreserving n μ σ)
    (he : MeasurePreserving (fun u=> (m u,n u)) μ (ν.prod σ)) (q : E→Ω) (r : F→Ω)
    (hq : Measurable q) (hr : Measurable r) (hq' : RightInverse q m) (hr' : RightInverse r n)
    (h : confined m f) (hp : confined n g) (hf : Measurable f) (hg : Measurable g) :
    (∫ u,f u*g u ∂μ)=(∫ u,f u ∂μ)*∫ u,g u ∂μ := by
  let a (s : E × F) := f (q s.1)*g (r s.2)
  have ha u : f u*g u=a (m u,n u) := congr_arg₂ (·*·) (h u _ (hq' _).symm) (hp u _ (hr' _).symm)
  have he' : (∫ i,f i*g i ∂μ)=∫ s, a s ∂ν.prod σ :=
    (integral_congr_ae (ae_of_all μ ha)).trans (reception he _ (((hf.comp hq).comp measurable_fst).mul
      ((hg.comp hr).comp measurable_snd)))
  rw [he',gathered q hq hl hq' h hf,gathered r hr hk hr' hp hg]; exact integral_prod_mul (μ:=ν) (ν:=σ) (f ∘ q) (g ∘ r)
end prod
section parts
variable {ι κ : Type} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ]

end parts

section fish
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
lemma observe {u v : Body ι} (Z : Finset ι) : swim Z u=swim Z v ↔ ∀ p∈Z,u p=v p :=
    ⟨fun h i hi=> congr_arg (fun a:Body (↥Z)=> a ⟨i,hi⟩) h,fun h=> by ext j; exact h j.val j.2⟩

lemma island {A : Matrix ι ι ℝ} (h : A.PosSemidef) {κ : Type} (S : Finset κ) (Z : κ→ Finset ι)
    (hx : ∀ i∈ S,∀ j∈S,i≠j→∀ a∈Z i,∀ b∈ Z j,A a b=0)
    (f : κ → Body ι→ℝ) (hf : ∀ i∈S, Measurable (f i))
    (hp : ∀ i∈S,confined (swim (Z i)) (f i)) :
    (∫ u,∏ i∈S,f i u ∂sweep A)=∏ i∈S,∫ u,f i u ∂sweep A := by
  -- pairwise collection via Induction; don't assume arbitrary sub-coordinates of single island independent
  suffices hh : ∀ p : Finset κ, p⊆S → (∫ u, ∏ i∈p,f i u ∂sweep A)=∏ i∈p,∫ u,f i u ∂sweep A by exact hh _ (Finset.Subset.refl _)
  intro p; induction p using Finset.induction_on with
  | empty => intro; simp
  | @insert i p hi ih =>
    intro hv; have hs : i∈S := hv (mem_insert_self ..)
    have ht : p⊆S := Finset.Subset.trans (subset_insert ..) hv
    let Y := p.biUnion Z; let g u := ∏ i∈p, f i u
    simp_rw [prod_insert hi]; rw [← ih ht]
    refine indexed_prod (orbit h (Z i)) (orbit h Y) (subdivision h _ _ ?_)
      (spill (Z i)) (spill Y) (spill_m _) (spill_m _) (settled _) (settled _) (hp i hs) (g:=g) ?_
      (hf i hs) (Finset.measurable_fun_prod p fun i hp=> hf i (ht hp))
    · intro a ha b hb; obtain ⟨j,hj,hb⟩ := mem_biUnion.mp hb
      exact hx i hs j (ht hj) (fun h=> hi (h.symm ▸ hj)) a ha b hb
    intro u v he; exact prod_congr rfl fun j hj=> hp _ (ht hj) u v ((observe _).2 (fun i hk=> (observe _).1 he i (mem_biUnion.mpr ⟨j,hj,hk⟩)))
end fish
end Pond
end YM.ConnectedActivityE6
