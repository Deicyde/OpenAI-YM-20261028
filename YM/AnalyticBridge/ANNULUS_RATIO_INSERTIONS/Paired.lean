import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.PriceLine
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay

/-!
# Present uniform costs for these specific matrices

Even identity completion logs, both gauges with same k and F. This
pre/post station quotes only for fsct LOCAL term and associated Gram
certificates, not the whole determinant proof. Can buy them at each
post-L with the charts before pricing other activity estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.FS
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented 
open Tier Wisps Schur LocalJet Completion SectorNext.Vacuum Panel Unitary
   
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure

variable {G : Gauge} {c f : Side} {S : StepData c f}

section linear
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {A : Gaussian.Table α} {p : α → Site c} {η C v : ℝ}

lemma fronts (h : Gapped A η) (hf : Pours A p p v C) (he : 0 ≤ v) (hm : A.PosDef) :
    let M := wide A (1:Gaussian.Table β)
    M.IsHermitian ∧ Numeric M (min η 1) (C+1) := by
  intro M
  obtain ⟨ht,hx⟩ := wide_gap (β:=β) (Matrix.isHermitian_iff_isSymm.mp hm.isHermitian) h
  have hv (x : α → ℝ) : x ⬝ᵥ (A *ᵥ x) ≤ C*sumSq x := (le_abs_self _).trans ((Schur.estimate
    (hf.weaker he (le_refl C)) x x).trans (by linarith))
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr ht,fun i => ⟨by rw [← sumSq_dot]; exact hx i,?_⟩⟩
  unfold M; rw [Completion.wide_cost,one_mulVec,← sumSq_dot i,sumSq,Fintype.sum_sum_type,← sumSq_dot]
  have h1 := hv (i ∘ Sum.inl)
  have hh := sumSq_nn (i ∘ Sum.inl)
  have h2 := mul_nonneg hf.pos (sumSq_nn (i ∘ Sum.inr))
  change _ ≤ (C+1) * (sumSq (i ∘ Sum.inl)+ sumSq (i ∘ Sum.inr))
  linarith only [h1,hh,h2]
end linear



variable (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (V : Config G c) (k : S.Choices)



/-- Uniform fixed patch cost even on all link-completed panels. E S:ew
interpretation with SC's actual endpoint-pair prescription, not claiming
geometric equivalence with midpoint choices in TeX. `meeting` all-pairs
max distance, radius ≥120 ensures root included. -/
structure Capped (K η : ℝ) : Prop where
  principle : (Rows.gram T x V k (shots S x) A F).PosDef
  spare : (embossed T A F x V k).IsHermitian
  mounts : Numeric (embossed T A F x V k) η K
  panel (i : key (G:=G) A F x) : (Schur.principal (embossed T A F x V k) (allPanels A F i)).PosDef ∧
    i∈allPanels A F i

variable {T A F x V k}
private lemma cap_of {v K η : ℝ} (ht : 120≤radiusB x) (he : 0≤v) (hη : 0<η)
    (h : Pours (Rows.gram T x V k (shots S x) A F) (front A F) (front A F) v K)
    (hf : Gapped (Rows.gram T x V k (shots S x) A F) η)
    (hh : (Rows.gram T x V k (shots S x) A F).PosDef) : Capped T A F x V k (K+1) (min η 1) := by
  let M := embossed T A F x V k
  let U := vacant A F x G
  obtain ⟨hI,hx⟩ : M.IsHermitian ∧ Numeric M (min η 1) (K+1) := by
    convert! fronts (β:=U) hf h he hh using 2 -- allows instance unification
  refine ⟨hh,hI,hx,fun i => ⟨(fits hI hx (lt_min hη (by norm_num)) (allPanels A F i)).2.2,?_⟩⟩
  rw [allPanels,Set.mem_setOf_eq]
  intro y hy z hz
  let p := S.ratio.parent (sorted A F i).1.1
  have hj : separation p y ≤ 1 := meetings _ hy
  have h3 : separation p z ≤ 1 := meetings _ hz
  apply (separation_triangle y p z).trans; rw [separation_comm y]; omega

private lemma uniq {A B : Patch} (h : A.L=B.L) (hj : A.J=B.J) : A=B := by cases A; cases B; congr

def Belongs (P : Teller G) (L : Side) (K η x : ℝ) :=
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x)≤c.val → P.Funds S T →
      ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c),
        A.flags=RG.flags (temp x) V → Capped T A F x V k K η

theorem hail (P : Teller G) (L : Side) :
    ∃ K η, 0<η ∧ η≤K ∧ ∀ᶠ x in atTop, Belongs P L K η x := by
  by_cases he : ∃ S0 : Patch,S0.L=L ∧ S0.J=P.j ∧ S0.Branches P.bind G
  swap
  · exact ⟨1,1,one_pos,le_rfl, Filter.Eventually.of_forall (p:=fun x => Belongs P L 1 1 x) (fun _ _ _ S T hT _ hP =>
      (he ⟨S.patch,hT,hP.atStep,hP.kernel⟩).elim)⟩
  obtain ⟨R,hR,hr,hB⟩ := he
  obtain ⟨u,C,η,k,b,hu,hC,hη,hk,hb,h⟩ := opaqueCost G R P hB
  let E := C+1; let F := min η 1
  refine ⟨E,F,lt_min hη one_pos,(min_le_right _ _).trans (le_add_of_nonneg_left hC),?_⟩
  filter_upwards [h,Work.E01.radiusB_tendsto.eventually_ge_atTop 120] with x h ha
  intro c f S T hL hv hT A A' k' V hD
  obtain ⟨hi,hl,hP,-⟩ := h S T (uniq (hL.trans hR.symm) (hT.atStep.trans hr.symm)) hv hT A A' k' V hD
  exact cap_of ha hu.le hη hi hl hP


end YM.AnalyticBridge.AnnulusRatioInsertions.FS
