import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Outcomes
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Windows

/-! Produce the local Y- and tag-dependent centers at the *same*
endpoint prescription, exact on Flags after authorization & gap purchases. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace Wires
open Schur Completion Geo
variable {G : Gauge} {c f : Side} {S : StepData c f} {A A' : Stores S} {F F' : Forest S.ratio}
    (T : Tube G S) (x : ℝ) (q : Chi) (d : ℝ) {V V' : Config G c} {k k' : S.Choices}

abbrev finger (A : Stores S) (F : Forest S.ratio) : (Rows.In (G:=G) x A F ⊕ vacant A F x G) ≃ Full G f := sorted A F
abbrev active (A : Stores S) (F : Forest S.ratio) (i : Rows.In (G:=G) x A F) := finger x A F (.inl i)

def debts (k : S.Choices) (V : Config G c) (Y : Config G f) (A : Stores S) (F : Forest S.ratio) : Gaussian.Vec (Full G f) := fun i =>
    if Physical.openBond A F x i.1 then ∑ j : Receipt G S, clueX T k V x i j * sources T x q d V k A F Y j else 0

lemma debt (hA : Map.Aperture S T x) {M} (ha : Authorized A V F x M) (Y : Config G f) (i : Rows.In (G:=G) x A F) :
    debts T x q d k V Y A F (active x A F i)=blame T x V k (shots S x) A F q d (iced Y A x F) i := by
  let e := active x A F i
  have hp : Physical.openBond A F x e.1 := ⟨i.1,rfl⟩
  unfold debts; rw [if_pos hp,sources_align T x q d hA k V Y A F ha]
  unfold blame mulVec dotProduct; apply Finset.sum_congr rfl; intro j _
  change _ = Rows.move T x V k (shots S x) A F j i*_
  rw [clueX_align T V k hA ha _ hp, Physical.to_clue _ _ _ _ _ hA.branched]

/-- Padded centers. Restrict them to Active before any application to
cloud variables, hard U, arrears, etc. -/
def outlook (k : S.Choices) (V : Config G c) (Y : Config G f) (A : Stores S) (F : Forest S.ratio) : Directions G f :=
    tape (-(perX T x k V A F).transpose *ᵥ debts T x q d k V Y A F)

lemma station (hA : Map.Aperture S T x) {M η} (h : Authorized A V F x M) (hη : 0<η)
    (hp : Gapped (Rows.gram T x V k (shots S x) A F) η) (Y : Config G f) (i : Rows.In (G:=G) x A F) :
    outlook T x q d k V Y A F (active x A F i).1 (active x A F i).2=
    meanLog A F T x V k q d (iced Y A x F) i := by
  let e : (_ ⊕ _) ≃ Full G f := finger (G:=G) x A F
  unfold outlook meanLog
  rw [perX_exact _ _ hA _ _ _ _ h hη hp]
  change (-(wide _ _ |>.submatrix (e.symm) (e.symm)).transpose *ᵥ _) (e (.inl i)) = _
  unfold mulVec dotProduct
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  have h₁ (j : Rows.In (G:=G) x A F) : e (.inl j) = active x A F j := rfl
  have h₂ (j : Full G f) := e.apply_symm_apply j
  simp only [Matrix.neg_apply,Matrix.transpose_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  simp only [wide, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₂₁,h₁,debt T x q d hA h, Matrix.zero_apply,
    neg_zero,zero_mul,Finset.sum_const_zero,add_zero]

theorem debts_meas (k : S.Choices) (A : Stores S) (F : Forest S.ratio) {P : Teller G} (h : P.Funds S T)
    (hd : 0<d) (hr : 2*d<firstRadius G) (i : Full G f) :
    Measurable (fun p : Config G c × Config G f => debts T x q d k p.1 p.2 A F i) := by
  unfold debts; split
  next hi =>
    refine Finset.measurable_fun_sum _ (fun j _=>?_)
    have hm : Measurable (fun p : Config G c × Config G f => clueX T k p.1 x i j) := (clueX_meas _ k x i j (funds_branch h)).comp measurable_fst
    exact hm.mul (sources_meas _ _ _ _ _ _ _ h hd hr j)
  exact measurable_const

theorem herald {P : Teller G} (h : P.Funds S T) (k : S.Choices) (A : Stores S) (F : Forest S.ratio)
    (hd : 0<d) (hr : 2*d<firstRadius G) : Measurable (fun p : Config G c × Config G f => outlook T x q d k p.1 p.2 A F) := by
  apply tape.measurable.comp
  change Measurable (fun p : Config G c × Config G f => -(perX T x k p.1 A F).transpose *ᵥ debts T x q d k p.1 p.2 A F)
  unfold mulVec dotProduct; refine measurable_pi_lambda _ fun i=>?_ ; simp only [Matrix.neg_apply,Matrix.transpose_apply]
  refine Finset.measurable_fun_sum _ fun j _=>?_
  have ht : Measurable (fun p : Config G c × Config G f=>perX T x k p.1 A F j i) := (perX_meas _ x _ _ _ (funds_branch h) j i).comp measurable_fst
  exact ht.neg.mul (debts_meas _ _ _ _ _ _ _ h hd hr j)

lemma debt_region {X : Support c} (h : Physical.Reads X A A' F F' V V' k k') (hA : Map.Aperture S T x)
    (i : Full G f) (hp : Shields X (Physical.place S i) (17*radiusB x))
    {Y Y' : Config G f} (he : Geo.Yreads S X Y Y') :
    debts T x q d k V Y A F i=debts T x q d k' V' Y' A' F' i := by
  have ht := hA.spans; have hB := hA.scale
  unfold debts; rw [h.frozen_bits hB _ (hp.shrink (by omega))]; split
  · refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hz : separation (spot S j.1) (Physical.place S i) ≤ Next.SectorChange.span S.patch x
    · have hM : Shields X (spot S j.1) (16*radiusB x) := hp.shift (by rw [separation_comm]; omega)
      rw [clueX_scoped T hA h _ _ (hM.shrink (by omega)),sources_read T x q d h hA _ hM he]
    rw [Wires.outside T k V i j hA hz,Wires.outside T k' V' i j hA hz]; simp
  rfl

lemma beam_bias {X : Support c} (h : Physical.Reads X A A' F F' V V' k k') (hA : Map.Aperture S T x)
    (i : Bond f) (hp : Shields X (portOf S i) (18*radiusB x))
    {Y Y' : Config G f} (he : Geo.Yreads S X Y Y') :
    outlook T x q d k V Y A F i=outlook T x q d k' V' Y' A' F' i := by
  apply PiLp.ext; intro j
  unfold outlook
  have hv : Shields X (Physical.place S (i,j)) (18*radiusB x) := hp
  change (-(Schur.per (Physical.windows S x) _).transpose *ᵥ _) (i,j)=( -(Schur.per _ _).transpose *ᵥ _) (i,j)
  simp only [mulVec,dotProduct,Matrix.neg_apply,Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun a ha => ?_
  by_cases h0 : a∈Physical.windows S x (i,j)
  change -(perX T x k V A F a (i,j))*_ = -(perX T x k' V' A' F' a (i,j))*_
  · rw [perX_read T x hA h (i,j) a (hv.shrink (by omega)), debt_region T x q d h hA _ (hv.shift ?_) he]
    have hh := Physical.contained _ _ h0; omega
  rw [Schur.per_zero (Physical.windows S x) _ h0,Schur.per_zero (Physical.windows S x) _ h0]; simp
end Wires
end YM.PhysicalNext.Dictionary
