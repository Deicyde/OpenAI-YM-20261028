import YM.UVExtension.Free.Rows
import YM.Next.FREE_KERNELS.Hall
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Free
open Function Filter Lattice Laurent Bloch Matrix Next.Free Precision Craft
open scoped Topology BigOperators Classical

variable {α : Type} [Fintype α]

-- real orbits
lemma positive_root {T : Row α α} {x V : ℝ} (hx : 0 ≤ x) (ht : Funds T x V) (h : Whole T) (n : Side) :
    (T.acts n).PosSemidef := by
  obtain ⟨he,hb⟩ := obey_band T h ht n
  refine posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun i=>?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact he
  simp only [star_trivial]; apply (mul_nonneg hx ?_).trans ((hb i).1)
  unfold dotProduct; apply Finset.sum_nonneg; intro j _; rw [← sq]; positivity

variable {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
lemma limited_pos {S : ℕ → Matrix E E ℝ} {p : Matrix E E ℝ} (h : Tendsto S atTop (𝓝 p))
    (hp : ∀ᶠ n in atTop,(S n).PosSemidef) : p.PosSemidef := by
  have h1 : Tendsto (fun i=> (S i)ᵀ) atTop (𝓝 pᵀ) := by
    apply tendsto_pi_nhds.mpr; intro i; exact tendsto_pi_nhds.mpr fun j=>tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h _) _
  have hθ := tendsto_nhds_unique (h1.congr' (hp.mono fun i h=>
    (conjTranspose_eq_transpose_of_trivial ..).symm.trans h.1)) h
  refine posSemidef_iff_dotProduct_mulVec.mpr ⟨(conjTranspose_eq_transpose_of_trivial ..).trans hθ,fun v=>?_⟩
  have hm : Tendsto (fun n=> dotProduct (star v) ((S n) *ᵥ v)) atTop (𝓝 (dotProduct (star v) (p *ᵥ v))) := by
    unfold dotProduct
    refine tendsto_finsetSum _ fun i hi=> Tendsto.const_mul _ ?_
    refine tendsto_finsetSum _ fun j _=> (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) j).mul_const _
  exact ge_of_tendsto hm (hp.mono fun i h=> h.dotProduct_mulVec_nonneg _)

open scoped MatrixOrder in
lemma root_unique {p q : Matrix E E ℝ} (h : p.PosSemidef) (hp : q.PosSemidef) (ht : p*p=q*q) : p=q :=
  calc
    p = CFC.sqrt (p*p) := (CFC.sqrt_mul_self _ h.nonneg).symm
    _ = _ := (congr_arg CFC.sqrt ht).trans (CFC.sqrt_mul_self _ hp.nonneg)

lemma square_limit {A : ℕ→Row α α} {η C : ℝ} (hη : 0<η)
    (h : ∀ᶠ i in atTop,(A i).strip η C ∧ ∀ n, ((A i).acts n).PosSemidef)
    (hp : ∀ n, Arrives (fun i=> ((A i).acts n)ᵀ*(A i).acts n)) : ∃ W, Received A W η C := by
  refine row_all (h.mono fun i hi=>hi.1) ?_; intro f g hf hg T U ht hu
  apply bank_injective (Whole.safe ⟨_,_,hη,ht.bound⟩) (Whole.safe ⟨_,_,hη,hu.bound⟩); intro L
  obtain ⟨z,hZ⟩ := hp L
  have he (g W) (hg: Tendsto g atTop atTop) (ht: Received (A ∘ g) W η C): (W.acts L).PosSemidef ∧ W.acts L*W.acts L=z := by
    have hp := hg.eventually h; have hk := (hp.mono fun i hi=>hi.2 L)
    have hx := acts_limit ht (hp.mono fun i hi=>hi.1) hη L
    refine ⟨limited_pos hx hk,?_⟩
    refine tendsto_nhds_unique ((hx.mul hx).congr' ?_) (hZ.comp hg)
    exact hk.mono fun i hi=> congr_arg (·*(A (g i)).acts L) (hi.1.symm.trans (conjTranspose_eq_transpose_of_trivial ..))
  obtain ⟨ht,H⟩ := he f T hf.tendsto_atTop ht; obtain ⟨hu,Q⟩ := he g U hg.tendsto_atTop hu
  exact root_unique ht hu (H.trans Q.symm)
end YM.UVExtension.Free
