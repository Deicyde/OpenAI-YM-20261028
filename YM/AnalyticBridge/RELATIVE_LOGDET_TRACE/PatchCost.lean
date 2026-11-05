import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Currencies
import YM.Push.ABSOLUTE_SUMS.Basic



/-!
# Marked traces: absolute costs for differences

 site hit estimates. Ask the determinant questions returning actual
variation on a finite torus with *no* volume constant in the price of a
local change. For use also by clients making many local edits (flags,
projection, tags, or the V-field itself). Group by typed indices and leave
local-letter charge separate; only ordered nonlocal letters paid
exponentially small here. Doesn't split a determinant by a geometric mask
without computing new windows and new inverse corrections, and we don't
freeze the inverse entries on changing stationary input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Function Set Matrix MeasureTheory Lattice RG Wilson Pressure Tree
open Next.SectorChange FreeResolvent
open Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {ι : Type} {c : Side} {B n l : ℕ}

section notes
variable {f g : ι → ℝ} {a H : ℝ}

/-- Price every support hit, including term index multiplicities.
Retain the exponent for consumption. -/
def Load (X : ι → Support c) (B : ℕ) (f : ι → ℝ) (a H : ℝ) :=
    SumBudget (fun i => |f i| * Real.exp (a*coverNumber B (X i))) H

lemma load_lump {X : ι→Support c} (Z : Support c) (hp : Ac.Hit X B g a H) (hf : ∀ i, |f i| ≤ g i)
    (h : ∀ i, X i ⊆ Zᶜ → f i=0) : Load X B f a ((Z.card:ℝ)*H) := by
  let u (j : Site c) (i : ι) := if j∈X i then g i*Real.exp (a*coverNumber B (X i)) else 0
  have hb : SumBudget (fun i => ∑ j∈Z,u j i) ((Z.card:ℝ)*H) := budget_loosen
      (budget_over Z u (fun _ => H) (fun j _ => hp j)) (by simp)
  refine budget_mono hb (fun i => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) fun i => ?_
  by_cases he : X i⊆Zᶜ
  · rw [h _ he, abs_zero, zero_mul]; exact hb.1 i
  obtain ⟨j,hj,ht⟩ := Finset.not_subset.mp he
  apply le_trans _ (Finset.single_le_sum (s:=Z) (f:=fun j => u j i) (fun j _ => (hp j).1 i) (by simpa using ht))
  show _ ≤ u j i; unfold u; rw [if_pos hj]
  exact mul_le_mul_of_nonneg_right (hf i) (Real.exp_pos _).le

lemma Load.absolute {X : ι → Support c} (h : Load X B f a H) (ha : 0 ≤ a) : SumBudget (fun i=>|f i|) H :=
  budget_mono h (fun i => abs_nonneg _) fun i => le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity))
lemma Load.summable {X : ι → Support c} (h : Load X B f a H) (ha : 0 ≤ a) : Summable f :=
  .of_norm (h.absolute ha).2.1


end notes
section charges
variable [Fintype ι] [DecidableEq ι] {W W' : ι → Set ι} {A A' : Square ι}
  {p : ι → Site c} {v C q γ a r : ℝ}

-- Equality on the series.
omit [DecidableEq ι] in
lemma gather {f : Letter ι n→ℝ} (hf : Summable f) (h : ∀ i : ι, Summable fun m => ∑ x,f ⟨m,i,x⟩) :
    ∑' z,f z = ∑ i, ∑' (m : ℕ), ∑ x,f ⟨m,i,x⟩ := by
  rw [Summable.tsum_sigma' (fun m=>.of_finite) hf]
  simp_rw [tsum_fintype,Fintype.sum_prod_type]
  exact Summable.tsum_finsetSum fun i _ => h i

omit [Fintype ι] [DecidableEq ι] in
lemma unmarked {f : Letter ι n → ℝ} (h : Ac.Hit (inventory p l B) B (ticket p B v C q (n:=n)) a γ)
    (hf : ∀ i, |f i| ≤ ticket p B v C q i) : Load (inventory p l B) B f a (((Finset.univ:Support c).card:ℝ)*γ) := by
  refine load_lump Finset.univ h hf fun i hi => ?_
  have ht : (inventory p l B i).Nonempty := ⟨_,first_lens _ i.2.1 i.2.1 _ (lens_root p i.2.1 _ _)⟩
  exact False.elim (by simpa using ht.mono hi)

namespace Priced
variable (h : Priced (native c) p W A v C q)
include h
lemma contributions (hq : q<1) (hψ : (Schur.clouded W A).PosDef)
    (hr : Aperture p B W A) (ha : 0≤a) (hp : Ac.Hit (inventory p l B) B (ticket p B v C q (n:=1)) a γ)
    (hc : Ac.Hit (inventory p l B) B (ticket p B v C q (n:=0)) a γ) :
    Summable (page W A) ∧ Summable (errata W A) ∧
    Real.log A.det = (∑ i, letterBase W A i)+(∑' z,page W A z) ∧
    Real.log (1+excess W A).det = ∑' z,errata W A z := by
  have hv := (unmarked hp (fun i => (h.scrolls hr i).2.2)).summable ha
  have ht := (unmarked hc (h.erratas hr)).summable ha
  obtain ⟨hx,he,ha,hc⟩ := h.labeled hq hψ
  rw [Finset.sum_add_distrib] at hx
  refine ⟨hv,ht,?_,?_⟩
  · rw [gather hv ha]; exact hx
  rw [gather ht hc]; exact he


end Priced
end charges
end YM.AnalyticBridge.RelativeLogdet
