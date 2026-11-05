import YM.Further.DENSE_MIXED_KERNELS.Hall
import YM.Further.DENSE_MIXED_KERNELS.Stroke
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.PhysicalNext.ORDERED_AFFINE_2B.Till
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Hood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels
import YM.Planned.ATOM_GUARDED_LAYOUT.Orbit
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local  Motion PhysicalNext.Repeat 
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "c'" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "Lℓ" => H.S.block i
open Extra.Histories
set_option quotPrecheck false
section method
variable {ι :Type*}{n : Side} {o : Site n} {R : Rep G n}
variable (e : ℕ ≃ ι × ℕ) (P : ι → Coefficient F n)
theorem merge_tab {a b:ι→ ℝ} {v : ℝ} (hp : 0 < v) (h : ∀ i, Tab (P i) o R v (a i) (b i)) (h₁: Summable a) (h₂: Summable b) :
    Tab (merge e P) o R v (∑' i, a i) (∑' i,b i) ∧
      Dominated (fun x : ι×ℕ => (P x.1).maskedTerm R x.2) ∧ Dominated (fun x : ι×ℕ => (P x.1).forced x.2) := by
  classical
  have ha (i:ι):= (h i).first; have hb (i:ι):=(h i).second
  choose E hE hR using fun i=> (h i).regular
  choose D hD hK using fun i=>(h i).forced
  let xmass (x : ι × ℕ) := R.p.mass ((P x.1).support x.2) (E x.1 x.2)
  let fmass (x : ι × ℕ) := R.p.mass (R.activities.forced x.2).support (D x.1 x.2)
  have hx := budget_prod (f:=xmass) hE h₁
  have hf := budget_prod (f:=fmass) hD (h₂.mul_left v)
  have hu (x : ι×ℕ) (U) : ‖(P x.1).forced x.2 U‖ ≤ D x.1 x.2 := (hK x.1 x.2).2 U
  have hh (x : ι×ℕ) : D x.1 x.2 ≤ fmass x := R.p.loMass _ _ (hK x.1 x.2).1
  have hj (j : ℕ) : Summable fun i => D i j := .of_nonneg_of_le (fun i => (hK i j).1)
    (fun i => hh (i,j)) (hf.2.1.prod_symm.prod_factor j)
  refine ⟨?_,⟨xmass,hx.2.1,?_⟩,fmass,hf.2.1,fun i U => (hu i U).trans (hh _)⟩
  · refine ⟨hp,tsum_nonneg ha,tsum_nonneg hb,⟨fun k => E (e k).1 (e k).2, ?_,
      fun k => hR (e k).1 (e k).2⟩, fun k => ∑' i, D i k, ?_, fun j => ⟨tsum_nonneg (fun i => (hK i j).1),?_⟩⟩
    · change SumBudget (fun k => xmass (e k)) _
      exact ⟨fun k => hx.1 _, hx.2.1.comp_injective e.injective,(e.tsum_eq xmass).trans_le hx.2.2⟩
    · have hy (j : ℕ) : R.p.mass (R.activities.forced j).support (∑' i, D i j) = ∑' i, fmass (i,j) := by
        unfold fmass BudgetPoint.mass; rw [← tsum_mul_left]
      simp_rw [hy]
      refine ⟨fun j => tsum_nonneg (fun i => hf.1 _), hf.2.1.prod_symm.prod,?_⟩
      calc
        _ = ∑' i, ∑' j, fmass (i,j) := Summable.tsum_comm hf.2.1
        _ = ∑' x, fmass x := hf.2.1.tsum_prod.symm
        _ ≤ _ := hf.2.2.trans_eq tsum_mul_left
    intro U
    have hs : Summable fun i => ‖(P i).forced j U‖ := .of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun i => hu (i,j) U) (hj j)
    exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum (fun i => hu (i,j) U) (hj j))
  intro i U
  refine le_trans (b:=E i.1 i.2) ?_ (R.p.loMass _ _ (hR i.1 i.2).1)
  dsimp only [Coefficient.maskedTerm]
  by_cases hu : Healthy R.p.threshold ((P i.1).support i.2) U
  · rw [masked_eq _ _ _ _ hu]; exact (hR ..).2 U hu [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ hu,norm_zero]; exact (hR i.1 i.2).1


end method
end YM.MergeProof
