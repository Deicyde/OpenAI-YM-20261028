import Mathlib.Data.Set.Finite.List
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Engrave


/-!
# Truncated smooth calls

For short ℓ no infinitely differentiated sum (though countably many real
labels/coupling coefficients, keep the budget). Call over all slots including
unscaled V variation; clocks can reduce the estimates with further rate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Exterior Wilson Push.AbsoluteSums Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {v u d e : ℝ} {k : ℕ}
open Brush

variable (T : PathData G) (p : Cell c) (R : ℕ)

lemma autumn {g : ℕ→ℝ} (p : PathData G) (i : PlaqAxes) (H : Finset Slot) (hg : Summable fun j=> |g j|) :
    ∑ s∈H, |∑' j:ℕ, if (p.row i j).2=s then g j else 0| ≤ ∑' j,|g j| := by
  let h (s : Slot) j := if (p.row i j).2=s then g j else 0
  have he (s) : Summable (fun j=> |h s j|) := by
    apply hg.of_nonneg_of_le (fun _=> abs_nonneg _); intro j; unfold h; split <;> simp
  change (∑ s∈H,|∑' j,h s j|) ≤ _
  apply le_trans (b:=∑ s∈H,∑' j, |h s j|)
  · exact sum_le_sum fun i _=> norm_tsum_le_tsum_norm (f:=h i) (he i)
  rw [← Summable.tsum_finsetSum (fun i (_:i∈H)=> he i)]; refine (summable_sum (fun i (_:i∈H)=> he i)).tsum_le_tsum (fun j=>?_) hg
  by_cases hs : (p.row i j).2∈H <;> simp [h,apply_ite abs,hs]

private lemma finiteSlots (R M : ℕ) (h : 0<M) : {a : Slot| a.length*M ≤ R}.Finite := by
  letI : Fintype Lattice.Step := Fintype.ofEquiv (Axis × Bool) (show _≃_ from
    { toFun x:= ⟨x.1,x.2⟩, invFun x:= (x.1,x.2), left_inv _:= rfl, right_inv _:= rfl })
  refine (((List.finite_length_le Lattice.Step R).prod (Set.finite_univ (α:=PlaqAxes))).image (fun x => (⟨x.1,x.2⟩:Slot))).subset ?_
  intro i hi; change i.length*M≤R at hi
  refine ⟨(i.walk,i.plaq),⟨?_, Set.mem_univ _⟩,rfl⟩; exact le_trans (show i.walk.length ≤ i.length by unfold Slot.length; omega)
    ((le_mul_of_one_le_right (Nat.zero_le _) h).trans hi)

/-- Price at unmasked paths, includes traversal and polynomial factors. -/
theorem shortened (M : ℕ) (h : 0<M) {σ C Λ} {P : Clip} (he : T.Bounds P σ C Λ)
    {U : E → Config G c} (hd : 0≤d) (hp : ∀ j, Brush k (royalty G) d (fun i=> G.mat (U i j)) x) :
    Brush k (C*royalty G^2) (2*R*(d*royalty G)) (fun i=> shorten T R M (U i) p) x := by
  let z := finiteSlots R M h; let H:=z.toFinset; let g i:=(T.row p.2 i).1
  let s j i := if (T.row p.2 i).2=j then g i else 0
  let f (i : Slot) := ∑' j,s i j
  let a := he.rows p.2
  have hz : Summable (fun j=>|g j|) := Work.F03.row_abs_summable _ he _
  have hk : ∑ i∈H,|f i| ≤ C := (autumn T p.2 H hz).trans ((hz.tsum_le_tsum (fun i=>
    le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg he.width.le (Nat.cast_nonneg _)))) a.2.1).trans a.2.2)
  have hv j : Summable (s j) := Summable.of_norm_bounded hz (fun i=> by dsimp only [s]; split <;> first | exact le_rfl | exact ((norm_zero (E:=ℝ)).trans_le (abs_nonneg (g i))))
  have ht : (fun i=> shorten T R M (U i) p)=(fun i=>∑ j∈ H, f j • j.atSite (U i) p.1) := by
    ext1 i; unfold f shorten; simp_rw [← Summable.tsum_smul_const (hv _),← Summable.tsum_finsetSum (s:=H) (f:= fun j n => s j n • j.atSite (U i) p.1) (fun j _=> (hv j).smul_const _)]
    apply tsum_congr; intro j; let i:=T.row p.2 j
    unfold shortenTerm; split
    next he => simp [s,H,ite_smul,PathData.ellTerms,g,he]
    next hn => simp [s,H,ite_smul,g,hn]
  rw [ht]
  have hi := royalty_ge G
  refine (Brush.spree H _ (fun i=>|f i| * royalty G^2) (show 0 ≤ 2*(R:ℝ)*(d*royalty G) by positivity) (fun i hi=> ?_)).climb ?_ le_rfl
  · exact ((slot_cost i _ hd hp).smul (f i)).climb (by rfl) (by
      have hx : i.length*M ≤ R := z.mem_toFinset.mp hi
      have hy := le_mul_of_one_le_right (Nat.zero_le i.length) h
      have hb : 0 ≤ royalty G := zero_le_one.trans (royalty_ge G)
      gcongr; omega)
  rw [← Finset.sum_mul]; gcongr
end YM.ConnectedActivityE6.Blaze
