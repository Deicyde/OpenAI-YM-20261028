import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.Further.THRESHOLD_SOURCE_RESTART.ClusterScale
import YM.Push.ABSOLUTE_SUMS.Gas

/-!
# Polynomial gas recurrence for hard-overlap unforced vertices

Lift finite recurrence algebraically from the already-proved real statement
(MvPolynomial argument). Used in ClusterCurrent to justify marked logarithm
identity, BEFORE any estimates on actual kernels. No convergence claimed here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart.Clusters
open Function Filter Set MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Prepare Width Extra.Multi
open Push.AbsoluteSums Coef Partition Graph Ursell
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {α V : Type*} [Fintype V] [DecidableEq V] {n : Side}
variable (X : α → Support n) (W : α → Marks.Algebra V)

def formed (s : Finset α) : Marks.Algebra V := if Gas.separated (blocked X) s then ∏ i∈s,W i else 0
def pSum (m : ℕ) : Marks.Algebra V := ∑' f : Fin (m+1) → α, Clusters.ink X W ⟨m,f⟩

lemma hard : Gas.Hard (blocked X) := ⟨fun _ => Or.inl rfl,fun _ _ => blocked_back X⟩

variable [Fintype α]

def cSum (m : ℕ) : Marks.Algebra V := ∑ i∈(Finset.univ : Finset α).powersetCard m,formed X W i

-- finite expression laws via eval
private def pDisk (m : ℕ) : MvPolynomial α ℝ :=
    ∑ f : Fin (m+1) → α, MvPolynomial.C (coefficient (blocked X) f / (m+1).factorial) *
      ∏ i, MvPolynomial.X (f i)
private def cDisk (m : ℕ) : MvPolynomial α ℝ :=
    ∑ s∈Finset.univ.powersetCard m, if Gas.separated (blocked X) s then ∏ i∈s,MvPolynomial.X i else 0
private lemma pReal (m : ℕ) (w : α→ℝ) : MvPolynomial.eval w (pDisk X m)= Coef.logRow (blocked X) w m := by
  let e := Fintype.equivOfCardEq (show Fintype.card (Option (Fin m))= Fintype.card (Fin (m+1)) by simp)
  rw [logRow,linked_equiv (blocked X) w e]
  unfold linked; rw [Finset.sum_div, pDisk, map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul,map_prod,MvPolynomial.eval_C,MvPolynomial.eval_X]; ring
private lemma cReal (m : ℕ) (w : α → ℝ) : MvPolynomial.eval w (cDisk X m)=gasRow (blocked X) w m := by
  rw [Gas.row (blocked X) _ m (hard X),cDisk, map_sum]; apply Finset.sum_congr rfl; intro i _
  unfold Gas.value; split
  · rw [map_prod]; simp only [MvPolynomial.eval_X]
  exact map_zero _

-- ring hom avoids introducing a NormedAlgebra instance
private abbrev letdown (W : α → Marks.Algebra V) := MvPolynomial.eval₂Hom
    ((Poly.bead (Marks.all V)).comp (algebraMap ℝ ℂ)) W
private lemma pDown (m : ℕ) : letdown W (pDisk X m)=pSum X W m := by
  unfold pSum
  rw [tsum_fintype, pDisk, map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  unfold letdown
  simp only [map_mul,map_prod,MvPolynomial.eval₂Hom_C]
  unfold Clusters.ink
  change Poly.bead (Marks.all V) _*(∏ j, MvPolynomial.eval₂ _ _ (MvPolynomial.X (R:=ℝ) (i j))) = _
  simp only [MvPolynomial.eval₂_X]
  exact Poly.product_bead ..
private lemma cDown (m : ℕ) : letdown W (cDisk X m)=cSum X W m := by
  unfold cSum; rw [cDisk,map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  unfold formed; split
  · rw [map_prod]; refine Finset.prod_congr rfl fun j _ => MvPolynomial.eval₂_X _ _ _
  exact map_zero _

theorem row_cost (m : ℕ) : ((m+1:ℕ):ℂ) • cSum X W (m+1) =
    ∑ j∈Finset.range (m+1), (((j+1:ℕ):ℂ) • pSum X W j)*cSum X W (m-j) := by
  have H : MvPolynomial.C (m+1:ℝ)*cDisk X (m+1) =
      ∑ j∈Finset.range (m+1),MvPolynomial.C (j+1:ℝ)*pDisk X j * cDisk X (m-j) := by
    apply MvPolynomial.funext; intro w; simp only [map_sum, map_mul,MvPolynomial.eval_C,cReal,pReal]; exact Coef.recurrence ..
  have he := congr_arg (fun v => letdown W v) H
  have hv (c : ℕ) : letdown W (MvPolynomial.C (c+1:ℝ)) = Poly.bead (Marks.all V) (↑(c+1:ℕ):ℂ) := by
    unfold letdown
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]; congr 1; push_cast; rfl
  simpa only [map_sum, map_mul, hv,cDown, pDown, Poly.product_bead] using he
lemma run_out (j) (hj : Fintype.card α < j) : cSum X W j = 0 := by
  rw [← cDown]; rw [show cDisk X j=0 from MvPolynomial.funext fun x => by
    rw [cReal _,Gas.rows_above (blocked X) _ (hard X) j hj,map_zero],map_zero]
lemma unity : cSum X W 0=1 := by simp [cSum,formed,Gas.separated]
theorem disk : ∑ m∈ Finset.range (Fintype.card α+1),cSum X W m = ∑ s,formed X W s := by
  have h (s : Finset α) (_ : s∈ Finset.univ) := Finset.mem_range.mpr (Nat.lt_add_one_of_le s.card_le_univ)
  rw [← Finset.sum_fiberwise_of_maps_to h]
  unfold cSum; apply Finset.sum_congr rfl; intro i _
  simp only [Finset.powersetCard_eq_filter,Finset.powerset_univ]
end YM.Further.ThresholdSourceRestart.Clusters
