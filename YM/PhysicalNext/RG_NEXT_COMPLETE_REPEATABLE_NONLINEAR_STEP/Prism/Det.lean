import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.IssuePlan
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pendant
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Plot
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Bass

/-!
# Determinant comparison on the actual marginal Key. Difference is tiny,
 all coefficients has to pay (can grow with $B,|keys|$). Uses orientation
 exact Bud budgets. Insist same support before comparing! Positive/unit
 etc from sigma cubes later; diagonal norm alone not enough. Counts rank
 AFTER projection. Also when root cuts embedded or paper in contour sets.
 Ordinary real scopes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Prism
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {n : ℕ} {v d N : ℝ}

section det
variable {J : Matrix ι ι ℝ} {B : E→ Matrix ι ι ℝ} {Q : Set E}
variable [Fintype ι] [DecidableEq ι]
private lemma signed (p : Equiv.Perm ι) {g : E→ℝ} (h : Brush n v d g x) : Brush n v d (fun x=> Equiv.Perm.sign p • g x) x := by
  let c:= Equiv.Perm.sign p
  rcases Int.units_eq_one_or c with hc|hc
  · simp_rw [show Equiv.Perm.sign p=1 from hc,one_smul]; exact h
  · simp_rw [show Equiv.Perm.sign p= -1 from hc]; change Brush _ _ _ (fun x=> (-1:ℤ) • g x) x; simpa using! h.opposite

abbrev EdgePay (B : E→Matrix ι ι ℝ) (n:ℕ) (v d:ℝ) (x:E) := ∀ i j,Brush n v d (fun x=> B x i j) x

set_option linter.unusedSectionVars false in
lemma demand (r : Finset ι) (h : EdgePay B n v d x) (hf : 0 ≤ d) : Brush n ((r.card.factorial:ℝ)*v^r.card) (r.card*d)
    (fun x=> (Pond.circuit r (B x)).det) x := by
  let f x:=Pond.circuit r (B x); simp_rw [Matrix.det_apply]; refine Brush.climb (Brush.spree _ _ (fun _=> v^r.card) (mul_nonneg (Nat.cast_nonneg _) hf) (fun p _ =>?_)) (by simp [Fintype.card_perm]) le_rfl
  apply signed
  have he:= Brush.all_prod Finset.univ (fun i:↥r => fun y=> f y (p i) i) _ _ (fun i _=> h _ _)
  simpa only [Finset.prod_const,Finset.card_univ,Finset.sum_const,nsmul_eq_mul,Fintype.card_coe] using! he


-- Extract entire determinant minus leading 1, including value ranks.
lemma dry_sail (h : EdgePay B n v 1 x) (hv : 0 ≤ v) (hN : (Fintype.card ι:ℝ) ≤ N) (hp : N^2*v ≤ 1) :
    Brush n (N*(N^2*v)) N (fun y=> (B y+1).det-1) x := by
  let A:=Fintype.card ι; let s:= Finset.univ (α:=Finset ι); let J:=s.erase ∅; let C (j:ℕ) := (j.factorial:ℝ)*v^j
  have he r (hh:r∈J) : r.card≤A := Finset.card_le_univ _
  have hx (i:E) : (B i+1).det-1=∑ j∈J,(Pond.circuit j (B i)).det := by
    unfold J; rw [combs,Finset.sum_erase_eq_sub (f:= fun j : Finset ι=> (Pond.circuit j (B i)).det) (s:=s) (a:=∅) (Finset.mem_univ ∅)]; rw [Matrix.det_isEmpty]
  have ha : 0 ≤ N := (Nat.cast_nonneg (α:=ℝ) A).trans hN
  simp_rw [hx]; refine (Brush.spree _ _ (fun j=> C j.card) ha (fun i hi=> (demand i h zero_le_one).climb le_rfl ?_)).climb ?_ le_rfl
  · rw [mul_one]; exact (Nat.cast_le.mpr (he _ hi)).trans hN
  let U:= Finset.Ioc 0 A; let V (i) := Finset.univ.powersetCard i (α:=ι)
  have hJ: J=U.biUnion V:= by
    ext i; constructor
    · intro hi; refine Finset.mem_biUnion.mpr ⟨_,Finset.mem_Ioc.mpr ⟨Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hi)), he _ hi⟩,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,rfl⟩⟩
    intro hi; obtain ⟨i',hx,hi⟩:=Finset.mem_biUnion.mp hi; have h:= (Finset.mem_powersetCard.mp hi).2; exact Finset.mem_erase.mpr ⟨Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp (lt_of_lt_of_le (Finset.mem_Ioc.mp hx).1 h.ge)),Finset.mem_univ _⟩
  have hV (i) (hi : i∈U) : (∑ j∈V i,C j.card)≤ N^2*v := by
    have hx : ∀ j∈V i,C (Finset.card j)=C i:= fun j hj=> congr_arg C (Finset.mem_powersetCard.mp hj).2
    rw [Finset.sum_congr rfl hx,Finset.sum_const,nsmul_eq_mul]; unfold V C; rw [Finset.card_powersetCard,Finset.card_univ]
    have hg:(Fintype.card ι).choose i≤ A^i:= Nat.choose_le_pow ..
    have hm : (i:ℝ) ≤ N := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hi).2).trans hN
    calc
      _ ≤ (A:ℝ)^i * ((i:ℝ)^i * v^i) := mul_le_mul (by exact_mod_cast hg) (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le_pow (n:=i)) (pow_nonneg hv _)) (by positivity) (by positivity)
      _ ≤ N^i*(N^i*v^i) := by gcongr
      _ = (N^2*v)^i := by ring
      _ ≤ _ := pow_le_of_le_one (by positivity) hp (by have hh:= Finset.mem_Ioc.mp hi; omega)
  rw [hJ,Finset.sum_biUnion (Finset.pairwise_disjoint_powersetCard _ |>.set_pairwise (s:=↑U))]
  refine (Finset.sum_le_sum hV).trans ?_; rw [Finset.sum_const,nsmul_eq_mul,show U.card=A by simp [U]]; exact mul_le_mul_of_nonneg_right hN (by positivity)
end det
end YM.PhysicalNext.Repeat.Prism
