import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Matrices
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Bingo
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Quarry
import YM.UVNext.FREE_STRESS_CERTIFICATE.Microphones



/-! # Helpers for comparing exponential charges, volumes only auxiliary
 Includes both signs of loop/tags -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Fare
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (k : S.Choices) (P : PathData G) {b : Clip}
    (B : BudgetPoint) {u σ C Λ : ℝ} {n : ℕ}

section tests
variable {f : Signed→ℝ}
lemma brine {q:ℝ} (h : ∀ s, |f s| ≤ q) : |Patch.average f| ≤ q := by
  apply abs_le.mpr; change -q ≤ Branch.avg f ∧ Branch.avg f ≤ q
  exact ⟨(Branch.avg_const (n:=Signed) (-q)).symm.le.trans (Branch.avg_mono fun i=> (abs_le.mp (h i)).1), (Branch.avg_mono fun i=> (abs_le.mp (h i)).2).trans (Branch.avg_const _).le⟩
lemma ozone {q:ℝ} (V : Config G c) (h: flags B.threshold V=∅) (a : ℕ → Atom G n) (hu : 0 <σ) (hq : SumBudget (fun i=>(a i).budget σ) q) :
    |uncut a V| ≤ (Fintype.card (Site c):ℝ)* (q * B.threshold^n):= by
  rw [← Pane.actly _ _ _ _ h]; exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun i _=> atomVolume _ _ _ _ hu hq)).trans_eq (by simp))
lemma loopbill (V : Config G c) (h : P.Bounds b σ C Λ) (hv : flags B.threshold V=∅) :
    |Precision.loop P V| ≤ (Fintype.card (Site c):ℝ)*(Λ*B.threshold^2) := brine fun i=>ozone B _ (Pane.tranquility _ hv i 0) _ h.width h.two
lemma classbill (V : Config G c) (h : P.Bounds b σ C Λ) (hv : flags B.threshold V=∅) :
    |mainTerm b P V-secondTerm b P V| ≤ (Fintype.card (Site c):ℝ)*(C*B.threshold^3+C*B.threshold^4) := by
  let v (i:Signed):= pull i 0 V
  let m:= fun i:Signed=> uncut P.cubic (v i)+uncut P.quartic (v i)
  rw [show mainTerm b P V-secondTerm b P V=Patch.average m by unfold mainTerm secondTerm Patch.average m v; rw [sum_add_distrib,sum_add_distrib,sum_add_distrib]; ring,mul_add]; apply brine; intro i
  exact (abs_add_le ..).trans (add_le_add (ozone _ _ (Pane.tranquility V hv i 0) _ h.width h.three) (ozone _ _ (Pane.tranquility V hv i 0) _ h.width h.four))
end tests
variable (A : Push.Uniform.Before G σ C S.patch.J S.kernel (n+3)) (ρ : Bid.Dir G c→ AxisChart G F) (O : ChartRatio G)
local notation "R" => A.tables T.high S.patch
local notation "X" => Positions (Uniform.Primary c G)
local notation "φ" => Lapis.table F k T.up T.high
local notation "g" => Lapis.orbit F ρ
local notation "M" => Lapis.gram F T.up T.high ρ k
local notation "ψ" => Lapis.mist F O T.up
open AnalyticBridge.MarginalMultiplier3b1d.FiniteMatrix
variable (he : A.Service F T.high T.up ρ) (ha : Larger (G:=G) S) (h : T.up.Bounds T.high σ C Λ) (V : ℝ) (ht : 1 ≤ V) (hv : (Fintype.card (Joint F G):ℝ) ≤ V)
def tapir (C : ChartPrices) (T' : ℝ) := T'^2*(C.value +(C.gap/2/2)⁻¹)
include he ha h hv
lemma tapping (x : X) (hx : ‖x‖ < (R).horizon) : |Lantern.shade (M) x| ≤ tapir (R) V := by
  obtain ⟨-,hp,hσ,-,ht,-,hy,-,hQ⟩ := A.full_pack F k h ha rfl rfl
  obtain ⟨-,-,-,he',hv',-⟩ := hQ x (weld _ (g x)) (he.pricing (mem_ball_zero_iff.mpr hx))
  have hM:= wakes F k T.up T.high ρ σ C Λ A ha h he x hx
  let Z:=((R).gap/2/2)⁻¹; have hz : 0<Z:= inv_pos.mpr (half_pos (half_pos hp))
  have he : Upper (M x) (R).value := fun i j=> (he' i j).trans (mul_le_of_le_one_right ht.le (decay_le hσ.le _ _)); have hh: Upper (M x)⁻¹ Z:= fun i j=> (hv' i j).trans (mul_le_of_le_one_right hz.le (decay_le hy.le _ _))
  have hi:= (log_abs hM.1 he hh ht.le hz.le).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (countsK F V hv) _) (add_pos ht hz|>.le))
  unfold Lantern.shade; rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; exact (div_le_self (abs_nonneg _) (by norm_num)).trans hi

def meterQ (A : ChartPrices) (n:ℕ) (V : ℝ) := tollS V (n+3) A.value*(1+Before.Service.trailCost A (n+3))
include ht
lemma costQ (x : X) (hx : ‖x‖ < (R).horizon) : ‖φ (x,g x)‖ ≤ meterQ (R) n V * ‖x‖ := by
  have hi:= evacuated F T.up k ρ A ha h he x hx
  have hR:= (A.receipt F k h ha rfl rfl).1
  have hs : 0 < Before.Service.trailCost (R) (n+3) := (he.trail_lipschitz h ha rfl rfl).1
  have hp:= horizonB ht hv hR.pos_C.le hR.pos_a hR.pos_r (show 1≤n+3 by omega) (closedBall_subset_ball hR.reserveH_lt (he.pricing (mem_ball_zero_iff.mpr hx))) (fun i hi=> ⟨(hR.born _ hi).2,(hR.born _ hi).1⟩)
  have he:= hp.1; rw [Lapis.zeroF F k T.up T.high σ C Λ ha h,sub_zero] at he; apply he.trans; unfold meterQ; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by unfold tollS; have := hR.pos_C; positivity)
  rw [show curve _ _= meetVar x (weld _ (g x)) from rfl,norm_meet,add_mul,one_mul]; exact max_le (le_add_of_nonneg_right (mul_nonneg hs.le (norm_nonneg x))) (hi.trans (le_add_of_nonneg_left (norm_nonneg _)))
omit ht in
lemma colo {D u v p' : ℝ} (hp : Golf φ ψ g M n D u v p') (hu : u ≤ (R).horizon) (x:X) (hx : ‖x‖ < u) (β : ℝ) :
    |coverLog F T O k ρ β x - β * φ (x,g x)| ≤ p'+tapir (R) V := by
  unfold coverLog; rw [add_assoc,add_sub_cancel_left]; apply (abs_add_le ..).trans; apply add_le_add _ (tapping F T k A ρ he ha h V hv _ (hx.trans_le hu))
  have hi := hp.color 0 0 ((0:ℝ),x) (norm_zero.trans_le hp.off) (by simp) (show ‖(0:ℝ)‖<v by rw [norm_zero]; exact hp.pos') hx
  simpa only [Real.norm_eq_abs,Lantern.visit,smul_zero,add_zero] using hi.2.bound
end YM.PhysicalNext.Repeat.Fare
