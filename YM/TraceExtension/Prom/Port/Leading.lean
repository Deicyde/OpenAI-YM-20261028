import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Leading
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Leading for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch WeightedGaussianMarginal45C.Issue.Cut
    AnalyticBridge.LocalGaussianLaws Work.F08 FreeResolvent Exterior
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}

section plan
variable {C : Family G} (B : Binding C) (N i p : ℕ)
local notation "S" => C.path.levels.clock.op i p
local notation "x" => C.path.levels.clock.hatBeta i

variable (hh : i<N)

include hh

end plan

section finances
open Next.Free Flux Filter
private lemma row_sum_fullSky (A : veilPsi S.patch.L) {s M : ℝ} (hs : 0<s) (hp : A.strip s M)
    (i : FreeResolvent.Slot G f 2) :
    ∑ j, |panePsi G S A i j| ≤ ticket (TypeFace 2) M := by
  let z := (i.1,i.2.1); let e := splitCo S.ratio (TypeFace 2)
  have hh := row_sprawl (show 0≤(0:ℝ) from le_rfl) (strip_mono hp hs.le le_rfl) c (e z)
  simp only [zero_mul,Real.exp_zero,one_mul] at hh
  have H : (∑ j, |panePsi G S A i j|) = ∑ j:Body 2 c, |A.acts c (e z) j| := by
    unfold panePsi; simp only [tensor, Matrix.of_apply,Fintype.sum_prod_type,apply_ite abs,abs_zero]; simp; rfl
  rw [H]; exact hh

variable {C : Family G} (B : Binding C) {N i p : ℕ}

-- Use rows on B. These hypotheses (per step) available from Binding and
-- levels on same C. Use also later with V PATH still equal.
local notation "s" => C.path.levels.clock.op i p
local notation "x" => C.path.levels.clock.hatBeta i

variable (h : i < N)

include h
local notation "X" => stamp C.path.levels N p
local notation "U" => C.path.levels.clock.J (i+1)
local notation "J" => C.path.levels.clock.J i
local notation "z" => max (B.prices.Ω U) (B.prices.Ω J)
local notation "t" => min (B.prices.α U) (B.prices.α J)

lemma sufficient_rowsSky : (curves B N i).strip t (psiBudget z / ((C.S.block i).val:ℝ)^2) := by
  -- apply Deep, not estimating new Pt overhead from post-L x
  let D := B.world.towers N i
  let A := B.world.H N (i+1); let H:=B.world.H N i
  have hf : A.dual_diag.strip t z := strip_mono (B.pays.rows N (i+1) h).2.2.2.2 (min_le_left ..) (le_max_left ..)
  have he : H.diagonal.strip t z := strip_mono (B.pays.rows N i h.le).1 (min_le_right ..) (le_max_right ..)
  let k := ((C.S.block i).val:ℝ)^2
  have ha : D.T.strip t (z/k) := strip_mono (P:=D.T) ((B.pays.costs N i h).2.2.2 [] (Nat.zero_le _)).2 (min_le_left ..) (div_le_div_of_nonneg_right (le_max_left ..) (sq_nonneg _))
  have hr := (lt_min (B.prices.alpha_pos U) (B.prices.alpha_pos J)).le
  have H' := strip_compose hr (strip_fine hr hf ha) he
  convert H' using 1
  · rfl
  dsimp only [psiBudget]; unfold k; ring

lemma rich_pathSky u v : (track X i).H u v = (panePsi G s (curves B N i) (toPAC u) (toPAC v) : ℂ) := by
  rw [planner_at B _ _ _ h]
  let D := B.world.towers N i; let A':= B.world.H N (i+1); let B':= B.world.H N i
  have hf : A'.dual_diag.strip t z := strip_mono (B.pays.rows N (i+1) h).2.2.2.2 (min_le_left ..) (le_max_left ..)
  have he : B'.diagonal.strip t z := strip_mono (B.pays.rows N i h.le).1 (min_le_right ..) (le_max_right ..)
  let k := ((C.S.block i).val:ℝ)^2
  have ha : D.T.strip t (z/k) := strip_mono (P:=D.T) ((B.pays.costs N i h).2.2.2 [] (Nat.zero_le _)).2 (min_le_left ..) (div_le_div_of_nonneg_right (le_max_left ..) (sq_nonneg _))
  have hr := (lt_min (B.prices.alpha_pos U) (B.prices.alpha_pos J)).le
  have hy := strip_fine hr hf ha
  have ht : tensor G (Current.psi s A' B' D)=panePsi G s (coverPsi A' B' D) := by
    apply congr_arg
    unfold coverPsi Extra.Iteration.psi Extra.Iteration.moving; simp only [Option.elim]
    symm; erw [installed_compose (C.path.levels.clock.op i p).ratio hr hy he, installed_fine _ hr hf ha]; rfl
  rw [show panePsi G s (curves B N i) = _ from ht.symm]

lemma high_rowsSky (u) : let P := psiBudget z / ((C.S.block i).val:ℝ)^2
    (∑ v, ‖(track X i).H u v‖) ≤ ticket (TypeFace 2) P ∧
    (∑ v, ‖(short B N p i).H u v - (track X i).H u v‖) ≤ cheque (TypeFace 2) t P x := by
  intro P
  have hr := lt_min (B.prices.alpha_pos U) (B.prices.alpha_pos J)
  simp_rw [H_at, rich_pathSky B h,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  constructor
  · let W : FreeResolvent.Slot G (C.side i p) 2 → ℝ := fun j => |panePsi G s (curves B N i) (toPAC u) j|
    apply ((Equiv.sum_comp toPAC W).trans_le ·)
    exact row_sum_fullSky _ hr (sufficient_rowsSky B h) _
  have hf := (contour_uses (S:=s) (curves B N i) hr (sufficient_rowsSky B h) (takePaths _ _ x) (toPAC u)).2.1
  let W : FreeResolvent.Slot G (C.side i p) 2 → ℝ := fun j=>|panePsi G s (shorter B N i) (toPAC u) j - panePsi G s (curves B N i) (toPAC u) j|
  apply ((Equiv.sum_comp toPAC W).trans_le ·)
  rw [show ∑ j, W j = _ from (show (∑ j, W j) = ∑ j, |panePsi G s (curves B N i) (toPAC u) j-panePsi G s (shorter B N i) (toPAC u) j| from
    Finset.sum_congr rfl (fun i _ => abs_sub_comm ..))]
  exact hf
end finances
end YM.PhysicalNext.InteractingRank
