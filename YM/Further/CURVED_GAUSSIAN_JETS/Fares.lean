import YM.Further.CURVED_GAUSSIAN_JETS.Shape
import YM.Next.WARD_BIN.Lies

/-!
# Uniform post-L costs for increments used in the chart comparisons
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.ChangeV
open Tree Lattice Wilson RG Precision Bid Exterior SectorNext.Vacuum Pockets Work Set Metric Matrix Function Filter WardBin.Lies Push.Uniform Progress.StationaryScenes Pressure
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {f c n : Side} {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {x : X} {C K : ℝ} {j k m : ℕ}

def Seen (U : X → Config G f) (k : ℕ) (x : X) (C : ℝ) := ∀ i, Allows k (fun y=> G.mat (U y i)) x C
def Views (b : X → Directions G f) (k : ℕ) (x : X) := ∀ i, Allows k (fun y=> b y i) x 1

def matSize (G : Gauge) := ‖(1:G.Mat)‖
lemma mat_size (u : G.El) : ‖G.mat u‖ = matSize G := by simpa only [one_mul,matSize] using Gauge.frob_mul_eq (1:G.Mat) (G.mat u) (G.mat_mul_star u)
lemma seen_const (U : Config G f) : Seen (fun _ : X=>U) k x (matSize G) := fun _=> allows_const _ (mat_size _).le

def gas (k : ℕ) (K : ℝ) := 1+2^k * composeCost k K 1
lemma Exp_nonneg (h : ExpReceipt G k K) : 0 ≤ K := (h 0 (by simp)).nonneg
lemma gas_one (hk : 0≤K) (k : ℕ) : 1≤gas k K := le_add_of_nonneg_right (by unfold composeCost; positivity)

lemma Seen.advance {U : X → Config G f} (h : Seen U k x C) (hk : ExpReceipt G k K) {b : X → Directions G f} (hb : Views b k x) : Seen (fun y=>increment (U y) (b y)) k x (gas k K*C) := by
  intro i
  have hE := (hk _ (hb i |>.value)).comp (f:=fun y=>b y i) (hb i)
  exact (hE.times (h i)).mono (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (h i |>.nonneg))
lemma Seen.jogs {U : X → Config G f} (h : Seen U k x C) (hk : ExpReceipt G k K) {J : X → Slab G f j} (hb : ∀ i, Views (fun y=> J y i) k x) : Seen (fun y=> chug j (U y) (J y)) k x (gas k K^j*C) := by
  induction j generalizing U C with
  | zero => simpa [chug] using h
  | succ j ih => rw [pow_succ,mul_assoc]; exact ih (J:=fun y=> Fin.tail (J y)) (h.advance hk (hb 0)) (fun i => hb i.succ)

lemma linear_fare (L : X →L[ℝ] Y) (h : ∀ y, ‖L y‖ ≤ ‖y‖) (hx : ‖x‖ ≤ 1) : Allows k L x 1 := allows_linear (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa)) ((h _).trans hx)
lemma linear_views {J : X → Directions G f} (h : ∀ i, ∃ L : X →L[ℝ] G.Color, ⇑L = (fun y=>J y i) ∧ ∀ y, ‖L y‖ ≤ ‖y‖) (hx : ‖x‖ ≤ 1) : Views J k x := by
  intro i; obtain ⟨L,hL,he⟩ := h i; rw [←hL]; exact linear_fare L he hx

lemma slabs {L : X →L[ℝ] Slab G f j} (he : ∀ y,‖L y‖ ≤ ‖y‖) (hx : ‖x‖ ≤ 1) (i : Fin j) : Views (fun y=> L y i) k x := by
  apply linear_views ?_ hx; intro b
  refine ⟨ContinuousLinearMap.proj b ∘L ContinuousLinearMap.proj i ∘L L, rfl, fun y=>?_⟩
  exact (norm_le_pi_norm (L y i) _).trans ((norm_le_pi_norm (L y) _).trans (he _))
lemma fields {L : X →L[ℝ] Directions G f} (he : ∀ y,‖L y‖ ≤ ‖y‖) (hx : ‖x‖ ≤ 1) : Views (fun y=> L y) k x := by
  apply linear_views ?_ hx; intro b; exact ⟨ContinuousLinearMap.proj b ∘L L,rfl,fun y=>(norm_le_pi_norm (L y) _).trans (he _)⟩
lemma Views.copy {L : X → Directions G c} (he : Views L k x) (r : Ratio c f) : Views (fun y=> linearCopy r (L y)) k x := by intro b; unfold linearCopy; dsimp only; split_ifs; exact allows_const _ (by simp); exact he _
lemma Seen.mimic {U : X → Config G c} (he : Seen U k x C) (hC : matSize G ≤ C) (r : Ratio c f) : Seen (fun y=> replica r (U y)) k x C := by intro b; unfold replica; dsimp only; split_ifs; exact allows_const _ ((mat_size (1:G.El)).le.trans hC); exact he _
lemma Seen.mono {U : X → Config G c} (he : Seen U k x C) (hC : C ≤ K) : Seen U k x K := fun b=> (he b).mono hC

-- uniform total price for left slabs followed by one more fine (regular a) increment
-- (also when an extra starting field is on a slab at 1 instead of literal V)
def fullCost (G : Gauge) (k : ℕ) (K : ℝ) := gas k K^(k+2)*matSize G
lemma full_nonneg (G : Gauge) (k : ℕ) (hK : 0≤K) : 0 ≤ fullCost G k K := by have := gas_one hK k; unfold fullCost matSize; positivity

lemma replica_pay (r : Ratio c f) (V : Config G c) (hk : ExpReceipt G k K) (hj : j ≤ k) (J : X → Slab G c j) (hb : ∀ i, Views (fun y=> J y i) k x) (b : X → Directions G f) (h : Views b k x) :
    Seen (fun y=> increment (replica r (chug j V (J y))) (b y)) k x (fullCost G k K) := by
  have hx := (seen_const V).jogs hk hb
  have hz := gas_one (Exp_nonneg hk) k
  have hg := (hx.mimic ?le r).advance hk h
  case le => exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hz)
  refine hg.mono ?_; rw [←mul_assoc, ← pow_succ']; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hz (by omega : j+1≤k+2)) (norm_nonneg _)

abbrev joint (G : Gauge) (c f : Side) (j : ℕ) := Slab G c j × Directions G f

def twoStep (r : Ratio c f) (V : Config G c) (j : ℕ) (x : joint G c f j) := increment (replica r (chug j V x.1)) x.2
lemma two_pay {x : joint G c f j} (r : Ratio c f) (V : Config G c) (hk : ExpReceipt G k K) (hj : j ≤ k) (hx : ‖x‖ ≤ 1) : Seen (twoStep r V j) k x (fullCost G k K) :=
    replica_pay r V hk hj (ContinuousLinearMap.fst ℝ _ _) (slabs (fun y=>show ‖y.fst‖ ≤ _ from by rw [Prod.norm_def]; exact le_max_left ..) hx) (ContinuousLinearMap.snd ℝ _ _) (fields (fun y=>show ‖y.snd‖ ≤ _ from by rw [Prod.norm_def]; exact le_max_right ..) hx)

lemma tap_read (H : Y → X) {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (b : Z →L[ℝ] Y) (h : DifferentiableAt ℝ H 0) (v : Z) : fderiv ℝ (fun x=>H (b x)) 0 v=fderiv ℝ H 0 (b v) := by
  have he := ((show DifferentiableAt ℝ H (b 0) by simpa using h).hasFDerivAt.comp 0 (b.hasFDerivAt))
  rw [map_zero] at he -- dependent?
  exact congr_arg (fun L : Z →L[ℝ] X=> L v) he.fderiv
lemma allows_proj {g : X → G.Color} (h : Allows k g x C) (i : G.ColorIndex) : Allows k (fun y=>(g y).ofLp i) x C := by
  rw [← one_mul C]
  exact h.linear (EuclideanSpace.proj i) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=> by rw [one_mul]; exact Shape.coord_paid v _)

end YM.Further.CurvedGaussianJets.ChangeV
