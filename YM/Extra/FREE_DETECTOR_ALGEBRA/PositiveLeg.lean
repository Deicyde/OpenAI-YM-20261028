import YM.Extra.FREE_DETECTOR_ALGEBRA.Shift

set_option warningAsError false

/-!
# Positive reflected Gram for all jet orders simultaneously

No barred operation needed yet (real). `legKernel` covariance is ordinary
Euclidean at nonzero difference x; apply to label transformed with tensor
reflection at **second** point. This diagonalization uses a triangular shift
of the *dual* probes (Riesz Frobenius convention above). Works also for
zero colors, zero derivative order, empty leg tower.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {G : Gauge} {x y : E4} {j k n : ℕ}

/-- Positive pivot in the basis of tensors for legs (rather than dual
coordinates on arbitrary jets). -/
def price (x : E4) (j : ℕ) : ℝ := (-1)^j * strength j * rr x ^ (j+2)
lemma price_pos (hx : x ∈ away) (j : ℕ) : 0 < price x j := mul_pos (strength_sign _) (pow_pos (rr_pos hx) _)

/-- Real reflected pairing of tensor tests at separation x (first point
minus second). -/
def scan (hx : x ∈ away) (j k : ℕ) : Sol G.Color j →ₗ[ℝ] Sol G.Color k →ₗ[ℝ] ℝ where
  toFun P := (pairing hx (dualSol G.Color j P)).comp ((solO (face x)).trans (dualSol G.Color k)).toLinearMap
  map_add' P Q := by ext R; simp
  map_smul' c P := by ext R; simp

lemma scan_read (hx : x ∈ away) (P : Sol G.Color j) (Q : Sol G.Color k) :
    scan hx _ _ P Q = legKernel (G:=G) (dualSol _ _ P) (dualSol _ _ (solO (face x) Q)) x := rfl

lemma scan_sym (hx : x ∈ away) (P : Sol G.Color j) (Q : Sol G.Color k) :
    scan hx _ _ P Q = scan hx _ _ Q P := by
  change pairing hx (dualSol G.Color _ P) (dualSol _ _ (solO (face x) Q)) = _
  rw [exchange,scan_read]
  let s := face x
  have hh : mov s x = -x := face_negates x
  have hs : s*s=1 := by nth_rw 1 [← (show s⁻¹=s from face_inv x)]; exact inv_mul_cancel _
  have he : solO s (solO s P) = P := by change solAct s (solAct s P) = _; rw [← solAct_mul,hs,solAct_id]
  have ht := leg_cov s Q (solO s P) hx
  rw [he,hh] at ht
  exact ht

lemma slide_sum (P : Sol G.Color j) (Q : Sol G.Color k) (hx : x ∈ away) :
    ∑ i : Fin (j+1), scan hx i.val k ((shifts j i.val x) P) Q = (-1)^k *
      dotF (solO (face x) Q).val (WaveOn.nth (signal (G:=G) P x) k x) := by
  simp_rw [scan_read,replyTest _ _ hx]
  have he : WaveOn.nth (signal (G:=G) P x) k x = ∑ i : Fin (j+1), WaveOn.nth (reply (G:=G) (shifts j i.val x P)) k x := by
    ext1 a; ext1 b
    rw [Finset.sum_apply, Finset.sum_apply]
    refine coeffFsum _ _ _ _ fun i _ => ((replied (_ : Sol G.Color i.val)).smooth a b x hx).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [he,_root_.map_sum, Finset.mul_sum]

lemma slide_below (P : Sol G.Color j) (Q : Sol G.Color k) (hk : k < j) (hx : x ∈ away) :
    ∑ i : Fin (j+1), scan hx i.val k ((shifts j i.val x) P) Q = 0 := by rw [slide_sum,signal_lower P hx hk]; simp

lemma slide_top (P Q : Sol G.Color j) (hx : x ∈ away) :
    ∑ i : Fin (j+1), scan hx i.val j ((shifts j i.val x) P) Q = price x j * dotF P.val Q.val := by
  rw [slide_sum,signal_top P hx,_root_.map_smul]
  change (-1)^j * ((strength j * rr x ^ (j+2)) * dotF (carry (face x) Q.val) (carry (face x) P.val)) = _
  rw [carry_dot,dotF_symm]
  unfold price; ring

abbrev ProbeTower (G : Gauge) (n : ℕ) := (j : Fin n) → Sol G.Color j.val

def towerB (hx : x ∈ away) (n : ℕ) : ProbeTower G n →ₗ[ℝ] ProbeTower G n →ₗ[ℝ] ℝ where
  toFun p :=
    { toFun q := ∑ j : Fin n, ∑ k : Fin n, scan hx j.val k.val (p j) (q k)
      map_add' := by intro u w; simp [Finset.sum_add_distrib]
      map_smul' := by intro c p; simp [Finset.mul_sum] }
  map_add' := by intro u v; ext w; simp [Finset.sum_add_distrib]
  map_smul' := by intro c p; ext v; simp [Finset.mul_sum]

def originLeg (G : Gauge) {n : ℕ} (i : Fin n) : Sol G.Color i.val →ₗ[ℝ] ProbeTower G n := LinearMap.single ℝ (fun i : Fin n => Sol G.Color i.val) i

lemma towerB_single (hx : x ∈ away) (i m : Fin n) (P : Sol G.Color i.val) (Q : Sol G.Color m.val) :
    towerB hx n (originLeg G i P) (originLeg G m Q) = scan hx _ _ P Q := by
  change (∑ j : Fin n, ∑ k : Fin n, scan hx j.val k.val (Pi.single (M := fun i : Fin n => Sol G.Color i.val) i P j) (Pi.single (M := fun i : Fin n => Sol G.Color i.val) m Q k)) = _
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ _)]
    · simp
    · intro k _ hk; rw [Pi.single_eq_of_ne hk,_root_.map_zero]
  intro j _ hj; rw [Pi.single_eq_of_ne hj]; simp

lemma towerB_sym (hx : x ∈ away) (p q : ProbeTower G n) : towerB hx n p q = towerB hx n q p := by
  change (∑ j : Fin n, ∑ k : Fin n, scan hx j.val k.val (p j) (q k)) = _
  rw [Finset.sum_comm]
  change _ = ∑ k : Fin n, ∑ j : Fin n, scan hx _ _ (q k) (p j)
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => scan_sym hx ..

def before (i : Fin n) (k : Fin (i.val+1)) : Fin n := ⟨k.val, lt_of_lt_of_le k.isLt i.isLt⟩

def newLeg (G : Gauge) (x : E4) {n : ℕ} (i : Fin n) : Sol G.Color i.val →ₗ[ℝ] ProbeTower G n :=
    ∑ k : Fin (i.val+1), (originLeg G (before i k)).comp (shifts i.val k.val x)

lemma newLeg_old (hx : x ∈ away) (i m : Fin n) (P : Sol G.Color i.val) (Q : Sol G.Color m.val) :
    towerB hx n (newLeg G x i P) (originLeg G m Q) = ∑ k : Fin (i.val+1), scan hx k.val m.val (shifts _ k.val x P) Q := by
  unfold newLeg; simp only [LinearMap.sum_apply,_root_.map_sum, LinearMap.comp_apply,towerB_single]; rfl

lemma newLeg_below (hx : x ∈ away) (i m : Fin n) (hp : m < i) (P : Sol G.Color i.val) (Q : Sol G.Color m.val) :
    towerB hx n (newLeg G x i P) (newLeg G x m Q) = 0 := by
  conv_lhs => rhs; rw [newLeg,LinearMap.sum_apply]
  rw [_root_.map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  change towerB hx n (newLeg G x i P) (originLeg G (before m k) _) = _
  rw [newLeg_old]; apply slide_below; exact lt_of_le_of_lt (Nat.le_of_lt_succ k.isLt) hp

lemma newLeg_diag (hx : x ∈ away) (i : Fin n) (P Q : Sol G.Color i.val) :
    towerB hx n (newLeg G x i P) (newLeg G x i Q) = price x i.val * dotF P.val Q.val := by
  conv_lhs => rhs; rw [newLeg,LinearMap.sum_apply]
  rw [_root_.map_sum, Finset.sum_eq_single_of_mem (Fin.last i.val) (Finset.mem_univ _)]
  · change towerB hx n (newLeg G x i P) (originLeg G i (shifts i.val i.val x Q)) = _
    rw [shifts_self,newLeg_old,slide_top]
  intro k _ hk
  change towerB hx n (newLeg G x i P) (originLeg G (before i k) _) = _
  rw [newLeg_old]; apply slide_below; exact Fin.lt_last_iff_ne_last.mpr hk

def shiftAll (G : Gauge) (x : E4) (n : ℕ) : ProbeTower G n →ₗ[ℝ] ProbeTower G n :=
    ∑ i : Fin n, (newLeg G x i).comp (LinearMap.proj i)

theorem shiftAll_gram (hx : x ∈ away) (p q : ProbeTower G n) :
    towerB hx n (shiftAll G x n p) (shiftAll G x n q) = ∑ i : Fin n, price x i.val * dotF (p i).val (q i).val := by
  unfold shiftAll; simp only [LinearMap.sum_apply,_root_.map_sum,LinearMap.comp_apply,LinearMap.proj_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i), newLeg_diag]
  intro j _ hj; rcases lt_or_gt_of_ne hj with h|h
  · rw [towerB_sym]; exact newLeg_below hx i j h (q i) (p j)
  exact newLeg_below hx j i h (p j) (q i)

lemma shiftAll_pos (hx : x ∈ away) {p : ProbeTower G n} (he : p ≠ 0) :
    0 < towerB hx n (shiftAll G x n p) (shiftAll G x n p) := by
  rw [shiftAll_gram]
  have hv : ∃ i, (p i).val ≠ 0 := not_forall_not.mp (fun h => he (funext fun i => Subtype.ext (not_not.mp (h i))))
  obtain ⟨i, hi⟩ := hv
  exact Finset.sum_pos' (fun a _ => mul_nonneg (price_pos hx _).le (dotF_nonneg _))
    ⟨i, Finset.mem_univ _, mul_pos (price_pos hx _) (dotF_pos hi)⟩

def shiftDual (G : Gauge) {x : E4} (hx : x ∈ away) (n : ℕ) : ProbeTower G n ≃ₗ[ℝ] ProbeTower G n :=
  LinearEquiv.ofInjectiveEndo (shiftAll G x n) (LinearMap.ker_eq_bot.mp (by
    refine LinearMap.ker_eq_bot'.mpr fun p h => ?_
    by_contra he; have hp := shiftAll_pos hx he; simp [h] at hp))

/-- Simultaneous (not direct-summing independent Gram assertions!)
positions at difference x. Sharp kernel on actual constrained jets. -/
theorem towerB_pos (hx : x ∈ away) (p : ProbeTower G n) : 0 < towerB hx n p p ↔ p ≠ 0 := by
  constructor
  · intro he h; simp [h] at he
  obtain ⟨q,rfl⟩ := (shiftDual G hx n).surjective p
  intro he; exact shiftAll_pos hx ((map_ne_zero_iff _ (shiftDual G hx n).injective).mp he)
end YM.Extra.FD
