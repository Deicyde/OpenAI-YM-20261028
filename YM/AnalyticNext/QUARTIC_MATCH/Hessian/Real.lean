import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Dues
import YM.AnalyticNext.QUARTIC_MATCH.Pre.Staged

/-!
# Scalar Hessian for pricing on each color separately
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Hessian
open Filter Function Lattice Laurent Bloch Exterior Matrix Precision RG Work.F06 Wilson
open Pre.Centered YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ComplexConjugate InnerProductSpace
variable {c f : Side} (S : StepData c f)
local notation "L" => (S.patch.L.val:ℝ)
local notation "j" => S.patch.J
local notation "D" => d 1 f
local notation "d₀" => d 0 f
local notation "d'" => d 0 c
local notation "Y" => form 1 f
local notation "A" => form 0 f
local notation "V" => form 0 c
local notation "B₀" => palette S
local notation "M" => Precision.mean S

def tariff (y : Y) (v : V) := (d 0 f).transpose *ᵥ y + (L^2) • ((palette S).transpose *ᵥ v)
lemma tariff_add (x y : Y) (u v : V) : tariff S (x+y) (u+v)=tariff S x u+tariff S y v := by
  unfold tariff; simp_rw [mulVec_add, smul_add]; abel
lemma tariff_smul (w : ℝ) (y : Y) (v : V) : tariff S (w • y) (w • v)=w • tariff S y v := by
  unfold tariff; rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_comm (L^2),smul_add]
lemma swapOffer (y : Y) (v : V) : upkeep S (offer y) (offer v)=offer (tariff S y v) := by
  unfold upkeep tariff drawC; rw [← approach_H, ← approach_H,← offer_mat, ← offer_mat]; funext i; simp [offer]

def gain (y : Y) (v : V) := ell2 (D*ᵥ y)+ell2 ((d 0 f).transpose *ᵥ y)+ell2 y/L+ell2 v
lemma swap_gain (y : Y) (v : V) : rent S (offer y) (offer v) = gain S y v := by
  rw [rent,drawC,drawC,← approach_H,← offer_mat,← offer_mat,offer_ell,offer_ell,offer_ell,offer_ell]; rfl
lemma offer_sub {i : Type*} (x y : i→ℝ) : offer (x-y)=offer x-offer y := by funext k; simp [offer]
lemma strain (y : Y) (v : V) : gain S y v ≤ yard j*(ell2 (D*ᵥ y) + ell2 (M*ᵥ y-d'*ᵥ v)+ell2 (tariff S y v)) := by
  have he := energetic S (offer y) (offer v);
  rw [swapOffer S,swap_gain S,drawC,drawC,← offer_mat,← offer_mat, ← offer_mat,← offer_sub, offer_ell,offer_ell,offer_ell] at he; exact he
lemma tari (y : Y) (v : V) : ell2 (tariff S y v) ≤ gain S y v := by rw [← offer_ell,← swapOffer]; exact (uptime ..).trans_eq (swap_gain ..)

lemma given (x : A) : ∃ y : A, tariff S (-(d₀*ᵥ y)) (-(B₀*ᵥ y))=x := by
  let T : A→ₗ[ℝ] A := {
    toFun := fun y => tariff S (-(d₀*ᵥ y)) (-(B₀*ᵥ y))
    map_add' y v := by simp_rw [Matrix.mulVec_add, neg_add]; exact tariff_add ..
    map_smul' s y := by simp_rw [Matrix.mulVec_smul, ← smul_neg]; exact tariff_smul .. }
  apply (LinearMap.injective_iff_surjective (f:=T)).mp ?_ x
  apply (injective_iff_map_eq_zero _).mpr
  intro y hy
  have hz : upkeep S (drawC f 0*ᵥ(offer y)) (approached B₀*ᵥ(offer y))=0 := by
    change tariff S (-(d₀*ᵥ y)) (-(B₀*ᵥ y))=0 at hy
    have h0 : tariff S (d₀*ᵥ y) (B₀*ᵥ y)=0 := by simpa only [tariff,mulVec_neg,smul_neg,← neg_add,neg_eq_zero] using hy
    rw [drawC,← offer_mat,← offer_mat,swapOffer,h0]; funext i; simp [offer]
  by_contra h
  have he := consume S (offer y); rw [hz,ell_zero,mul_zero] at he
  have hh := (house S (offer y)).trans (mul_nonpos_of_nonneg_of_nonpos (resident_pos j).le he);
  rw [offer_ell] at hh; exact (div_pos (ell_pos.mpr h) (side_pos S.patch.L)).not_ge hh

def reserve (i : ℕ) (a k : ℝ) := min a (min k 1) / (3*yard i ^ 2)
lemma reserve_pos (i : ℕ) (a k : ℝ) (ha : 0<a) (hk : 0<k) : 0 < reserve i a k := div_pos (lt_min ha (lt_min hk zero_lt_one))
    (mul_pos (by norm_num) (pow_pos (yard_pos _) _))

/-- Factor form for CT pricing. -/
def baseline (H : Precision.Bed) (x y : Y) (u v : V) := dotProduct (D*ᵥ x) (H.metric.acts f *ᵥ(D*ᵥ y)) +
    S.kernel.penalty * dotProduct (M*ᵥ x-d'*ᵥ u) (M*ᵥ y-d'*ᵥ v) +
    dotProduct (tariff S x u) (tariff S y v)
lemma flatBill (H : Precision.Bed) (x y : Y) (u v : V) : baseline S H x y u v=secondOne S H x y u v+
    dotProduct (tariff S x u) (tariff S y v) := by
  rw [baseline,secondOne,Precision.K, ← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, dotProduct_mulVec x,Matrix.vecMul_transpose]

lemma positive_gain (x : Y) (u : V) : 0 ≤ gain S x u := by
  unfold gain
  exact add_nonneg (add_nonneg (add_nonneg (ell_nonneg _) (ell_nonneg _)) (div_nonneg (ell_nonneg _) (by positivity))) (ell_nonneg _)
lemma enter (x : Y) (u : V) (h : x≠0 ∨ u≠0) : 0 < gain S x u := by
  have hb := ell_nonneg x; have hL := side_pos S.patch.L;
  unfold gain
  rcases h with v|v
  · exact add_pos_of_pos_of_nonneg
      (add_pos_of_nonneg_of_pos (add_nonneg (ell_nonneg _) (ell_nonneg _)) (div_pos (ell_pos.mpr v) hL)) (ell_nonneg _)
  exact add_pos_of_nonneg_of_pos (add_nonneg (add_nonneg (ell_nonneg _) (ell_nonneg _)) (div_nonneg hb hL.le)) (ell_pos.mpr v)

lemma wins {p : Clip} {u a : ℝ} {H : Precision.Bed} (h : Floor H p f a u) (ha : 0 < a)
    (x : Y) (v : V) : reserve j a S.kernel.penalty * gain S x v ^ 2 ≤ baseline S H x x v v := by
  have he := strain S x v
  rw [baseline, real_count,real_count]
  apply le_trans _ (add_le_add (add_le_add ((show _ from (h.uniform.1 _).1)) le_rfl) le_rfl)
  rw [real_count]
  let k := S.kernel.penalty; let m := min a (min k 1)
  have hm : 0 < m := lt_min ha (lt_min S.kernel.penalty_pos zero_lt_one)
  have hj : 0 < yard j := yard_pos j
  have hu := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (positive_gain ..) he 2) (le_of_lt (reserve_pos j _ _ ha S.kernel.penalty_pos))
  refine hu.trans ?_
  let E := ell2 (D*ᵥ x); let N := ell2 (M*ᵥ x-d'*ᵥ v); let z := ell2 (tariff S x v)
  change m / (3*yard j^2)*(yard j*(E+N+z))^2 ≤ a*E^2 + k*N^2+z^2
  calc
    _ = m*((E+N+z)^2/3) := by field_simp
    _ ≤ m*(E^2+N^2+z^2) := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (E-N),sq_nonneg (E-z),sq_nonneg (z-N)]) hm.le
    _ ≤ _ := by
      simp_rw [mul_add]; apply add_le_add
      · apply add_le_add (mul_le_mul_of_nonneg_right (min_le_left ..) (sq_nonneg _)); exact mul_le_mul_of_nonneg_right
          ((min_le_right ..).trans (min_le_left ..)) (sq_nonneg _)
      exact mul_le_of_le_one_left (sq_nonneg _) ((min_le_right ..).trans (min_le_right ..))
end YM.AnalyticNext.QuarticMatch.Hessian
