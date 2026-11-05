import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Deploy
import YM.Next.SCHEDULE.Chorus
import YM.Next.SCHEDULE.Circuit
import YM.Work.F05.Measure

/-!
# Traveling Hessian estimates

An arbitrary mesh, pre-L gap and tilted estimate. Feed color purchase and
true cubic-rough-legged invoice. No limit assertion for Green functions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Hessian
open Filter Function Lattice Laurent Bloch Exterior Matrix Precision RG Work.F06
open Pre.Centered YM.Next.Free YM.Progress.StationaryScenes Wilson
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ComplexConjugate InnerProductSpace
namespace Tracks
open Green (Rows Both wt)
variable {c f : Side} (S : StepData c f)
local notation "L" => (S.patch.L.val:ℝ)
local notation "D" => d 1 f
local notation "d₀" => d 0 f
local notation "d'" => d 0 c
local notation "Y" => form 1 f
local notation "V" => form 0 c
local notation "M" => Precision.mean S
local notation "j" => S.patch.J
local notation "k" => S.kernel.penalty

section toll
def partsK (C : ℝ) := max 1 ((Fintype.card (TypeFace 2):ℝ)*C)
lemma partsK_pos (C : ℝ) : 0 < partsK C := lt_of_lt_of_le one_pos (le_max_left ..)

def scheme (i : ℕ) (η C κ : ℝ) := rectify (dc 1 η) (partsK C) + κ * repair (service i η) (1+dc 0 η) + repair (service i η) 1

def chamberCost (i : ℕ) (η C κ : ℝ) := max 1 (scheme i η C κ)
lemma chamberCost_pos (i : ℕ) (η C κ : ℝ) : 0 < chamberCost i η C κ := lt_of_lt_of_le one_pos (le_max_left ..)
def exponent (i : ℕ) (a η C κ : ℝ) := min 1 (reserve i a κ / (2*chamberCost i η C κ))
def purchase (i : ℕ) (a η C κ : ℝ) := exponent i a η C κ*η
lemma purchase_pos (i : ℕ) {a η : ℝ} (ha : 0 < a) (he : 0<η) (C : ℝ) {κ : ℝ} (hk : 0<κ) :
    0 < purchase i a η C κ := mul_pos (lt_min one_pos (div_pos (reserve_pos i _ _ ha hk)
      (mul_pos two_pos (chamberCost_pos ..)))) he
end toll
variable {t r η C a u : ℝ} {H : Bed} {p : Clip} (he : 0<η) (h : H.metric.strip η C)
include he h
lemma total_shift (hr : 0 ≤ r) (ht : |t| ≤ r*η) (hp : r ≤ 1) (z : Site f) (x : Y) (v : V) :
    |baseline S H (feeF S (-t) z x) (feeF S t z x) (feeC S (-t) z v) (feeC S t z v) - baseline S H x x v v| ≤
      r*chamberCost j η C k * gain S x v^2 := by
  let N := gain S x v; let K := H.metric.acts f; let u := dc 1 η
  have hc : 0 ≤ partsK C := (partsK_pos _).le
  have hK : Both Prod.fst Prod.fst K η (partsK C) (partsK C) :=
    ⟨fun i => ((Green.periodic H.metric f he.le h).1 i).trans (le_max_right ..),
      fun i => ((Green.periodic H.metric f he.le h).2 i).trans (le_max_right ..)⟩
  let A := feeF S (-t) z x; let B := feeF S t z x; let X := feeC S (-t) z v; let W := feeC S t z v
  have hn : |-t| ≤ r*η := (abs_neg _).trans_le ht
  have hv : 0 ≤ N := positive_gain ..; let w := service j η
  have hP : 0 ≤ w := add_nonneg (tp_pos _ _).le (dc_pos _ _).le
  have Ht : 0 ≤ u := (dc_pos ..).le; have h₀ := dc_pos 0 η; have hL := side_pos S.patch.L
  let Θ := shade Prod.fst Prod.fst (-t/L) z K
  have hϕ y : ell2 (Θ*ᵥ y-K*ᵥ y) ≤ r*partsK C*ell2 y := by
    have hi := (on_fine S he hr hn hp K _ hc hK z y); unfold feeF at hi
    rw [show - -t / L = -(-t/L) from by ring,hit] at hi
    refine hi.trans ?_; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (div_le_self hr (by exact_mod_cast S.patch.L.property)) hc) (ell_nonneg _)
  have ht' : feeF S (-t) z (K*ᵥ(D*ᵥ B)) = Θ *ᵥ feeF S (-t) z (D*ᵥ B) := by
    have hh (a : form 2 f) : feeF S (-t) z (K*ᵥ feeF S t z a)=Θ*ᵥ a := by
      unfold feeF Θ
      rw [neg_div,← hit,neg_neg]
    rw [← hh,closedSign]
  have hi : |dotProduct (D*ᵥ A) (K*ᵥ (D*ᵥ B))-dotProduct (D*ᵥ x) (K*ᵥ (D*ᵥ x))| ≤ r*rectify u (partsK C)*N^2 := by
    rw [← signed_dot S t z (D*ᵥ A), ht']
    apply unpair _ _ _ _ _ hr hp Ht hc hv (original _ _ _ he.le hK (by rw [pow_two]) hc hc) hϕ (digit S he hr ht hp z x v)
    · simpa only [neg_neg,B] using digit S he hr hn hp z x v
    unfold N gain; linarith [ell_nonneg v,ell_nonneg (d₀ᵀ*ᵥ x),div_nonneg (ell_nonneg x) hL.le]
  have ha : |dotProduct (tariff S A X) (tariff S B W) - dotProduct (tariff S x v) (tariff S x v)| ≤ r*repair w 1*N^2 := by
    rw [← signed_dot S t z (tariff S A X)]
    apply pair_off _ _ _ hr hp hP zero_le_one hv (clip S he hr ht hp z x v)
    · simpa only [B,W,neg_neg] using clip S he hr hn hp z x v
    rw [one_mul]; exact tari ..
  let c₁ := dotProduct (M*ᵥ A-d'*ᵥ X) (M*ᵥ B-d'*ᵥ W); let c₂ := dotProduct (M*ᵥ x-d'*ᵥ v) (M*ᵥ x-d'*ᵥ v)
  have hb : |c₁-c₂| ≤ r*repair w (1+dc 0 η)*N^2 := by
    unfold c₁ c₂; rw [← box_dot S t z (M*ᵥ A-d'*ᵥ X)]
    apply pair_off _ _ _ hr hp hP (by positivity) hv (cloud S he hr ht hp z x v)
    · simpa only [B,W,neg_neg] using cloud S he hr hn hp z x v
    exact fare_clip S he.le x v
  have hd : |k*c₁-k*c₂| ≤ k*(r*repair w (1+dc 0 η)*N^2) := by
    rw [← mul_sub,abs_mul, abs_of_nonneg S.kernel.penalty_pos.le];
    exact mul_le_mul_of_nonneg_left hb S.kernel.penalty_pos.le
  unfold baseline
  apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right 1 (scheme j η C k)) hr) (sq_nonneg N))
  rw [add_sub_add_comm,add_sub_add_comm]
  apply ((abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)).trans
  exact (add_le_add (add_le_add hi hd) ha).trans_eq (show _ + _=r*scheme j η C k*N^2 by unfold scheme u w; ring)

lemma sojourn (ha : 0<a) (hF : Floor H p f a u) (ht : |t| ≤ purchase j a η C k)
    (z : Site f) (x : Y) (v : V) : reserve j a k / 2 * gain S x v^2 ≤
      baseline S H (feeF S (-t) z x) (feeF S t z x) (feeC S (-t) z v) (feeC S t z v) := by
  let α := reserve j a k; have ho : 0 < α := reserve_pos _ _ _ ha S.kernel.penalty_pos
  let r := exponent j a η C k; let K := chamberCost j η C k; have hk : 0 < K := chamberCost_pos ..
  have hr : 0 ≤ r := le_min zero_le_one (by change 0 ≤ α/(2*K); positivity)
  have hh := total_shift S he h hr ht (min_le_left ..) z x v
  have hb : r*K ≤ α/2 := by
    have hv := min_le_right 1 (α/(2*K)); have hh : r*(2*K) ≤ α := (le_div_iff₀ (by positivity : 0 < 2*K)).mp hv; linarith
  have hx := wins S hF ha x v; unfold α at hb; unfold K at hb
  have he := abs_le.mp (hh.trans (mul_le_mul_of_nonneg_right hb (sq_nonneg _))); linarith only [hx,he.1]
end Tracks
end YM.AnalyticNext.QuarticMatch.Hessian
