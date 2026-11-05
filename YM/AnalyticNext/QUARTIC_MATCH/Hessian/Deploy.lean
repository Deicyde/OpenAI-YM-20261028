import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Grade
import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Real
import YM.Next.FREE_KERNELS.Amend

/-!
# Pre-L twist of the completed operator

Here ordinary real exponential weights on real centered joint Hessian with div-gauge
penalty. Keep the tilted argument of the rough variation as-is, bill quantitative
invertibility on the H¹ norm with its mass term. No determinant or loop expansion.
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
local notation "A" => form 0 f
local notation "V" => form 0 c
local notation "M" => Precision.mean S
local notation "j" => S.patch.J
local notation "k" => S.kernel.penalty

abbrev feeF {r : ℕ} (t : ℝ) (z : Site f) (a : form r f) := hood Prod.fst (t/L) z a
abbrev feeC {r : ℕ} (t : ℝ) (z : Site f) (a : form r c) := hood (locator S) (t/L) z a

lemma closedSign (t : ℝ) (z : Site f) {r : ℕ} (a : form r f) : feeF S t z (feeF S (-t) z a)=a := by unfold feeF; rw [neg_div]; exact hood_switch ..

lemma signed_dot (t : ℝ) (z : Site f) {r : ℕ} (a b : form r f) : dotProduct (feeF S t z a) (feeF S (-t) z b)=dotProduct a b := by unfold feeF; rw [neg_div,hood_dot]
lemma box_dot (t : ℝ) (z : Site f) {r : ℕ} (a b : form r c) : dotProduct (feeC S t z a) (feeC S (-t) z b)=dotProduct a b := by unfold feeC; rw [neg_div,hood_dot]
lemma fine_bill (t : ℝ) (z : Site f) {r : ℕ} (a b : form r f) (K : ℝ) :
    feeF S t z (a+K • b)=feeF S t z a+K • feeF S t z b := by funext i; simp [feeF,hood,mul_add,mul_left_comm]
lemma coarse_bill (t : ℝ) (z : Site f) {r : ℕ} (a b : form r c) :
    feeC S t z (a-b)=feeC S t z a-feeC S t z b := by funext i; simp [feeC,hood,mul_sub]

section fixed
variable {t η r : ℝ} (he : 0 < η) (hr : 0 ≤ r) (ht : |t| ≤ r*η) (hp : r ≤ 1)
include he hr ht hp

lemma on_fine {l m} (H : Matrix (Body l f) (Body m f) ℝ) (K : ℝ) (hk : 0 ≤ K)
    (h : Both Prod.fst Prod.fst H η K K) (z : Site f) (x : form m f) :
    ell2 (feeF S t z (H *ᵥ feeF S (-t) z x)-H*ᵥ x) ≤ (r/L*K) * ell2 x := by
  have hu : |t/L| ≤ (r/L)*η := by rw [abs_div, abs_of_pos (side_pos S.patch.L),div_mul_eq_mul_div]; gcongr
  unfold feeF; rw [neg_div,hit]
  exact shaded _ _ _ he.le (div_nonneg hr (side_pos S.patch.L).le) hu ((div_le_self hr (by exact_mod_cast S.patch.L.property)).trans hp) h (le_of_eq (pow_two _).symm) hk hk _ _
lemma digit (z : Site f) (x : Y) (v : V) :
    ell2 (feeF S t z (D*ᵥ feeF S (-t) z x)-D*ᵥ x) ≤ r*dc 1 η*gain S x v := by
  obtain ⟨hx,hh⟩ := both_axis 1 f he.le
  apply (on_fine S he hr ht hp D _ (dc_pos 1 η).le ⟨hx,hh⟩ z x).trans
  rw [show r/L*dc 1 η*ell2 x = r*dc 1 η*(ell2 x/L) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hr (dc_pos _ _).le)
  unfold gain; linarith [ell_nonneg v,ell_nonneg (D*ᵥ x),ell_nonneg ((d 0 f).transpose *ᵥ x)]
lemma shaft (z : Site f) (x : Y) (v : V) :
    ell2 (feeF S t z ((d 0 f).transpose *ᵥ feeF S (-t) z x)-(d 0 f).transpose *ᵥ x) ≤ r*dc 0 η*gain S x v := by
  obtain ⟨hx,hh⟩ := both_axis 0 f he.le
  apply (on_fine S he hr ht hp (d 0 f).transpose _ (dc_pos 0 η).le ⟨hh,by rw [transpose_transpose]; exact hx⟩ z x).trans
  rw [show r/L*dc 0 η*ell2 x = r*dc 0 η*(ell2 x/L) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hr (dc_pos _ _).le)
  unfold gain; linarith [ell_nonneg v,ell_nonneg (D*ᵥ x),ell_nonneg ((d 0 f).transpose *ᵥ x)]

lemma fiat (z : Site f) (x : Y) :
    ell2 (feeC S t z (M *ᵥ feeF S (-t) z x)-M*ᵥ x) ≤ r*(tagPrice j η/L)*ell2 x := by
  let T := tagPrice j η; let H := side_pos S.patch.L; let ht' := tp_pos j η
  unfold feeC feeF
  rw [neg_div,hit]; apply shaded _ _ _ (div_nonneg he.le H.le) hr ?_ hp (mean_price S he.le)
  · apply le_of_eq; field_simp
  · exact mul_nonneg ht'.le H.le
  · exact div_nonneg ht'.le H.le
  rw [abs_div,abs_of_pos H,← mul_div_assoc]; exact div_le_div_of_nonneg_right ht H.le

lemma await (z : Site f) (x : V) :
    ell2 (feeC S t z (d'*ᵥ feeC S (-t) z x)-d'*ᵥ x) ≤ r*dc 0 η*ell2 x := by
  have H := side_pos S.patch.L
  unfold feeC
  rw [neg_div,hit]; apply shaded _ _ _ (div_nonneg he.le H.le) hr ?_ hp (both_coarse S 0 he.le) (by rw [pow_two]) (dc_pos _ _).le (dc_pos _ _).le
  rw [abs_div,abs_of_pos H,← mul_div_assoc]; exact div_le_div_of_nonneg_right ht H.le

lemma arrival (z : Site f) (x : V) :
    ell2 (feeF S t z ((palette S).transpose*ᵥfeeC S (-t) z x)-(palette S).transpose*ᵥ x) ≤
      r*(tagPrice j η/L^2)*ell2 x := by
  have hx := palette_price S he.le; have H := side_pos S.patch.L; have ht' := tp_pos j η
  unfold feeC feeF; rw [neg_div,hit]; apply shaded _ _ _ (div_nonneg he.le H.le) hr ?_ hp ⟨hx.2, by rw [transpose_transpose]; exact hx.1⟩
  · apply le_of_eq; field_simp
  · exact mul_nonneg ht'.le (by positivity)
  · exact div_nonneg ht'.le (by positivity)
  rw [abs_div,abs_of_pos H,← mul_div_assoc]; exact div_le_div_of_nonneg_right ht H.le

def service (i : ℕ) (u : ℝ) := tagPrice i u+dc 0 u
lemma cloud (z : Site f) (x : Y) (v : V) :
    ell2 (feeC S t z (M*ᵥ feeF S (-t) z x-d'*ᵥ feeC S (-t) z v)-(M*ᵥ x-d'*ᵥ v)) ≤ r*service j η * gain S x v := by
  have H := side_pos S.patch.L; have ht' := tp_pos j η; have hu := dc_pos 0 η
  rw [coarse_bill S,sub_sub_sub_comm]
  apply ((ell_sub ..).trans (add_le_add (fiat S he hr ht hp z x) (await S he hr ht hp z v))).trans
  have ha := positive_gain S x v
  unfold service; rw [mul_add,add_mul]; apply add_le_add
  · rw [show r*(tagPrice j η/L)*ell2 x=r*tagPrice j η*(ell2 x/L) by ring]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    unfold gain; linarith [ell_nonneg v,ell_nonneg (D*ᵥ x),ell_nonneg ((d 0 f).transpose *ᵥ x)]
  apply mul_le_mul_of_nonneg_left _ (by positivity); unfold gain
  linarith [div_nonneg (ell_nonneg x) H.le,ell_nonneg (D*ᵥ x),ell_nonneg ((d 0 f).transpose *ᵥ x)]

lemma clip (z : Site f) (x : Y) (v : V) :
    ell2 (feeF S t z (tariff S (feeF S (-t) z x) (feeC S (-t) z v))-tariff S x v) ≤ r*service j η * gain S x v := by
  have H := side_pos S.patch.L
  have hs := tp_pos j η
  rw [tariff,tariff,fine_bill,add_sub_add_comm,← smul_sub]
  apply (ell_tri ..).trans; rw [ell_smul,Real.norm_of_nonneg (sq_nonneg _)]
  apply (add_le_add (shaft S he hr ht hp z x v) ((mul_le_mul_of_nonneg_left (arrival S he hr ht hp z v) (sq_nonneg L)))).trans
  unfold service
  rw [show (L^2)*(r*(tagPrice j η/L^2)*ell2 v) = r*tagPrice j η*ell2 v by field_simp]
  rw [add_comm (tagPrice j η),mul_add,add_mul]; apply add_le_add le_rfl; apply mul_le_mul_of_nonneg_left _ (by positivity);
  unfold gain; linarith [ell_nonneg (D*ᵥ x),ell_nonneg ((d 0 f).transpose *ᵥ x),div_nonneg (ell_nonneg x) H.le]
end fixed

lemma fare_clip {η : ℝ} (he : 0 ≤ η) (x : Y) (v : V) : ell2 (M*ᵥ x-d'*ᵥ v) ≤ (1+dc 0 η)*gain S x v := by
  have hv : ell2 (d'*ᵥ v) ≤ dc 0 η * ell2 v := original _ _ _ he (both_axis 0 c he) (le_of_eq (pow_two _).symm) (dc_pos _ _).le (dc_pos _ _).le v
  have hx : ell2 (M*ᵥ x) ≤ ell2 x/L := by
    rw [← offer_ell,offer_mat,← offer_ell x]; exact (fraction ..).trans_eq (inv_mul_eq_div ..)
  apply ((ell_sub ..).trans (add_le_add hx hv)).trans
  have h := dc_pos 0 η
  have ht := ell_nonneg (D*ᵥ x)
  have hu := ell_nonneg ((d 0 f).transpose *ᵥ x)
  rw [add_mul,one_mul]; apply add_le_add
  · unfold gain; linarith [ell_nonneg v]
  apply mul_le_mul_of_nonneg_left _ h.le; unfold gain; linarith [div_nonneg (ell_nonneg x) (side_pos S.patch.L).le]

section fc
variable {ι : Type*} [Fintype ι]
def repair (K C : ℝ) := K*C+(K+C)*K
lemma pair_off (a b x : ι→ℝ) {r K C l : ℝ} (hp : 0 ≤ r) (hu : r ≤ 1) (he : 0 ≤ K) (hc : 0 ≤ C) (hL : 0 ≤ l)
    (ha : ell2 (a-x) ≤ r*K*l) (hb : ell2 (b-x) ≤ r*K*l) (hh : ell2 x ≤ C*l) :
    |dotProduct a b-dotProduct x x| ≤ r*repair K C*l^2 := by
  have ht := ((ell_tri (b-x) x).trans (add_le_add hb hh)); rw [sub_add_cancel] at ht
  rw [show _-_ = dotProduct (a-x) b+dotProduct x (b-x) from by rw [sub_dotProduct, dotProduct_sub]; ring]
  refine (abs_add_le ..).trans (((add_le_add (norm_real_area ..) (norm_real_area ..)).trans
    (add_le_add (mul_le_mul ha (ht.trans (add_le_add (show r*K*l≤K*l from
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_left he hu) hL) le_rfl)) (ell_nonneg _) (by positivity))
      (mul_le_mul hh hb (ell_nonneg _) (mul_nonneg hc hL)))).trans_eq (by unfold repair; ring))


def rectify (K C : ℝ) := (1+K)*(1+K)*C+K*C*(1+K)+C*K
lemma unpair (x y v : ι→ℝ) (H Q : Matrix ι ι ℝ) {r K C l : ℝ} (hp : 0 ≤ r) (hu : r ≤ 1)
    (he : 0 ≤ K) (hc : 0 ≤ C) (hL : 0 ≤ l) (h : ∀ x, ell2 (H *ᵥ x) ≤ C*ell2 x)
    (hQ : ∀ x, ell2 (Q *ᵥ x-H*ᵥ x) ≤ r*C*ell2 x)
    (ha : ell2 (x-v) ≤ r*K*l) (hb : ell2 (y-v) ≤ r*K*l) (hh : ell2 v ≤ l) :
    |dotProduct x (Q*ᵥ y)-dotProduct v (H*ᵥ v)| ≤ r*rectify K C*l^2 := by
  have hi a (ha : ell2 (a-v) ≤ r*K*l) : ell2 a ≤ (1+K)*l := by
    have hv := ((ell_tri (a-v) v).trans (add_le_add ha hh)); rw [sub_add_cancel] at hv
    exact hv.trans ((add_le_add (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left he hu) hL) le_rfl).trans_eq (by ring))
  rw [show _-_ = dotProduct x (Q*ᵥ y-H*ᵥ y)+dotProduct (x-v) (H*ᵥ y) + dotProduct v (H*ᵥ (y-v)) from by
    rw [Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub,dotProduct_sub]; ring]
  apply ((abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)).trans
  apply (add_le_add
    (add_le_add ((norm_real_area ..).trans (mul_le_mul (hi x ha) ((hQ y).trans
      (mul_le_mul_of_nonneg_left (hi y hb) (by positivity))) (ell_nonneg _) (by positivity))) ((norm_real_area ..).trans
        (mul_le_mul ha ((h y).trans (mul_le_mul_of_nonneg_left (hi y hb) hc)) (ell_nonneg _) (by positivity))))
    ((norm_real_area ..).trans (mul_le_mul hh ((h _).trans (mul_le_mul_of_nonneg_left hb hc)) (ell_nonneg _) hL))).trans_eq
  unfold rectify; ring
end fc

end Tracks
end YM.AnalyticNext.QuarticMatch.Hessian
