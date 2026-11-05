import YM.OPE.Columns.Accounts

/-!
# The low (at top) plane

Starting at the *bare* end. Show expansion on the coordinates of weight ≤ e under
transport, and the slower expansion bound on the space transverse to those. Not the
cone without unit, and not a new transfer omitting the nonlinear mixing. All these
comparisons use the *exact* representative in `Columns.Accounts`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter RG Wilson Lattice Labels Source MergeProof Bid Extra.Histories
open Push.Local Work.G08
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {d : ℕ}
namespace Columns
variable (F : Labels.Frame G d)

/-- Projection to columns of weight at most e. -/
def low (e : ℕ) : Module.End ℂ F.Coeff where
  toFun v i := if (F.grades i).1 ≤ e then v i else 0
  map_add' v u := by funext i; by_cases h : (F.grades i).1 ≤ e <;> simp [h]
  map_smul' c v := by funext i; by_cases h : (F.grades i).1 ≤ e <;> simp [h]

local notation "μ" => F.coeffSize
variable (e : ℕ)
local notation "P" => low F e

@[simp] lemma low_apply (x : F.Coeff) (i) : low F e x i = if (F.grades i).1 ≤ e then x i else 0 := rfl
lemma project (x : F.Coeff) : P (P x) = P x := by
  ext i; by_cases h : (F.grades i).1 ≤ e <;> simp [h]
lemma size_low (x : F.Coeff) : μ (P x) ≤ μ x :=
    Finset.sum_le_sum fun i _ => by by_cases h : (F.grades i).1 ≤ e <;> simp [low_apply,h]
lemma size_rest (x : F.Coeff) : μ (x-P x) ≤ μ x :=
    Finset.sum_le_sum fun i _ => by by_cases h : (F.grades i).1 ≤ e <;> simp [low_apply,h]

variable {F}
lemma triangular_high {B : F.Coeff →ₗ[ℂ] F.Coeff} {c : ℝ} (h : Leading B c) (x : F.Coeff)
    (hx : P x = 0) : P (B x) = 0 := by
  ext i; by_cases hi : (F.grades i).1 ≤ e
  swap; · simp [hi]
  rw [low_apply, if_pos hi, ← matrix_coeff]; apply Finset.sum_eq_zero
  intro j _; by_cases hh : (F.grades j).1 ≤ e
  · have hz : x j = 0 := by simpa only [low_apply, if_pos hh, Pi.zero_apply] using congr_fun hx j
    rw [hz, mul_zero]
  by_contra! hne
  obtain ⟨hne,-⟩ := mul_ne_zero_iff.mp hne
  have ht := h.triangular i j (fun he => hh (he.symm ▸ hi)) hne; omega

lemma inv_triangular_high {B : F.Coeff ≃ₗ[ℂ] F.Coeff} {c : ℝ}
    (h : Leading B.toLinearMap c) (x : F.Coeff) (hx : P x=0) : P (B.symm x)=0 := by
  let T := LinearMap.ker P
  let V : Module.End ℂ T := (B.toLinearMap.comp T.subtype).codRestrict _ fun y =>
    show P (B.toLinearMap y.val)=0 from triangular_high e h _ y.property
  have hV : Injective V := fun i j hij => Subtype.ext (B.injective (congr_arg Subtype.val hij))
  obtain ⟨y,hy⟩ := LinearMap.injective_iff_surjective.mp hV (⟨x,hx⟩:T)
  rw [show x = B y.val from Eq.symm (congr_arg Subtype.val hy), LinearEquiv.symm_apply_apply]
  exact y.property

lemma low_le {B : F.Coeff ≃ₗ[ℂ] F.Coeff} {c k : ℝ} (h : Leading B.toLinearMap c)
    (hk : ∀ y, μ (B.symm y) ≤ k*μ y) (x : F.Coeff) : μ (P x) ≤ k*μ (P (B x)) := by
  have he := inv_triangular_high e h (B x-P (B x)) (by rw [map_sub,project]; abel)
  rw [map_sub,map_sub,LinearEquiv.symm_apply_apply] at he
  rw [sub_eq_zero] at he
  exact le_trans (le_of_eq (congr_arg μ he)) ((size_low _ _ _).trans (hk _))

variable (F)
lemma vowel_expands (L : Side) (x : F.Coeff) :
    (L.val:ℝ)^(d-e)*μ (P x) ≤ μ (P (vowel F L x)) := by
  unfold Frame.coeffSize; rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : (F.grades i).1 ≤ e
  · simp only [low_apply,h, if_true,vowel,norm_mul,norm_pow,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by exact_mod_cast L.pos) (Nat.sub_le_sub_left h d)) (norm_nonneg _)
  simp [h]
lemma vowel_rest (L : Side) (x : F.Coeff) :
    μ (vowel F L x - P (vowel F L x)) ≤ (L.val:ℝ)^(d-(e+1))*μ x := by
  unfold Frame.coeffSize; rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : (F.grades i).1 ≤ e
  · simp only [Pi.sub_apply,low_apply,h,if_true,sub_self, norm_zero]; positivity
  simp only [Pi.sub_apply,low_apply,h,if_false,sub_zero,vowel,norm_mul,norm_pow,Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast L.pos) (by omega)) (norm_nonneg _)
lemma vowel_low_zero {L : Side} {x : F.Coeff} (h : P x=0) : P (vowel F L x) = 0 := by
  ext i; by_cases hi : (F.grades i).1 ≤ e
  · have hx : x i = 0 := by simpa only [low_apply, if_pos hi, Pi.zero_apply] using congr_fun h i
    simp [hi,vowel,hx]
  simp [hi]
lemma size_sub (x y : F.Coeff) : μ (x-y) ≤ μ x + μ y := by
  unfold Frame.coeffSize; rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => norm_sub_le (x i) (y i)

variable {W : Worth} {H : History G}
lemma room (hc : roomCost H.levels W) (i j : ℕ) (h : j ≤ H.levels.clock.J i + 1) :
    64* (W.K j)^2 ≤ (H.levels.params i).columns := by
  have he : (W.K j)^2 ≤ W.K (H.levels.clock.J i + 1)^2 :=
    pow_le_pow_left₀ (zero_le_one.trans (W.prices _)) (W.growth h) _
  exact (mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ 64 from by norm_num)).trans (hc i)

variable {e F} (hc : roomCost H.levels W) (hb : Bank W H.levels) {i : ℕ} {x y : F.Coeff → F.Coeff}
    (hT : Triangle H W i x y) (v : F.Coeff)
set_option quotPrecheck false
local notation "L" => H.S.block i
local notation "K" => W.K (H.levels.clock.J (i+1))
local notation "s₀" => (H.levels.params i).columns
local notation "s" => (H.levels.params (i+1)).columns

include hb
lemma ε_small : 0 ≤ barunit L ∧ 2*K*barunit L*(1+s) ≤ 1 :=
  bank_slack (W.prices _) (W.growth (Nat.le_add_right ..)) (H.levels.params _).columns_ge (hb i)
lemma column_small : s ≤ ((L).val:ℝ) := by
  have hk := hb i
  change 100000*(W.K _)^6*(1+s)^2 ≤ _ at hk
  have hx := one_le_pow₀ (n:=6) (W.prices (H.levels.clock.J (i+1)+1))
  have hg := (H.levels.params (i+1)).columns_ge
  exact le_trans ((show s ≤ 100000*(W.K _)^6*(1+s)^2 from
    by nlinarith only [hg,hx,mul_le_mul_of_nonneg_right hx (sq_nonneg (1+s))]).trans hk)
    (Real.rpow_le_self_of_one_le (by exact_mod_cast (L).pos) (by norm_num))
include hc hT
lemma step_expand (h : μ (x v) ≤ s * μ (P (x v))) (he : e < d) :
    μ (y v) ≤ s₀ * μ (P (y v)) ∧ ((L).val:ℝ)^(d-e) * μ (P (x v)) ≤ s * μ (P (y v)) := by
  have hs₀ := room hc i _ (H.levels.fits.stepSlow i)
  have hs : 64*K^2 ≤ s := room hc (i+1) _ (Nat.le_add_right ..)
  have hb' : s ≤ ((L).val:ℝ) := column_small hb
  have hh' : (1:ℝ) ≤ (L).val := by exact_mod_cast (L).pos
  obtain ⟨q,⟨c,hq⟩,hv,hε⟩ := hT.leads
  let a:=x v; let b:= y v; let D:=vowel F L a; let Y:=μ (P D)
  have hY: ((L).val:ℝ)^(d-e)*μ (P a) ≤ Y := vowel_expands F e L a
  have hD : μ D ≤ 2*Y := calc
    _ ≤ Y+ μ (D-P D) := size_triangle F D _
    _ ≤ Y + ((L).val:ℝ)^(d-(e+1))* (s*μ (P a)) := add_le_add le_rfl
        ((vowel_rest F e L a).trans (mul_le_mul_of_nonneg_left h (by positivity)))
    _ ≤ Y + Y := by
      apply add_le_add le_rfl
      rw [← mul_assoc]; apply le_trans _ hY
      apply mul_le_mul_of_nonneg_right _ (size_nonneg F _)
      rw [show d-e = d-(e+1)+1 from by omega,pow_succ]; gcongr
    _ = 2*Y := (two_mul _).symm
  have hp : μ a ≤ s*Y := h.trans (mul_le_mul_of_nonneg_left (((size_vowel F L (P a)).1).trans_eq
    (congr_arg μ (by
      ext i; by_cases h : (F.grades i).1 ≤ e <;> simp [D, low_apply, vowel, h]))) (zero_le_one.trans (H.levels.params _).columns_ge))
  have hk : 1 ≤ K := W.prices _; have hx := ε_small hb (i:=i); have hk₀ : 0 ≤ K := zero_le_one.trans hk
  have hz : 0 ≤ Y := size_nonneg F _
  have hu : 2*K * μ (b - q.map D) ≤ Y := calc
      _ ≤ 2*K*(barunit L * μ (F.core a)) := mul_le_mul_of_nonneg_left (hε v) (by positivity)
      _ ≤ 2*K*(barunit L * ((1+s)*Y)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((size_core F _).trans (hp.trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hz))) hx.1) (by positivity)
      _ ≤ Y := by rw [← mul_assoc, ← mul_assoc];
                  exact mul_le_of_le_one_left hz hx.2
  have ht : Y ≤ 2*K * μ (P b) := by
    have ht' : Y ≤ K* (μ (P b)+μ (b-q.map D)):= calc
      _ ≤ K*μ (P (q.map D)) := low_le e hq (fun v=> (hv v).2) D
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hk₀; apply (size_triangle F _ (P b)).trans
        rw [size_sub_rev F (P (q.map D)) (P b),← map_sub]
        exact add_le_add le_rfl (size_low ..)
    linarith only [hu,ht']
  have hs' : μ (b-q.map D) ≤ K*Y:=
    ((le_mul_of_one_le_left (size_nonneg F _) (show 1 ≤ 2*K from by linarith only [hk])).trans hu).trans
      (le_mul_of_one_le_left hz hk)
  have hs'' : μ b ≤ K*(2*Y) + K*Y :=
    (size_triangle F b (q.map D)).trans (add_le_add ((hv D).1.trans (mul_le_mul_of_nonneg_left hD hk₀)) hs')
  refine ⟨?_, hY.trans (ht.trans (mul_le_mul_of_nonneg_right ?_ (size_nonneg F _)))⟩
  · have hx : (3*K)*(2*K) ≤ s₀ := by nlinarith only [hs₀,sq_nonneg K]
    calc
      _ ≤ 3*K*Y := hs''.trans_eq (by ring)
      _ ≤ 3*K*(2*K*μ (P b)) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hx (size_nonneg F _)
  nlinarith only [hk,hs]

lemma step_transverse (h : P (x v) = 0) :
    μ (y v) ≤ s * (((L).val:ℝ)^(d-(e+1)) * μ (x v)) := by
  let D := vowel F L (x v)
  obtain ⟨q,hHead,hQ,hv⟩ := hT.leads -- do not shadow H
  have ht : μ D ≤ ((L).val:ℝ)^(d-(e+1))*μ (x v) := by
    have ht' := vowel_rest F e L (x v)
    rw [vowel_low_zero F e h,sub_zero] at ht'; exact ht'
  have hs : 64*K^2 ≤ s := room hc (i+1) _ (Nat.le_add_right ..)
  have hk : 1 ≤ K := W.prices _
  have hg := ε_small hb (i:=i)
  have hz := (H.levels.params (i+1)).columns_ge
  have hx : barunit L ≤ 1 := le_trans (le_mul_of_one_le_left hg.1 (by linarith only [hk] : 1 ≤ 2*K)) ((le_mul_of_one_le_right (show 0 ≤ 2*K*barunit L from mul_nonneg (by linarith only [hk]) hg.1) (show 1 ≤ 1+s by linarith only [hz])).trans hg.2)
  have hw : μ (y v - q.map D) ≤ μ D := calc
    _ ≤ barunit L*μ (F.core (x v)) := hv v
    _ ≤ μ (F.core (x v)) := mul_le_of_le_one_left (size_nonneg F _) hx
    _ ≤ μ (x v) := size_core F (x v)
    _ ≤ _ := (size_vowel F L _).1
  calc
    _ ≤ K*μ D + μ D := (size_triangle F _ (q.map D)).trans (add_le_add (hQ D).1 hw)
    _ ≤ s * μ D := by
      rw [show K*μ D+μ D = (K+1)*μ D from by ring]; exact mul_le_mul_of_nonneg_right (by nlinarith only [hs,hk]) (size_nonneg F _)
    _ ≤ _ := mul_le_mul_of_nonneg_left ht (zero_le_one.trans hz)
end Columns
end YM.OPE
