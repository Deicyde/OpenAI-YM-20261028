import YM.Next.MULTISOURCE.Wage

/-!
# Automatically pay adjacent-scale factor from Tabs etc.
 No coupling, period or marker arguments in extra thresholds here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Wage
open RG Wilson Filter Function Finset Source Labels Mix Stock
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}

lemma ranges (h : G.Simple) (A : Levels G) : Tendsto A.clock.coverSize atTop atTop := by
  -- nat ceil
  have he := ((tendsto_pow_atTop (n:=2) (by decide : 2 ≠ 0)).comp (log_tend h A))
  apply tendsto_atTop.mpr; intro i
  filter_upwards [he.eventually_ge_atTop (i:ℝ)] with j hj
  exact_mod_cast (le_trans (show (i:ℝ) ≤ Real.log (A.clock.hatBeta j)^2 from hj) (Nat.le_ceil _))

lemma log_next_le (h : G.Simple) (A : Levels G) (H : Tabs A) : ∀ᶠ i in atTop,
    Real.log (A.clock.hatBeta (i+1)) ≤ 2*Real.log (A.clock.hatBeta i) := by
  let f (i) := Real.log (A.clock.hatBeta i)
  have hf : Tendsto f atTop atTop := log_tend h A
  filter_upwards [hf.eventually_ge_atTop 1] with i hi
  have hK : ((A.clock.coverSize (i+1):ℝ))^2 ≤2*(A.clock.coverSize i:ℝ)^2 := by exact_mod_cast H.grows i
  have hn : f (i+1)^2 ≤ (A.clock.coverSize (i+1):ℝ) := Nat.le_ceil _
  have hu : (A.clock.coverSize i:ℝ) ≤ f i^2+1 := (Nat.ceil_lt_add_one (sq_nonneg (f i))).le
  have he : 0 ≤ (A.clock.coverSize i:ℝ) := by positivity
  have hs : (A.clock.coverSize (i+1):ℝ) ≤ 2*A.clock.coverSize i := by nlinarith
  change f _ ≤ 2*f _; nlinarith

private lemma growingL (A : Levels G) (i : ℕ) : (1:ℝ) < (A.S.block i).val := by
  exact_mod_cast (lt_of_lt_of_le (by norm_num) (A.S.block_large i) : 1 < (A.S.block i).val)

private lemma cheap_column (A : Levels G) (i : ℕ) :
    Real.log (A.params (i+1)).columns ≤ Real.log (A.S.block i).val := by
  let X := A.params (i+1)
  have h := A.fits.logCost i
  have hL := Real.log_pos (growingL A i)
  have ht : Real.log X.columns ≤
          Real.log (1 + X.paths + X.width⁻¹ + X.columns + X.clip.relaxation + X.supportExponent) :=
        Real.log_le_log (lt_of_lt_of_le zero_lt_one X.columns_ge) (by
          linarith only [X.paths_pos, (inv_pos.mpr X.width_pos), X.clip.radius_pos, X.price_pos])
  refine ht.trans ((div_le_iff₀ hL).mp h |>.trans (mul_le_of_le_one_left hL.le (inv_le_one_of_one_le₀ ?_)))
  have hx : (1:ℝ) ≤ A.clock.J (i+1) := by exact_mod_cast (le_trans (by norm_num : 1≤4) (A.clock.adm (i+1)))
  exact one_le_pow₀ hx

open Vac in
lemma pays_length (h : G.Simple) (A : Levels G) (H : Tabs A) : ∀ᶠ i in atTop,
    ((A.S.block i).val:ℝ) ≤ A.clock.hatBeta (i+1) := by
  have he (i) : 1 ≤ fiat G (A.params i) (A.clock.hatBeta i) := by
    unfold fiat
    have he := (A.params i).paths_pos
    have hx := (A.params i).clip.quadratic_pos
    have hp := Real.log_pos (A.fits.delayed i)
    have hf : 0 ≤ (Fintype.card Lattice.PlaqAxes:ℝ)* ((A.params i).clip.direct + (A.params i).paths^2)+
        4*Module.finrank ℝ G.Mat * (Real.log 16+Real.log (A.clock.hatBeta i)/2) := by positivity
    linarith
  have hs := Gauge.slopeConstant_pos h
  filter_upwards [H.cheap G.slopeConstant hs] with i hi
  let L := (A.S.block i).val
  have hn : (1:ℝ) ≤ A.clock.coverSize i := by exact_mod_cast (A.budget i).B_pos
  have ha : 1 < (L:ℝ) := growingL ..
  refine le_trans ?_ (hi.trans (le_add_of_nonneg_left A.clock.bar_pos.le))
  calc
    (L:ℝ) ≤ (L:ℝ)^4 := by
      conv_lhs => rw [← pow_one (L:ℝ)]
      gcongr <;> first | exact ha.le | decide
    _ ≤ ((L:ℝ)*(A.clock.coverSize i:ℝ)^2)^4 := pow_le_pow_left₀ (by positivity)
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hn)) _
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (he _)

lemma feasible (C : Family G) (h : G.Simple) (ht : Tabs C.path.levels) (k d : ℕ) :
    ∀ᶠ j in atTop, width C 1 k j * ((C.S.block j).val:ℝ)^d * Real.exp ((C.path.levels.clock.coverSize j:ℝ)/256)
        /width C 1 k (j+1) ≤ Real.exp ((C.path.levels.clock.coverSize j:ℝ)/64) := by
  let A := C.path.levels
  let B := A.clock.coverSize
  let L i : ℝ := (A.S.block i).val
  let u i := (A.params i).columns
  let g := A.clock.hatCoupling
  let y i := Real.log (A.clock.hatBeta i)
  let F := width C 1 k
  let M : ℝ := (d:ℝ)+2+k
  have hm : 0 ≤ M := by unfold M; positivity
  filter_upwards [log_next_le h A ht,pays_length h A ht,(log_tend h A).eventually_ge_atTop (2*256*M)] with i Hi Hf hk
  have hl : 0 < L i := zero_lt_one.trans (growingL ..)
  have hw : Real.log (L i) ≤ y (i+1) := Real.log_le_log hl Hf
  have hu (i) : 1 ≤ u i := (A.params i).columns_ge
  have hh (i) := zero_lt_one.trans_le (hu i)
  have hg (i) : 0 < g i := (potential_hat ..).1
  have hy (i) : g i ≤ 1 := ((potential_hat ..).2).trans (A.budget _).threshold_le
  have hX (i) : tab C i > 0 := zero_lt_one.trans_le (tab_ge ..)
  have hp : Real.log (u (i+1)) ≤ y (i+1) := (cheap_column A i).trans hw
  have hb (i) : Real.log (F i) = (k:ℝ)*Real.log (g i) - (Real.log (u i)+Real.log (tab C i)) := by
    unfold F width; rw [canvas, Real.log_div (pow_pos (hg i) _).ne' (mul_pos (hh i) (hX i)).ne',Real.log_pow, Real.log_mul
      (hh i).ne' (hX i).ne']
  have hx : Real.log (F i)-Real.log (F (i+1)) ≤ ((2:ℝ)+k)*y (i+1) := by
    have ht : Real.log (g i) ≤ 0 := Real.log_nonpos (hg i).le (hy i)
    have hK : 0≤ Real.log (u i) := Real.log_nonneg (hu i)
    have hy : - Real.log (g (i+1))=y (i+1)/2 := by
      unfold g Calendar.hatCoupling; rw [Real.log_inv,neg_neg,Real.log_sqrt
        (zero_lt_one.trans (A.fits.delayed _)).le]
    have hi : Real.log (tab C (i+1))=Real.log (tab C i)+Real.log (u (i+1)) := by
      rw [show tab C (i+1)=tab C i*u (i+1) from Finset.prod_range_succ _ _]; exact Real.log_mul (hX _).ne' (hh _).ne'
    have hu : 0 ≤ k*y (i+1) := mul_nonneg (by positivity) (Real.log_pos (A.fits.delayed _)).le
    rw [hb,hb,hi]; nlinarith [mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ) ≤ k by positivity) ht]
  have hs : 0 < F i * L i^d * Real.exp ((B i:ℝ)/256) := mul_pos (mul_pos (width_positive ..) (pow_pos hl _))
    (Real.exp_pos _)
  change F i * L i^d * Real.exp ((B i:ℝ)/256)/ F _ ≤ Real.exp ((B i:ℝ)/64)
  rw [← Real.log_le_log_iff (div_pos hs (width_positive ..)) (Real.exp_pos _),
    Real.log_div hs.ne' (width_positive ..).ne', Real.log_mul (mul_pos (width_positive ..) (pow_pos hl _)).ne'
      (Real.exp_pos _).ne', Real.log_mul (width_positive ..).ne' (pow_pos hl _).ne',Real.log_pow, Real.log_exp, Real.log_exp]
  have hG : Real.log (F i) + ↑d * Real.log (L i)- Real.log (F (i+1)) ≤ 2*M*y i := by
    apply le_trans (b:= M*y (i+1))
    · unfold M; linarith only [hx, mul_le_mul_of_nonneg_left hw (show (0:ℝ) ≤ d by positivity)]
    exact (mul_le_mul_of_nonneg_left Hi hm).trans_eq (by unfold M y; ring)
  have hy : 0 ≤ y i := (Real.log_pos (A.fits.delayed i)).le
  have hω : 2*256*M ≤ y i := hk
  have hc : y i^2 ≤ B i := Nat.le_ceil _
  nlinarith
end YM.Multi.Wage
