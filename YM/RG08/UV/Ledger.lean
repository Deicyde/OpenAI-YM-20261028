import YM.RG08.UV.Costs
/-! # Triangular long iteration estimate. Polynomial in age with strict
margin ratio allows even the 1/4 exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice Laurent
open scoped Topology BigOperators
variable {S : Schedule} {i j k N : ℕ} {Z : ℝ}

private lemma av_m {Z : ℝ} (h : i ≤ j) : age S Z k j≤ age S Z k i+(S.scale j-S.scale i) := by
  unfold age; have ht:=abs_add_le (S.scale j-S.scale i) (S.scale i-S.scale k); rw [sub_add_sub_cancel,abs_of_nonneg (sub_nonneg.mpr (age_scale_mono S h))] at ht; linarith
private def vat (S : Schedule) (Z : ℝ) (k p i : ℕ) := age S Z k i+8*p
lemma inflate (h : 0≤Z) (hi : i≤j) (p : ℕ) :
    (vat S Z k p j)^p ≤ (vat S Z k p i)^p * Real.exp ((1/8:ℝ)*(S.scale j-S.scale i)) := by
  let c:ℝ:=p; let d:=S.scale j-S.scale i; let v:=vat S Z k p i
  have he : 0≤d:=sub_nonneg.mpr (age_scale_mono S hi)
  have hb : 1 ≤ v := (age_one h ..).trans (le_add_of_nonneg_right (by positivity)); have hv:= lt_of_lt_of_le zero_lt_one hb
  calc
    _ ≤ (v*(1+d/v))^p := by
      apply pow_le_pow_left₀ ((zero_le_one.trans (age_one h ..)).trans (le_add_of_nonneg_right (by positivity)))
      rw [mul_add,mul_one,mul_div_cancel₀ d hv.ne']; unfold v vat; have hx := av_m (S:=S) (Z:=Z) (k:=k) hi; unfold d; linarith
    _ ≤ v^p*Real.exp (d/v)^p := by
      rw [mul_pow]; have hg : 1+d/v ≤ Real.exp (d/v) := by simpa only [add_comm] using Real.add_one_le_exp (d/v)
      gcongr
    _ ≤ _ := by
      rw [← Real.exp_nat_mul]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply Real.exp_le_exp.mpr
      rw [← mul_div_assoc]; apply (div_le_iff₀ hv).2
      apply le_trans (b:=1/8*d*(8*(p:ℝ)))
      · exact le_of_eq (by ring)
      apply mul_le_mul_of_nonneg_left ?_ (by positivity); unfold v vat; linarith [age_one (S:=S) h k i]

def gammaR := Real.exp ((-1/8:ℝ)*Real.log 2)
lemma gamma_range : 0<gammaR ∧ gammaR<1 := ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by norm_num) (Real.log_pos (by norm_num:(1:ℝ)<2)))⟩
lemma downGill (i : ℕ) (S : Schedule) : Real.log 2 ≤ S.scale (i+1)-S.scale i := by
  have he:= S.block_large i
  rw [S.scale_succ, add_sub_cancel_left]; gcongr; exact_mod_cast (show 2 ≤ (S.block i).val by omega) -- 3<=...

lemma foothold (h : 0 ≤ Z) (p) {θ : ℝ} (hθ : θ≤1/4) :
    (vat S Z k p (i+1))^p * gain S θ (i+1) N * gain S (1/2) i (i+1) ≤
      gammaR * (vat S Z k p i)^p*gain S θ i N := by
  let d:= S.scale (i+1)-S.scale i
  have hv : Real.log 2≤d:= downGill i S
  have he : 0 < d := lt_of_lt_of_le (Real.log_pos (by norm_num)) hv
  let v:= vat S Z k p i; have hp : 0≤v:= by unfold v vat; linarith [age_one (S:=S) h k i,(show 0≤(p:ℝ) by positivity)]
  have H : Real.exp ((1/8)*d)*gain S (1/2) i (i+1) ≤ gammaR*gain S θ i (i+1) := by
    unfold gain gammaR; rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_le_exp.mpr
    change 1/8*d+ -(1/2)*d≤ _ + -θ*d; nlinarith
  calc
      _ ≤ v^p * Real.exp ((1/8)*d) * gain S θ (i+1) N * gain S (1/2) i (i+1) := by
         gcongr <;> first|exact (gain_pos ..).le|exact inflate h (Nat.le_succ _) p
      _ ≤ (v^p) * (gammaR*gain S θ i (i+1))*gain S θ (i+1) N := by rw [mul_right_comm _ (gain S θ (i+1) N),mul_assoc (v^p)]; gcongr; exact (gain_pos ..).le
      _ = _ := by rw [gain_trans S θ i (i+1) N]; unfold v; ring

theorem solve_bed (θ : ℝ) (hθ : θ≤1/4) (A : ℝ) (hA : 0≤A) (p : ℕ) : ∃ D≥(0:ℝ),
    ∀ (S : Schedule) {Z : ℝ}, 0 ≤ Z → ∀ (ℓ N k : ℕ) (F : ℕ→ℝ→ Prop), ℓ≤N→
      (∀ i, ℓ ≤ i → i≤ N → ∀ v,F i v → ∀ w, v ≤ w → F i w) →
      F N (A*age S Z k N^p) →
      (∀ i, ℓ ≤ i → i<N → ∀ v,F (i+1) v → F i (v*gain S (1/2) i (i+1)+A*age S Z k i^p*gain S θ i N)) →
      ∀ i,ℓ ≤ i → i≤N → F i (D*age S Z k i^p* gain S θ i N) := by
  let B:= A/(1-gammaR); have hv := sub_pos.mpr gamma_range.2; have hp:0≤B:=by unfold B; positivity
  have hB : A=B*(1-gammaR) := Eq.symm (div_mul_cancel₀ _ hv.ne'); have hY : A≤ B:= by rw [hB]; nlinarith [gamma_range.1]
  let C := 1+(8:ℝ)*p; refine ⟨B*C^p,by unfold C; positivity,fun S Z hZ L N k F hP hh h hF i hL hi=>?_⟩
  let G := gain S θ; let v := vat S Z k p; let y := age S Z k
  have hc i : y i ≤ v i := le_add_of_nonneg_right (by positivity)
  have hm i : 0≤ y i := zero_le_one.trans (age_one hZ k i)
  have he i (hi:L ≤ i) (ha:i≤N) : F i (B*v i^p * G i N) := by -- hi : L ≤ i
     induction ha using Nat.decreasingInduction with
     | self=> rw [show G N N=1 from gain_zero ..,mul_one]
              apply hh _ hi le_rfl _ h; gcongr <;> first|exact hc _|exact pow_nonneg (hm _) _|exact hm _
     | of_succ i ht IH =>
       refine hh i hi ht.le _ (hF _ hi ht _ (IH (hi.trans (Nat.le_succ _)))) _ ?_
       calc
          _ ≤ B* (gammaR * v i^p * G i N) + A*v i^p * G i N := by
            refine add_le_add ?_ ?_
            · rw [mul_assoc B,mul_assoc B]; exact mul_le_mul_of_nonneg_left (foothold hZ _ hθ) hp
            gcongr <;> first|exact (gain_pos ..).le|exact hm _|exact hc _
          _ = _ := by rw [hB]; ring
  refine hh i hL hi _ (he i hL hi) _ ?_
  have hu : v i ≤ C*y i := by unfold C v vat; change y i+_≤_; nlinarith [show 0≤(p:ℝ) by positivity,show 1≤y i from age_one hZ ..]
  rw [mul_assoc B (C^p),← mul_pow]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ((hm i).trans (hc i)) hu _) hp) (gain_pos ..).le
end YM.RG08
