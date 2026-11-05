import YM.Further.CURVED_GAUSSIAN_JETS.Passengers
import YM.Further.CURVED_GAUSSIAN_JETS.Zones

/-!
# Counting absolute hit costs of the true ordered position-address envelopes

For determinant terms (post the absolutely convergent u integral) and
quadratic inverse-precision amplitudes, including if one wants square roots
before spending. Output halo currency (`coverNumber`), enough for an
arbitrary fixed support exponent after L and increasing delay, even if the
matrix block lives on an eligible subset of columns and depends on the
whole sector. For aggregation over changing sectors one should use the
full-key universe and insert zeros for missing addresses (show that the
complete decision data including any queries not present in the numerical
formula fit in the PAID halos!). Not pricing sums of probabilities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Tracks
open Matrix Function Filter Jets Lattice Wilson RG Precision Push.Uniform SectorNext.Vacuum
open scoped BigOperators Classical Topology ContDiff
variable {I : Type*} [Fintype I] {c f : Side} {a : I → Site f} {b : I → Site c} {d m N D L e : ℕ} {R K σ : ℝ} {P : Prices}

lemma decay_sum (i : I) (d : ℕ) (ha : Multiplicity a L) (h : 0<R) : ∑ z : Fin d → I, decay a R (p:=Fin.cons i z) ≤ ((L:ℝ)*countCost R)^d := by
  induction d generalizing i with
  | zero => simp [decay,fare]
  | succ d ih => rw [all_trips]; simp only [decay_cons,Fin.tail_cons,Fin.cons_zero, ←Finset.mul_sum]
                 exact ((Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (decay_pos ..).le).trans_eq (Finset.sum_mul ..).symm).trans ((mul_le_mul_of_nonneg_right (ha.count a h (a i)) (by have := count_pos h; positivity)).trans_eq (pow_succ' ..).symm)

def volumeCost (m D N : ℕ) : ℝ := ((m*N+m*N+1:ℕ)^4 *D : ℕ)
def mapCost (R σ : ℝ) (m L : ℕ) := (2:ℝ)^4 * Real.exp (σ*((m+m+1:ℕ):ℝ)^4) * (1+(L:ℝ)*countCost R)
lemma map_ge (hs : 0≤σ) (hr : 0<R) : 1 ≤ mapCost R σ m L := by
  have h := count_pos hr
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) (Real.one_le_exp (by positivity))) (le_add_of_nonneg_right (by positivity))

def meter (b : I → Site c) (σ : ℝ) (m N : ℕ) (x : Site c) (E : Run I d → ℝ) := ∑ p : Run I d, if Hops b (m*N) p ∧ x∈dots b (m*N) p then Real.exp (σ * coverNumber N (dots b (m*N) p)) * E p else 0
lemma meter_mul (x : Site c) (E : Run I d → ℝ) (y : ℝ) : meter b σ m N x (fun p=> y * E p) = y * meter b σ m N x E := by
  unfold meter; rw [Finset.mul_sum]; simp only [mul_ite,mul_zero,mul_left_comm y]


lemma volume_price (hm : Multiplicity b D) (x : Site c) : ((disk b x ((d+1)*(m*N))).card:ℝ) ≤ volumeCost m D N*((2:ℝ)^4)^(d+1) := by
  let a := m*N
  have he : ((d+1)*a+(d+1)*a+1) ≤ 2^(d+1)*(a+a+1) := calc
    _ ≤ (d+1)*(a+a+1) := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
  have h := (size_disk x ((d+1)*a) hm).trans (Nat.mul_le_mul_right _ (pow_le_pow_left' he _))
  have hg : ((disk b x ((d+1)*a)).card:ℝ) ≤ ((2^(d+1))*(a+a+1:ℝ))^4 * D := by exact_mod_cast h
  rw [mul_pow] at hg; exact hg.trans_eq (by unfold volumeCost a; push_cast; rw [←pow_mul, Nat.mul_comm (d+1), pow_mul]; ring)

lemma sum_meter (ha : Multiplicity a L) (hb : Multiplicity b D) (hN : 0<N) (hr : 0<R) (hs : 0 ≤ σ) (x : Site c) : meter b σ m N x (decay a R (d:=d)) ≤ volumeCost m D N * mapCost R σ m L^(d+1) := by
  let E := Real.exp (σ*((m+m+1:ℕ):ℝ)^4)
  let C := volumeCost m D N
  let B := disk b x ((d+1)*(m*N))
  let H : ℝ := L*countCost R; have hH : 0≤H := by have := count_pos hr; unfold H; positivity
  have he (p : Run I d) (ht : Hops b (m*N) p) : Real.exp (σ * coverNumber N (dots b (m*N) p)) ≤ E^(d+1) := by
    unfold E; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; apply le_trans (mul_le_mul_of_nonneg_left (c:=((d+1:ℕ):ℝ)*((m+m+1:ℕ):ℝ)^4) (by exact_mod_cast ht.sum_tiles hN) hs); exact le_of_eq (by ring)
  unfold meter
  rw [all_trips]
  calc
    _ ≤ ∑ i : I, if i∈B then E^(d+1) * ∑ z : Fin d→I, decay a R (Fin.cons i z) else 0 := by
      refine Finset.sum_le_sum fun i _=>?_ ; split_ifs with hh
      · rw [Finset.mul_sum]; refine Finset.sum_le_sum fun p _=>?_ ; split_ifs with hp; exact mul_le_mul_of_nonneg_right (he _ hp.1) (decay_strict _).le; exact mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (decay_strict _).le
      exact Finset.sum_nonpos fun z _=> by rw [if_neg (fun h => hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1.reaches h.2⟩))]
    _ ≤ ∑ i∈ B,E^(d+1) * H^d := by rw [←Finset.sum_filter]; simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]; exact Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (decay_sum i d ha hr) (pow_nonneg (Real.exp_pos _).le _)
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]; refine (mul_le_mul (volume_price hb x) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH (le_add_of_nonneg_left zero_le_one) _) (pow_nonneg (Real.exp_pos _).le _)) (show 0 ≤ E^(d+1)*H^d by unfold E; positivity) (show 0≤ C*(2^4:ℝ)^(d+1) by unfold C volumeCost; positivity)).trans ?_
      have hc : 0≤C := by unfold C volumeCost; positivity
      calc
        _ ≤ C*(2^4:ℝ)^(d+1)*(E^(d+1)*(1+H)^(d+1)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right hH) (Nat.le_succ d)) (pow_nonneg (Real.exp_pos _).le _)) (by positivity)
        _ = _ := by unfold C H E mapCost; simp only [mul_pow]; ring

def envelope (a : I → Site f) (R K : ℝ) (N d : ℕ) (p : Run I e) := K^e * Real.exp (-R*N)^(d+1)*decay a R p
lemma envelope_ge (hK : 0 ≤ K) (p : Run I e) : 0 ≤ envelope a R K N d p := by have := decay_strict (R:=R) (a:=a) p; unfold envelope; positivity
omit [Fintype I] in
lemma envelope_ticket (p : Run I e) : envelope a (spare P) K N d p = ticket a P K N d p := rfl
lemma half_envelope (h : 0≤K) (p : Run I e) : Real.sqrt (envelope a R K N d p) = envelope a (R/2) (Real.sqrt K) N d p := by
  have h₁ : (Real.exp (-(R/2)*N))^2=Real.exp (-R*N) := by rw [sq,←Real.exp_add]; congr 1; ring
  apply (Real.sqrt_eq_iff_mul_self_eq (envelope_ge h _) (envelope_ge (Real.sqrt_nonneg _) _)).mpr; unfold envelope; conv_rhs => rw [←sq, mul_pow,mul_pow, ←pow_mul, Nat.mul_comm e, pow_mul, ←pow_mul (Real.exp _), Nat.mul_comm (d+1), pow_mul, Real.sq_sqrt h,h₁]
  rw [decay_twice (R:=R),sq]


omit [Fintype I] in
lemma paid_meter (m L : ℕ) (hr : 0<R) (hs : 0 ≤ σ) (hK : 1 ≤ K) : ∀ᶠ N : ℕ in atTop, ∀ {f c : Side} {I : Type*} [Fintype I] (a : I → Site f) (b : I → Site c) {D d e : ℕ}, Multiplicity a L → Multiplicity b D → e ≤ d+2 → ∀ x : Site c,
    meter b σ m N x (envelope a R K N d (e:=e)) ≤ volumeCost m D N * (mapCost R σ m L*K)^3 * Real.exp (-(R/2)*N) * ((1/2:ℝ)^d) := by
  let C := mapCost R σ m L*K
  have hM := map_ge (m:=m) (L:=L) hs hr
  have hC : 1≤C := one_le_mul_of_one_le_of_one_le hM hK
  have he : ∀ᶠ N : ℕ in atTop, C * Real.exp (-R*N) < 1/2 := by
    apply Tendsto.eventually_lt_const (show (0:ℝ)<1/2 by norm_num)
    simpa only [Function.comp_def,neg_mul,mul_zero] using ((Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hr)).const_mul C)
  filter_upwards [eventually_gt_atTop (0:ℕ), he] with N hN he
  intro _ _ I _ a b D d e ha hb hh x
  unfold envelope; rw [meter_mul]; let H := volumeCost m D N; have hH : 0≤H := by unfold H volumeCost; positivity
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_meter ha hb (m:=m) hN hr hs x) (show 0 ≤ K^e*Real.exp (-R*N)^(d+1) by positivity)
    _ ≤ K^(d+3) * Real.exp (-R*N)^(d+1) * (H*mapCost R σ m L^(d+3)) := by gcongr K^?_ * _ * (H*_ ^ ?_) <;> omega
    _ = H*C^3 * Real.exp (-R*N) * (C*Real.exp (-R*N))^d := by unfold C; simp [pow_add,mul_pow]; ring
    _ ≤ _ := by gcongr; linarith

end YM.Further.CurvedGaussianJets.Tracks
