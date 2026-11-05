import Mathlib.Analysis.PSeries
import YM.Push.LOOP_COEFFICIENT.Block.Portal
import YM.Push.LOOP_COEFFICIENT.Fine.Tilt
import YM.Push.LOOP_COEFFICIENT.Kernel.Mass
import YM.Push.LOOP_COEFFICIENT.Spread



/-!
# Nonanalytic real-end weights on alias fibers and counting decay
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Filter Set Matrix Lattice Laurent RG Precision Exterior Bloch Wilson Complex Fine Metric Kernel
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator
variable {L : Side} {η : ℝ} {p q₁ : Momentum}

def energy (L : Side) (p : Momentum) (l : Site L) := (L.val:ℝ)⁻¹ + Real.sqrt (deltaFreq (shade (aliasAt p l)))
lemma energy_lo (L : Side) (q) (l) : (L.val:ℝ)⁻¹ ≤ energy L q l := le_add_of_nonneg_right (Real.sqrt_nonneg _)
lemma energy_pos (L : Side) (p l) : 0<energy L p l := (inv_pos.mpr (side_pos _)).trans_le (energy_lo ..)
lemma delta_period (p : Momentum) (x : Cover) : deltaFreq (p+reciprocal x)=deltaFreq p := by unfold deltaFreq; apply Finset.sum_congr rfl fun i _ => ?_; unfold Exterior.q; rw [show cexp (I * (p+reciprocal x) i) = _ from freq_period p i x]; rfl
lemma energy_shift (l : Site L) (q : Momentum) (x : Cover) : energy L (q+reciprocal x) l = energy L q (l+wrap L x) := by
  unfold energy; obtain ⟨y,hy⟩ := alias_shift l q x
  rw [hy,show ∀ k : Momentum, shade (k + reciprocal y) = shade k + reciprocal y by intro k; ext; simp [shade,reciprocal],delta_period]
lemma energy_neg (p : Momentum) (l : Site L) : energy L (-p) (-l) = energy L p l := by
  unfold energy; obtain ⟨x,hx⟩ := alias_opposite l p; rw [hx]
  let k := shade (aliasAt p l)
  have he : star k = k := by ext; simp [k,shade]
  rw [show shade (-aliasAt p l+reciprocal x) = -k+reciprocal x by ext; simp [shade,reciprocal,k],delta_period]; unfold deltaFreq; simp [q_bar he]; rfl
lemma delta_upper (q : Momentum) (he : star q=q) : Real.sqrt (deltaFreq q) ≤ 2*‖q‖ := by
  apply Real.sqrt_le_iff.mpr ⟨by positivity,(Finset.sum_le_sum (s:=Finset.univ) (fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2)).trans (show (∑ _ : Axis, ‖q‖^2) ≤ (2*‖q‖)^2 by simp [Axis]; linarith)⟩
  refine le_trans ?_ (norm_le_pi_norm q i); unfold Exterior.q; rw [← conj_eq_iff_re.mp (congr_fun he i : (starRingEnd ℂ) _ = _), Complex.norm_real]; apply Real.norm_exp_I_mul_ofReal_sub_one_le
lemma energy_ruler (q : Momentum) (l : Site L) : energy L q l ≤ 2*ruler (L.val:ℝ)⁻¹ (shade (aliasAt q l)) := by have := delta_upper (shade (aliasAt q l)) (by ext; simp [shade]); have := (inv_pos.mpr (side_pos L)); unfold energy ruler; linarith
lemma energy_center (hp : p∈Center η) (hL : Odd L.val) (l : Site L) : mass l/L.val ≤ 2*energy L p l := by
  let z := aliasAt p l
  let k := shade z
  have hw : Windowed k := center_window (z:=z) ⟨alias_tube l hp.1, alias_core hL l hp⟩
  have he : 2/Real.pi * ‖k‖ ≤ Real.sqrt (deltaFreq k) := (Real.le_sqrt (by positivity) (delta_nonneg _)).mpr (by rw [mul_pow]; exact delta_gap hw.1 hw.2)
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => (Lattice.lift l i).natAbs)
  change pdist l = _ at hi
  have ht : |(z i).re| ≤ ‖k‖ := by simpa [k,shade] using norm_le_pi_norm k i
  have hx := hp.2 i
  rw [show (z i).re = _ from alias_real l p i, abs_div,abs_of_pos (side_pos _),div_le_iff₀ (side_pos _)] at ht
  have hsub := abs_sub ((p i).re + 2*Real.pi*(Lattice.lift l i:ℤ)) (p i).re
  rw [add_sub_cancel_left,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi), ← Int.cast_abs,← Int.natCast_natAbs,Int.cast_natCast,← hi] at hsub
  unfold mass energy; rw [div_mul_eq_mul_div,div_le_iff₀ Real.pi_pos] at he
  rw [div_le_iff₀ (side_pos L),mul_assoc,add_mul, inv_mul_cancel₀ (side_pos L).ne']; change _ ≤ 2*(1+Real.sqrt (deltaFreq k)*_)
  apply le_of_mul_le_mul_left _ Real.pi_pos; nlinarith [Real.pi_pos, side_pos L, mul_nonneg (mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg (deltaFreq k))) (side_pos L).le,mul_le_mul_of_nonneg_right he (side_pos L).le]

lemma band_count (L : Side) (n : ℕ) : (Finset.univ.filter (fun l : Site L => pdist l=n)).card ≤ (n+n+1)^4 := by
  rw [← Corona.box_size]; refine Finset.card_le_card_of_injOn Lattice.lift (fun i hi => box_test.mpr ?_) ((show Function.LeftInverse (wrap L) Lattice.lift from wrap_lift).injective.injOn)
  have h := Finset.mem_filter.mp hi |>.2; constructor <;> (intro j; have := component_le i j; omega)
lemma mass_sum : ∃ C>0,∀ L : Side, ∑ i : Site L, (mass i)⁻¹^6 ≤ C := by
  have hs := (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).comp_injective (show Injective (fun n : ℕ => n+1) from fun _ _ => Nat.succ_inj.mp)
  let f (n : ℕ) := (16:ℝ)*(1/(n+1:ℕ)^2)
  have he : Summable f := by simpa [f] using hs.mul_left 16
  have hc (n) : 0≤f n := by unfold f; positivity
  refine ⟨1+∑' i,f i,by linarith [show 0≤∑' i,f i from tsum_nonneg hc],fun L => ?_⟩; rw [← Finset.sum_fiberwise_of_maps_to (g:=pdist (n:=L)) (t:=Finset.univ.image pdist) (fun _ hi => Finset.mem_image_of_mem _ hi)]
  refine (Finset.sum_le_sum (fun i _ => ?_)).trans ((he.sum_le_tsum _ fun _ _ => hc _).trans (by linarith))
  rw [show (∑ x : Site L with pdist x = i, (mass x)⁻¹^6) = (∑ _x : Site L with pdist _x = i, ((i+1:ℕ):ℝ)⁻¹^6) by apply Finset.sum_congr rfl fun x hx => ?_; rw [mass,Finset.mem_filter.mp hx |>.2]; simp [add_comm]]; simp only [Finset.sum_const,nsmul_eq_mul]
  have h' := Nat.cast_le (α:=ℝ).mpr (band_count L i); push_cast at h'; unfold f; push_cast
  refine (mul_le_mul_of_nonneg_right (h'.trans (show _ ≤ (2*((i:ℝ)+1))^4 by gcongr; linarith)) (by positivity)).trans_eq ?_; field_simp; ring
end YM.Push.Loops.Block
