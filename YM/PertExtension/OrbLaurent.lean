import YM.PertExtension.OrbParity
import YM.PertExtension.PTBills

/-! Laurent factors from slot powers for filtered (unnormal-ordered) columns:
no negative coupling degrees survive and the leading law is Gaussian. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.PertExtension.Orb
open Wilson Lattice Gauge Precision Function Filter Set Metric MeasureTheory
open scoped ContDiff Topology Classical BigOperators ENNReal
open Chart Series Series.Radial Series.Tested
variable {G : Gauge}{n : Side}{P : ChartRatio G}
local notation "W" => tangent G (Cotree n)

def passave {O : Observable G n}(j : ℕ) := jet (O ∘ expLinks G _) j
variable {O : Observable G n}(R : LocalRatio P)(h:LocalTest O) {w : ℕ}
variable (H : RadialOrder w (O ∘ expLinks G (Cotree n)))

include H h R
lemma entering_jets (i:ℕ)(hi : i ≤ w)(u : Dir G n) :
    jet (accountingWith P O) i u = (if i=w then jacobian P (U:=Cotree n) 0 * jet (O ∘ expLinks G _) w u else 0) := by
  let f : Dir G n → ℝ := O ∘ expLinks G _
  let J : Dir G n→ℝ := jacobian P
  have hn : ∀ i < w, jet f i u=0:=fun i hi=> by rw [jets_vanish h.germ H hi];rfl
  have ha := directions (Chart.Ratio.jacobian_smooth R (U:=Cotree n) |>.of_le le_top) u
  have hb := directions h.germ u
  have he := (directions (chart_integrand R h) u).unique (ha.prod hb)
  have he' := congr_fun he i
  simp only [conv,term,PowerSeries.coeff_mul,PowerSeries.coeff_mk] at he'; rw [he']
  by_cases eq:i=w
  · subst i
    rw [Finset.sum_eq_single_of_mem (0,w) (Finset.mem_antidiagonal.mpr (zero_add w))]
    · simp [J]
    intro a ha he;have hh := Finset.mem_antidiagonal.mp ha
    have ht:a.2<w := by by_contra! hq;apply he;ext1 <;> simp [(show a.1=0 from by omega),(show a.2=w from by omega)]
    rw [show jet (O ∘ expLinks G _) a.2 u = 0 from hn _ ht,mul_zero]
  have hl:i<w := lt_of_le_of_ne hi eq
  rw [if_neg eq]; apply Finset.sum_eq_zero; intro a ha
  have hh := Finset.mem_antidiagonal.mp ha
  rw [show jet (O ∘ expLinks G _) a.2 u=0 from hn _ (by omega),mul_zero]

lemma entry_top {i : ℕ}(hi : i≤w)(u : Dir G n):
    integrandSeries fiscal (accountingWith P O) i u = if i=w then jacobian P (U:=Cotree n) 0 * jet (O ∘ expLinks G _) w u else 0 := by
  unfold integrandSeries Zone.mul;refine (Finset.sum_eq_single_of_mem (i,0) (Finset.mem_antidiagonal.mpr (add_zero i)) (fun a ha h'=>?_)).trans ?_
  · have ht:= Finset.mem_antidiagonal.mp ha
    have hv:a.1<w := by by_contra! hq;apply h';ext1 <;> simp [(show a.1=i from by omega),(show a.2=0 from by omega)]
    rw [entering_jets R h H _ (hv.le),if_neg hv.ne,zero_mul]
  dsimp only; rw [entering_jets R h H i hi,expsum];simp [Zone.TaylorPow]

lemma rows_down {i : ℕ}(hi : i < w) : rowsWith P O i=0:=by
  unfold rowsWith Radial.moment normTerm
  simp_rw [entry_top R h H hi.le, if_neg hi.ne]; simp

private lemma hPivot (even : Even n.val){i : ℕ}(hi:i≤w) (hf:∀ j < i, diagonalWith P O j=0): diagonalWith P O i * rowsWith P (n:=n) 1 0=rowsWith P O i:=by
  have he:=congr_fun (rows_with_head R even O) i
  rw [conv,term,PowerSeries.coeff_mul] at he;simp only [PowerSeries.coeff_mk] at he
  rw [Finset.sum_eq_single_of_mem (i,0) (Finset.mem_antidiagonal.mpr (add_zero i)) (f:=fun v=>diagonalWith P O v.1 * rowsWith P (n:=n) 1 v.2) (fun a ha h'=>?_)] at he
  · exact he
  have ht := Finset.mem_antidiagonal.mp ha
  rw [hf _ ?_, zero_mul]
  by_contra! hq;apply h';ext1 <;> simp [show a.1=i from by omega,show a.2=0 from by omega]

lemma diag_down (even : Even n.val) : ∀ i < w, diagonalWith P O i=0:=by
   intro i hi; induction i using Nat.strong_induction_on with
   | _ k ih =>
     apply Or.resolve_right (mul_eq_zero.mp _) (pivot even R).ne'
     exact (hPivot R h H even hi.le (fun j hj=>ih _ hj (hj.trans hi))).trans (rows_down R h H hi)

/-- All powers calculated after the same normalized denominator; leading
slot enters by its ordinary Taylor polynomial without top Wick compensation in
this lemma. -/
theorem LaurentShift (even : Even n.val):
    Aspiration (fun (t:ℝ) => (t⁻¹)^w * expectation O t) (fun j=>diagonalWith P O (w+j)) := (finite_formula even R h).shift (diag_down R h H even)

theorem leading_row (even : Even n.val) :
     diagonalWith P O w = (∫ u, jet (O ∘ expLinks G (Cotree n)) w u * kernel fiscal u ∂W) / (∫ u, kernel fiscal u ∂W) := by
   let J := jacobian P (U:= Cotree n) 0
   let D := (∫ u, kernel fiscal u ∂W)
   have hd : J * D = rowsWith P (n:=n) 1 0 := by rw [rows_zero,Pi.one_apply,mul_one]
   have hd' := (pivot even R).ne'
   rw [← hd] at hd'
   have hp := hPivot R h H even le_rfl (diag_down R h H even); rw [← hd] at hp
   let F (u : Dir G n) := jet (O ∘ expLinks G _) w u* kernel fiscal u
   have he : rowsWith P O w=J * ∫ u,F u ∂W:=by
      unfold rowsWith Radial.moment normTerm
      simp [entry_top R h H le_rfl,mul_assoc, J,F, integral_const_mul]
   change _ = _ / D;apply (eq_div_iff (right_ne_zero_of_mul hd')).mpr
   apply mul_left_cancel₀ (left_ne_zero_of_mul hd')
   rw [show J*(diagonalWith P O w*D)=diagonalWith P O w*(J*D) by ring, hp, he]

omit H h
lemma unit_diagonal (even : Even n.val) : diagonalWith P (1:Observable G n) =fun j=> if j=0 then 1 else 0 := by
  unfold diagonalWith divide
  funext k
  rw [PowerSeries.mul_inv_cancel ..]; exact PowerSeries.coeff_one _
  simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, (pivot even R).ne']

lemma unit_expectation : expectation (1:Observable G n)=1:=by unfold expectation;ext t;exact div_self (numerator_pos t).ne'

end YM.PertExtension.Orb
