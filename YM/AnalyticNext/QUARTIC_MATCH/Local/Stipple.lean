import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Collective
import YM.Next.SCHEDULE.GridCost
import YM.Progress.STATIONARY_SCENES.Green

/-!
# Integrating the marked bills

Weights attached to physical origins (exponents can be signed). Pay for
summing mixed derivatives; retain external distances, constants pre-L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Local
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 
open  Estimate Estimate.Purse Estimate.Logfee  
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {n l c f : Side} {ι : Type} [DecidableEq ι]
namespace Premium
open Green (wt)

lemma angle {η t : ℝ} (h : |t| ≤ η) (x y z : Site n) : wt t x z ≤ wt η x y * wt t y z := by
  unfold wt; rw [← Real.exp_add]; apply Real.exp_monotone
  rcases le_total 0 t with he|he
  · have hh : (separation x z:ℝ) ≤ (separation x y:ℝ)+(separation y z:ℝ) := by exact_mod_cast separation_triangle x y z
    have hp := mul_le_mul_of_nonneg_left hh he
    rw [mul_add] at hp; exact hp.trans (add_le_add (mul_le_mul_of_nonneg_right ((le_abs_self _).trans h) (by positivity)) le_rfl)
  have hh : (separation y z:ℝ) ≤ (separation x y:ℝ)+(separation x z:ℝ) := by rw [separation_comm x y]; exact_mod_cast separation_triangle y x z
  linarith only [mul_le_mul_of_nonpos_left hh he,mul_le_mul_of_nonneg_right ((neg_le_abs _).trans h) (show 0 ≤ (separation x y:ℝ) by positivity)]

lemma scaled (l : Side) {η t : ℝ} (h : |t| ≤ η) (x y z : Site n) :
    wt (t/l.val) x z ≤ wt (η/l.val) x y*wt (t/l.val) y z := angle (by rw [abs_div,abs_of_pos (side_pos l)]; gcongr) ..
lemma inhabits (x y : Site n) : size (lift (x-y)) ≤ 4 * separation x y := by
  unfold Laurent.size; exact (Finset.sum_le_sum (fun i _ => Lattice.component_le (x-y) i)).trans_eq (by simp [Axis,separation])

def shells (η : ℝ) := 2*(1+η/4)/(η/4)
def overall (η : ℝ) := max 1 (shells η^4)
lemma cover_ge (η : ℝ) : 1 ≤ overall η := le_max_left ..
lemma lives (l : Side) {η : ℝ} (h : 0<η) (z : Site n) : ∑ i : Site n,(wt (η/l.val) i z)⁻¹ ≤ overall η*(l.val:ℝ)^4 := by
  classical
  let b i := size (lift (i-z))
  have he := side_pos l
  let r := η / l.val / 4; have hr : 0<r := by unfold r; positivity
  have hb i : (wt (η/l.val) i z)⁻¹ ≤ Real.exp (-r* b i) := by
    unfold wt; rw [← Real.exp_neg]; apply Real.exp_monotone
    have hp : (b i:ℝ) ≤ 4*(separation i z:ℝ) := by exact_mod_cast inhabits i z
    apply le_trans _ (mul_le_mul_of_nonpos_left hp (neg_nonpos.mpr hr.le)); unfold r; linarith
  have hh : _ := Width.compactPay (α:=Axis) r hr
  let t (i : Site n) := lift (i-z)
  apply ((Finset.sum_le_sum (fun i _ => hb i)).trans ((by
    let e : Site n ↪ Cover := ⟨t,fun _ _ he => sub_left_injective (lift_inj he)⟩
    rw [show ∑ i : Site n, Real.exp (-r*b i)=∑ i∈Finset.univ.map e, Real.exp (-r*size i) by rw [Finset.sum_map]; rfl]
    exact hh.2.1.sum_le_tsum _ (fun i _ => hh.1 i)) : _ ≤ ∑' i : Cover,Real.exp (-r*size i))) |>.trans (hh.2.2.trans ?_)
  simp only [Axis,Fintype.card_fin]
  apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right 1 (shells η^4)) (show 0 ≤ (l.val:ℝ)^4 by positivity)); rw [← mul_pow];
  apply pow_le_pow_left₀ (by positivity); unfold shells r; field_simp; nlinarith
    [show 1 ≤ (l.val:ℝ) by exact_mod_cast l.property]
lemma meanlives (l : Side) {η : ℝ} (h : 0<η) (z : Site n) : rlen (fun i : Site n => (wt (η/l.val) i z)⁻¹) ≤ overall η*(l.val:ℝ)^2 := by
  have he := cover_ge η; have hk := zero_le_one.trans he
  apply (sq_le_sq₀ (ell_nonneg _) (mul_nonneg hk (by positivity))).mp; rw [square_length]
  apply (le_trans ?_ ((lives l h z).trans ?_))
  · refine Finset.sum_le_sum fun i _ => ?_
    have hh : 1 ≤ wt (η/l.val) i z := Real.one_le_exp (by positivity)
    have hm := inv_le_one_of_one_le₀ hh
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hh)),pow_two]; exact mul_le_of_le_one_right (inv_nonneg.mpr (zero_le_one.trans hh)) hm
  rw [mul_pow]; apply mul_le_mul ?_ (le_of_eq ?_) (pow_nonneg (by positivity) _) (sq_nonneg _)
  · nlinarith
  ring

/-- Weight lower at all anchors leaves a single-factor e decay for summing
the anchors. Use ρ on product of cross external distances. -/
def Stamp {ι : Type} (P : Purse ι (Site n)) (S : Finset ι) (l : Side) (η C : ℝ) (z : Site n) :=
    ∀ x, C*wt (η/l.val) x z ≤ P.price S x

variable {P : Purse ι (Site n)} {x : Site n → ℝ} {S : Finset ι} {η C R : ℝ}
omit [DecidableEq ι] in
lemma tariff (h : P.Pays S x C) (hy : P.cap=(l.val:ℝ)^2) (he : 0<η) (hr : 0≤R) (z : Site n) (hx : Stamp P S l η R z) :
    R* |∑ i,x i| ≤ (overall η*(l.val:ℝ)^4)*(C*P.target S) := by
  let w (i : Site n) := wt (η/l.val) i z
  let b i := P.price S i * |x i|
  have hh (i : Site n) : R* |x i| ≤ (w i)⁻¹*b i := by
    have he : 0 < w i := Green.wt_pos ..
    rw [inv_mul_eq_div]; apply (le_div_iff₀ he).mpr; rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)
  apply ((mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs x _) hr)).trans
  rw [Finset.mul_sum]; apply (Finset.sum_le_sum (fun i _ => hh i)).trans
  by_cases hS : P.tagged S
  · let u i := (w i)⁻¹
    change dotProduct u b ≤ _
    apply (le_abs_self _).trans; apply (norm_real_area ..).trans
    exact (mul_le_mul (meanlives l he z) (h.2.2 hS) (ell_nonneg b) (mul_nonneg (zero_le_one.trans (cover_ge _)) (sq_nonneg _))).trans_eq (by rw [hy]; ring)
  · apply (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h.2.1 hS i)
      (inv_nonneg.mpr (show 0 ≤ w i from (Green.wt_pos ..).le)))).trans
    rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (lives l he z) (mul_nonneg h.1 (P.target_pos _))
end Premium
end YM.AnalyticNext.QuarticMatch.Local
