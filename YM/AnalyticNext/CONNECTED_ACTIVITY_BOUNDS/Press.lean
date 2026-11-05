import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Chromosomes
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tensors
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.TiltAccount
import YM.Push.RELAY_DIFFERENCE.Shuffles


/-!
# Marginal pressure for the coupling derivatives

Scaling trick avoids differentiating the **full** determinant, which charges volume, when
inspecting a single component. The surcharge is neutral upon exp-polynomial deposition, even
on empty Gaussian population. Intended for beta powers only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Plotter
open Function MeasureTheory Filter Matrix Finset Topology Centered Centered.Moment
open Centered.Till Progress.StationaryScenes Green
open scoped Topology BigOperators ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P]

lemma drilled {A : Matrix ι ι ℝ} (ha : PosDef A) {r : ℝ} (hr : 0<r) (hP : Bottom A r) (z : Subtype P→ℝ) :
    0 ≤ dotProduct z ((ops P A)⁻¹ *ᵥ z) ∧ dotProduct z ((ops P A)⁻¹ *ᵥ z) ≤ r⁻¹ * dotProduct z z := by
  let M := ops P A; let y := M⁻¹ *ᵥ z
  have hm : M.PosDef := ha.submatrix Subtype.val_injective; have hy : M*ᵥ y=z := by unfold y; rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hm.det_pos.ne'), Matrix.one_mulVec]
  have h : Bottom M r := hP.restrict (Embedding.subtype P)
  have he := h y; rw [hy,dotProduct_comm y z] at he
  refine ⟨le_trans (mul_nonneg hr.le (dot_nonneg _)) he,?_⟩
  apply le_of_mul_le_mul_left _ hr; rw [← mul_assoc, mul_inv_cancel₀ hr.ne',one_mul]; change r*dotProduct z y ≤ _
  have hp := dot_nonneg (z-r • y)
  rw [dotProduct_sub, sub_dotProduct, sub_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,dotProduct_comm y z] at hp
  nlinarith only [hp,mul_le_mul_of_nonneg_left he hr.le]

def levy (A : Matrix ι ι ℝ) (t : ℝ) (z : Subtype P→ℝ) := (1+t)^Fintype.card (Subtype P) *
    Real.exp (- (hour t-1)*dotProduct z ((ops P A)⁻¹ *ᵥ z)/2)

def abrupt (A : Matrix ι ι ℝ) (t : ℂ) (z : ι→ℝ) := let v := fulsome P z
    (1+t)^Fintype.card (Subtype P) * Complex.exp (-((1+t)^2-1)* ↑(dotProduct v ((ops P A)⁻¹ *ᵥ v))/2)






lemma continuous_abrupt (A : Matrix ι ι ℝ) (t : ℂ) : Continuous (abrupt P A t) := by
  unfold abrupt fulsome; dsimp only; fun_prop

-- real-valued remittance. Domains incl z junk; need PF earns to justify.


def seedRadius (u w : ℝ) := min (u*w/8) (1/16)
def cord (u w : ℝ) := seedRadius u w / (1+(Fintype.card (Subtype P):ℝ))

omit [DecidableEq ι] in
lemma highT {u w : ℝ} (he : 0<u) (ht : 0<w) : 0<cord P u w ∧ cord P u w≤1/16 := by
  have hn : 0<seedRadius u w := lt_min (by positivity) (by norm_num)
  exact ⟨div_pos hn (by positivity),le_trans (div_le_self hn.le (by simp)) (min_le_right ..)⟩

def levyBill (u w : ℝ) : Tilt ι := ⟨Real.exp (seedRadius u w),fun i => if P i then
    w/(2*(1+(Fintype.card (Subtype P):ℝ))) else 0⟩
omit [DecidableEq ι] in
lemma levySound {u w : ℝ} (hw : 0<w) : (levyBill P u w).Sound := ⟨(Real.exp_pos _).le,fun i => by dsimp only [levyBill]; split <;> positivity⟩
omit [DecidableEq ι] in
lemma levy_ge (u w : ℝ) (hw : 0 ≤ w) (i : ι) : (levyBill P u w).tally i ≤ w/2 := by
  dsimp only [levyBill]; split; swap; positivity
  apply div_le_div_of_nonneg_left hw (by norm_num); simp [mul_add]

def palet (t : Till) (u : ℝ) := Real.exp (seedRadius u t.expense)*Real.exp ((t.floor⁻¹ * (t.expense/2))/2)
omit [DecidableEq ι] in
lemma logLevy (t : Till) (u : ℝ) : t.sale (levyBill P u t.expense) ≤ palet t u := by
  unfold sale palet; dsimp only [levyBill]; gcongr
  · exact inv_nonneg.mpr t.floor_pos.le
  rw [← Fintype.sum_subtype_add_sum_subtype P,show (∑ i : {k // ¬ P k}, (if P i.val then t.expense / (2*(1+(Fintype.card (Subtype P):ℝ))) else 0))=0
      from sum_eq_zero fun i _ => if_neg i.property, add_zero, sum_congr (s₂:=@univ (Subtype P) _) (f:=fun i => if P i.val then t.expense/(2*(1+(Fintype.card (Subtype P):ℝ))) else 0) (g:=fun _ => t.expense / (2*(1+(Fintype.card (Subtype P):ℝ)))) rfl
        (fun i _ => if_pos i.property)]
  rw [sum_const,card_univ,nsmul_eq_mul]; field_simp; linarith [t.expense_nn]

lemma pays_abrupt (A : Matrix ι ι ℝ) (ha : PosDef A) (u w : ℝ) (hu : 0<u) (hw : 0<w) (hA : Bottom A u)
    (t : ℂ) (ht : ‖t‖ ≤ cord P u w) (z : ι→ℝ) : ‖abrupt P A t z‖ ≤ Ticket (levyBill P u w) z := by
  obtain ⟨hr,hh⟩ := highT P hu hw; let M := Fintype.card (Subtype P)
  let n := 1+(M:ℝ); have hn : 0<n := by unfold n; positivity
  let e := seedRadius u w; have he : 0<e := lt_min (by positivity) (by norm_num)
  have hs := distance' (ht.trans hh)
  let v := fulsome P z; let f : ℂ := -((1+t)^2-1)
  let Z := dotProduct v ((ops P A)⁻¹*ᵥ v); let g := levyBill P u w
  change ‖(1+t)^M * Complex.exp (f*↑Z/2)‖≤ _; unfold Ticket
  rw [norm_mul, norm_pow]
  have hf : ‖1+t‖^M ≤ Real.exp e := by
    calc
      _ ≤ (Real.exp ‖t‖)^M := by
        gcongr; have hx := Real.add_one_le_exp ‖t‖; have hz := norm_add_le (1:ℂ) t; rw [norm_one] at hz; linarith
      _ ≤ _ := by
        rw [← Real.exp_nat_mul,Real.exp_le_exp]; change ‖t‖≤e/n at ht
        have hp := (le_div_iff₀ hn).mp ht; unfold n at hp; nlinarith [norm_nonneg t]
  apply mul_le_mul hf _ (norm_nonneg _) (Real.exp_pos _).le; rw [Complex.norm_exp,Real.exp_le_exp]
  let a := w/(2*n)
  have hl : 3*‖t‖ * u⁻¹ ≤ a := by
    calc
      _ ≤ (3*cord P u w)*u⁻¹ := by gcongr
      _ ≤ (3*(u*w/8/n))*u⁻¹ := by unfold cord; gcongr; exact min_le_left ..
      _ ≤ _ := by unfold a; field_simp; nlinarith
  have h₁ := (Complex.re_le_norm f).trans (show ‖f‖≤3*‖t‖ by unfold f; rw [norm_neg]; exact hs)
  obtain ⟨hL,hv⟩ := drilled P ha hu hA v
  change 0 ≤ Z at hL; change Z ≤ _ at hv
  have hh : f.re * Z ≤ a * dotProduct v v := calc
    _ ≤ 3*‖t‖*Z := mul_le_mul_of_nonneg_right h₁ hL
    _ ≤ 3*‖t‖*(u⁻¹ * dotProduct v v) := mul_le_mul_of_nonneg_left hv (by positivity)
    _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hl (dot_nonneg _)
  have he : tilt (levyBill P u w).tally z=a*dotProduct v v := by
    unfold tilt; rw [← Fintype.sum_subtype_add_sum_subtype P]
    rw [show ∑ i : {k // ¬ P k}, g.tally i.val*z i.val^2=0 from sum_eq_zero fun i _ => by
      unfold g; dsimp only [levyBill]; rw [if_neg i.property,zero_mul], add_zero]
    unfold dotProduct; rw [mul_sum]; exact sum_congr rfl fun i _ => by dsimp only [levyBill]; rw [if_pos i.property,pow_two]; rfl
  rw [he,← Complex.ofReal_ofNat (n:=2),Complex.div_ofReal_re, Complex.mul_re , Complex.ofReal_re,Complex.ofReal_im]; linarith
end YM.AnalyticNext.ConnectedActivity.Plotter
