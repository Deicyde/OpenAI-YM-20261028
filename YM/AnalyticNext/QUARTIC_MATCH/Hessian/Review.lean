import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Origin
import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Stripe

/-!
# First buy an inexpensive representative

Scalar case over ℂ (real frequencies, all complex gauge directions). Real
kernel estimates later. Low component need not be real (edge-of-zone
modes etc.).

Plan of the gap estimates: keep Q = mean on links, palette = box average on
sites. W-space cost `rent S a χ = ‖curl a‖+‖div a‖+‖a‖/L+‖χ‖`
(ℓ² norms). In `twist_free` remove χ and the divergence of the *high*
part of the fine field, by a gauge shift (d₀ and site palette conventions as
in `duel`). χ elimination can use *just* low aliases, leaving high divergence
removed. Thus we can price this particular representative modulo gauge: use
high curl for high part, use Q and subtract residual contributions from high
part to control the low part (Q on it is quantitatively bounded below).
Even harmonic components treated. This is only flat linear algebra; now
`Dues` pays the W-cost of restoring the gauge via `upkeep`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Hessian
open Filter Function Lattice Laurent Bloch Exterior Matrix Precision RG Work.F06
open Pre.Centered YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ComplexConjugate InnerProductSpace
variable {c f : Side} (S : StepData c f)
local notation "L" => (S.patch.L.val:ℝ)
local notation "j" => S.patch.J
local notation "D" => drawC f 1
local notation "d₀" => drawC f 0
local notation "d'" => drawC c 0
local notation "Y" => Form f 1
local notation "A" => Form f 0
local notation "V" => Form c 0
local notation "B₀" => approached (palette S)
local notation "M" => approached (Precision.mean S)

def rent (a : Form f 1) (x : Form c 0) := ell2 (D*ᵥ a) + ell2 (d₀ᴴ *ᵥ a) + ell2 a / L + ell2 x

lemma rent_sub (a b : Form f 1) (u v : Form c 0) : rent S (a-b) (u-v) ≤ rent S a u + rent S b v := by
  unfold rent; simp only [Matrix.mulVec_sub];
  have he := add_le_add (add_le_add (ell_sub (D*ᵥ a) (D*ᵥ b)) (ell_sub (d₀ᴴ *ᵥ a) (d₀ᴴ *ᵥ b)))
    (div_le_div_of_nonneg_right (ell_sub a b) (side_pos S.patch.L).le)
  rw [add_div] at he
  linarith [ell_sub u v]

lemma duel (x : Form f 0) : M*ᵥ (d₀*ᵥ x)=d'*ᵥ(B₀*ᵥ x) := by
  have hu : Precision.mean S*d 0 f=d 0 c*palette S := by
    apply Matrix.toLin'.injective; apply LinearMap.ext; intro x
    funext ⟨a,i⟩; obtain ⟨i,rfl⟩ := axisEquiv.surjective i
    change ((Precision.mean S * d 0 f)*ᵥ x) (a,coord i)=((d 0 c*palette S)*ᵥ x) (a,coord i)
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,d_sites,palette_site,palette_site,Precision.mean_site]
    simp only [show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply _,mul_sub,Finset.sum_sub_distrib]
  rw [mulVec_mulVec,mulVec_mulVec,drawC,drawC,← prom_mul,← prom_mul,hu]
lemma shadow (x : A) : D*ᵥ(d₀*ᵥ x)=0 := by
  rw [mulVec_mulVec,drawC,drawC,← prom_mul,d_d_vac]; simp [approached]

/-- Cost after eliminating high-alias longitudinal components. -/
def earlyAddon (i : ℕ) := (1+earlyFee) * (colorPrice i)⁻¹*(1+lateFee⁻¹)
def farePlan (i : ℕ) := 1 + lateFee⁻¹ + earlyAddon i
lemma go_positive (i : ℕ) : 0 < farePlan i := by
  unfold farePlan earlyAddon; have hx := color_pos i; have ht := late_pos; have hb := early_pos; positivity

lemma rates (a l : Form f 1) (h : TopF S a) (H : d₀ᴴ *ᵥ a=0) (hh : ToeF S l) :
    rent S (a+l) 0 ≤ farePlan j*(ell2 (D*ᵥ (a+l))+ell2 (M*ᵥ (a+l))) := by
  let e := ell2 (D*ᵥ (a+l))
  let u := ell2 (M*ᵥ (a+l))
  have he : ell2 a/L ≤ lateFee⁻¹ * e := by
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ late_pos).mpr
    calc
      _ = lateFee/L*ell2 a := by ring
      _ ≤ ell2 (D*ᵥ a) := top_one S h H
      _ ≤ e := by unfold e; rw [Matrix.mulVec_add]; exact (growth S (top_up _ h) (toe_up _ hh)).1
  have hp : ell2 l / L ≤ (colorPrice j)⁻¹ * (u+lateFee⁻¹ * e) := by
    rw [inv_mul_eq_div]; apply (le_div_iff₀ (color_pos j)).mpr; apply le_trans _ (add_le_add le_rfl he)
    calc
      _ = (colorPrice j*ell2 l)/L := by ring
      _ ≤ ell2 (M*ᵥ l) := (div_le_iff₀ (side_pos S.patch.L)).mpr ((show colorPrice j * ell2 l ≤ L*ell2 (M*ᵥ l) from fare_one S l hh).trans_eq (mul_comm ..))
      _ ≤ _ := by
        have ht : ell2 (M*ᵥ a) ≤ ell2 a/L := (fraction S a).trans_eq (inv_mul_eq_div ..)
        have hu := (ell_sub (M*ᵥ (a+l)) (M*ᵥ a)).trans (add_le_add le_rfl ht)
        rw [Matrix.mulVec_add,add_comm (M*ᵥ a),add_sub_cancel_right] at hu
        unfold u; rw [Matrix.mulVec_add,add_comm (M*ᵥ a)]; exact hu
  have ha : ell2 ((drawC f 0)ᴴ *ᵥ l)+ell2 l/L ≤ earlyAddon j *(e+u) := by
    have he' := toe_one S hh
    have h₁ := late_pos; have h₂ := early_pos; have h₃ : 0<colorPrice j := color_pos _
    unfold earlyAddon
    have H := (mul_le_mul_of_nonneg_left hp (by linarith : (0:ℝ) ≤ 1+earlyFee))
    calc
      _ ≤ (1+earlyFee)*(ell2 l/L) := (add_le_add he' (le_refl (ell2 l/L))).trans_eq (by ring)
      _ ≤ _ := H
      _ ≤ _ := by
        simp only [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr h₃.le)
        have hv : 0 ≤ u := ell_nonneg _; have hh : 0 ≤ e := ell_nonneg _
        have hw := mul_nonneg (inv_nonneg.mpr h₁.le) hv; linarith
  have hu := div_le_div_of_nonneg_right (ell_tri a l) (side_pos S.patch.L).le
  rw [add_div] at hu
  unfold rent farePlan
  rw [Matrix.mulVec_add (d₀ᴴ),H,zero_add,ell_zero]
  change e+_+_+(0:ℝ) ≤ _*(e+u)
  have hx : 0 ≤ u := ell_nonneg _; linarith [mul_nonneg (inv_nonneg.mpr late_pos.le) hx]

lemma twist_free (y : Form f 1) (v : Form c 0) : ∃ u : Form f 0,
    rent S (y+d₀*ᵥ u) (v+B₀*ᵥ u) ≤ farePlan j *
      (ell2 (D*ᵥ y)+ell2 (M*ᵥ y-d'*ᵥ v)) := by
  obtain ⟨a,b,ha,hb,rfl⟩ := split_from S y
  obtain ⟨w,hw,hk⟩ := top_available S (top_down S ha)
  obtain ⟨l,hl,hh⟩ := supplied S (B₀ *ᵥ w - v)
  refine ⟨l-w,?_⟩
  let x := a-d₀*ᵥ w
  let k := b+d₀*ᵥ l
  have h1 : TopF S x := top_left S ha (top_up S hw)
  have h2 : d₀ᴴ *ᵥ x=0 := by unfold x; rw [Matrix.mulVec_sub,hk,sub_self]
  have h3 : ToeF S k := by
    intro p l' hp i'; change rootC S (b+d₀*ᵥ l) (p,l',i')=0
    have hh : ∀ (x y : Form f 1), rootC S (x+y)=rootC S x+rootC S y := fun _ _ => Matrix.mulVec_add ..
    rw [hh,Pi.add_apply,hb p l' hp, toe_up S hl p l' hp,zero_add]
  have ht : a+b+d₀*ᵥ (l-w)=x+k := by unfold x k; rw [Matrix.mulVec_sub]; abel
  have hd : v+B₀*ᵥ(l-w)=0 := by rw [Matrix.mulVec_sub,hh]; abel
  rw [ht,hd]; apply le_trans (rates S x k h1 h2 h3) (le_of_eq ?_)
  rw [← ht,Matrix.mulVec_add D (a+b),Matrix.mulVec_add M (a+b),shadow,duel,add_zero,
    show B₀*ᵥ (l-w)=-v from eq_neg_of_add_eq_zero_right hd,Matrix.mulVec_neg,← sub_eq_add_neg]
end YM.AnalyticNext.QuarticMatch.Hessian
