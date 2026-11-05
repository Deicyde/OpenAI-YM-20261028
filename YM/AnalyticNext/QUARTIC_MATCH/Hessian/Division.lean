import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Voltage
import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Wire

/-!
# Low / high in the finer periodic cochain fields

Orthogonality. Include even-period end representatives consistently. Real
field decompositions not needed here (just do estimates on the complexification).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Hessian
open Filter Function Lattice Laurent Bloch Exterior Matrix Precision RG
open Pre.Centered YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ComplexConjugate InnerProductSpace

variable {c f : Side} (S : StepData c f)
abbrev Spec (r : ℕ) := Co c (Co S.ratio.count (TypeFace r))→ℂ
abbrev Form (n : Side) (r : ℕ) := Body r n→ℂ
abbrev drawC (n : Side) (r : ℕ) := approached (d r n)

def rootC {r : ℕ} (x : Form f r) := inverseC (fineBook S r) (stageVolume f)*ᵥ x
local notation "M" => S.ratio.count
local notation "L" => (S.patch.L.val:ℝ)

def TopF {r : ℕ} (x : Form f r) := ∀ p : Site c,∀ i, rootC S x (p,(0:Site M),i)=0
def ToeF {r : ℕ} (x : Form f r) := ∀ (p : Site c) (l : Site M), l≠0 → ∀ i, rootC S x (p,l,i)=0

section rules
variable {r : ℕ}
lemma roundC (x : Form f r) : fineBook S r*ᵥrootC S x=x := (inverts (readings_crew _ _) x 0).1
lemma roundH (x : Spec S r) : rootC S (fineBook S r*ᵥ x)=x := (inverts (readings_crew _ _) 0 x).2
lemma totalC (x : Form f r) : ell2 x=(f.val:ℝ)^2 * ell2 (rootC S x) := by
  have he := transacts (readings_crew S.ratio (TypeFace r)) (rootC S x); rwa [show readings S.ratio (TypeFace r) *ᵥ _ = _ from roundC S x] at he
lemma root_up (x : Form f r) : rootC S (drawC f r *ᵥ x)=forward S r *ᵥ rootC S x := by
  calc
    _ = rootC S (drawC f r*ᵥ (fineBook S r*ᵥ rootC S x)) := by rw [roundC]
    _ = _ := by rw [show _ *ᵥ _ = _ from woven (manages S r) (rootC S x),roundH]
lemma root_down (x : Form f (r+1)) : rootC S ((drawC f r)ᴴ *ᵥ x)=(forward S r)ᴴ *ᵥ rootC S x := by
  unfold drawC; rw [← approach_H]
  calc
    _ = rootC S (approached (d r f).transpose*ᵥ (fineBook S (r+1)*ᵥ rootC S x)) := by rw [roundC]
    _ = _ := by rw [woven (controls S r),roundH]

def chamber (x : Spec S r) (p : Site c) (l : Site M) : TypeFace r → ℂ := fun i => x (p,l,i)
lemma chamber_up (x : Form f r) (p : Site c) (l : Site M) : chamber S (rootC S (drawC f r *ᵥ x)) p l =
    signal 1 r (aliasAt (mon p) l) *ᵥ chamber S (rootC S x) p l := by
  rw [root_up]; exact funext fun i => gather S (signal 1 r) _ p l i
lemma chamber_down (x : Form f (r+1)) (p : Site c) (l : Site M) : chamber S (rootC S ((drawC f r)ᴴ *ᵥ x)) p l =
    (signal 1 r (aliasAt (mon p) l))ᴴ *ᵥ chamber S (rootC S x) p l := by
  rw [root_down]; exact funext fun i => gather_back S _ _ _ _ _
lemma splitPower (x : Form f r) : ell2 x ^ 2 = ((f.val:ℝ)^2)^2 * ∑ p,∑ l, ell2 (chamber S (rootC S x) p l)^2 := by
  rw [totalC S x,mul_pow]; congr 1
  rw [square_length, Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]; simp_rw [square_length]; rfl
lemma top_up {x : Form f r} (h : TopF S x) : TopF S (drawC f r*ᵥ x) := by
  intro p i
  change chamber S (rootC S (drawC f r *ᵥ x)) p 0 i=0; rw [chamber_up,show chamber S (rootC S x) p 0=0 from funext (h p), mulVec_zero]; rfl
lemma top_down {x : Form f (r+1)} (h : TopF S x) : TopF S ((drawC f r)ᴴ *ᵥ x) := by
  intro p i
  change chamber S (rootC S ((drawC f r)ᴴ *ᵥ x)) p 0 i=0; rw [chamber_down,show chamber S (rootC S x) p 0=0 from funext (h p), mulVec_zero]; rfl
lemma toe_up {x : Form f r} (h : ToeF S x) : ToeF S (drawC f r *ᵥ x) := by
  intro p l hl i
  change chamber S (rootC S (drawC f r *ᵥ x)) p l i=0; rw [chamber_up,show chamber S (rootC S x) p l=0 from funext (h p l hl), mulVec_zero]; rfl

lemma top_left {x y : Form f r} (h : TopF S x) (hh : TopF S y) : TopF S (x-y) := by
  intro p i
  rw [rootC,Matrix.mulVec_sub,Pi.sub_apply,sub_eq_zero]; exact (h p i).trans (hh p i).symm

lemma apart {x y : Form f r} (h : TopF S x) (g : ToeF S y) : ell2 (x+y)^2=ell2 x^2+ell2 y^2 := by
  rw [splitPower,splitPower,splitPower,← mul_add]; congr 1
  rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun l _ => ?_
  rw [show chamber S (rootC S (x+y)) p l=chamber S (rootC S x) p l+chamber S (rootC S y) p l from by unfold rootC; rw [Matrix.mulVec_add]; rfl]
  by_cases he : l=0
  · subst l; rw [show chamber S (rootC S x) p 0=0 from funext (h p)]; simp
  rw [show chamber S (rootC S y) p l=0 from funext (g p l he)]; simp
lemma growth {x y : Form f r} (h : TopF S x) (g : ToeF S y) : ell2 x ≤ ell2 (x+y) ∧ ell2 y ≤ ell2 (x+y) := by
  have he := apart S h g; have ha := ell_nonneg (x+y); constructor <;> nlinarith
lemma split_from (x : Form f r) : ∃ a b : Form f r, TopF S a ∧ ToeF S b ∧ a+b=x := by
  let y := rootC S x
  let T : Spec S r := fun i => if i.2.1=0 then 0 else y i
  let U := fineBook S r
  refine ⟨U*ᵥ T,U*ᵥ (y-T),?_,?_,?_⟩
  · intro p i; unfold U; rw [roundH]; exact if_pos rfl
  · intro p l hl i; unfold U; rw [roundH,Pi.sub_apply,sub_eq_zero]; exact (if_neg hl).symm
  rw [← Matrix.mulVec_add,add_sub_cancel]; exact roundC S x
end rules

lemma light_top {x : Form f 0} (h : TopF S x) : (lateFee/L)*ell2 x ≤ ell2 (drawC f 0*ᵥ x) := by
  apply (sq_le_sq₀ (by apply mul_nonneg (div_nonneg late_pos.le (side_pos S.patch.L).le) (ell_nonneg _)) (ell_nonneg _)).mp
  rw [mul_pow, splitPower S,splitPower S, mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [Finset.mul_sum]; refine Finset.sum_le_sum fun p _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_le_sum fun l _ => ?_
  by_cases he : l=0
  · subst l; rw [show chamber S (rootC S x) p 0=0 from funext (h p), ell_zero]; simpa using sq_nonneg _
  rw [chamber_up,thermal0]; exact mul_le_mul_of_nonneg_right (cold S p l he) (sq_nonneg _)
lemma toe_one {x : Form f 1} (h : ToeF S x) : ell2 ((drawC f 0)ᴴ *ᵥ x) ≤ earlyFee/L*ell2 x := by
  apply (sq_le_sq₀ (ell_nonneg _) (mul_nonneg (div_nonneg early_pos.le (side_pos S.patch.L).le) (ell_nonneg _))).mp
  rw [mul_pow,splitPower S,splitPower S, mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]; refine Finset.sum_le_sum fun p _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_le_sum fun l _ => ?_
  rw [chamber_down S]
  by_cases he : l=0
  · subst l
    apply le_trans _ (mul_le_mul_of_nonneg_right (chilly S p) (sq_nonneg _))
    rw [← thermal1]; exact le_add_of_nonneg_left (sq_nonneg _)
  rw [show chamber S (rootC S x) p l = 0 from funext (h p l he)]; simp
lemma top_one {x : Form f 1} (h : TopF S x) (H : (drawC f 0)ᴴ *ᵥ x = 0) :
    lateFee/L*ell2 x ≤ ell2 (drawC f 1 *ᵥ x) := by
  apply (sq_le_sq₀ (mul_nonneg (div_nonneg late_pos.le (side_pos S.patch.L).le) (ell_nonneg _)) (ell_nonneg _)).mp
  rw [mul_pow,splitPower S,splitPower S, mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]; refine Finset.sum_le_sum fun p _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_le_sum fun l _ => ?_
  rw [chamber_up S]
  by_cases he : l=0
  · subst l; rw [show chamber S (rootC S x) p 0=0 from funext (h p)]; simp
  apply le_trans (mul_le_mul_of_nonneg_right (show (lateFee/L)^2≤volt (aliasAt (mon p) l) from cold S p l he) (sq_nonneg _))
  rw [← thermal1, ← chamber_down S x, H,show chamber S (rootC S (0:Form f 0)) p l=0 from by unfold rootC; rw [Matrix.mulVec_zero]; rfl]; simp

lemma top_available {x : Form f 0} (h : TopF S x) : ∃ a,TopF S a ∧ (drawC f 0)ᴴ *ᵥ (drawC f 0 *ᵥ a) = x := by
  let K (p : Site c) (l : Site M) := volt (aliasAt (mon p) l)
  let w : Spec S 0 := fun i => ((K i.1 i.2.1:ℂ))⁻¹ * rootC S x i
  let a := fineBook S 0 *ᵥ w
  refine ⟨a,fun p i => by rw [show rootC S a=_ from roundH S w]; simp only [w,h p i,mul_zero],?_⟩
  have he : rootC S ((drawC f 0)ᴴ *ᵥ (drawC f 0 *ᵥ a))=rootC S x := by
    funext ⟨p,l,i⟩
    change chamber S (rootC S ((drawC f 0)ᴴ *ᵥ (drawC f 0 *ᵥ a))) p l i=_
    rw [chamber_down,chamber_up,Matrix.mulVec_mulVec,heat0,smul_mulVec,one_mulVec,Pi.smul_apply,
      show rootC S a=_ from roundH S w]
    change (K p l:ℂ)*((K p l:ℂ)⁻¹ * rootC S x (p,l,i))=_
    by_cases h' : l=0
    · subst l; rw [h]; simp
    have hm : 0<K p l := lt_of_lt_of_le (pow_pos (div_pos late_pos (side_pos S.patch.L)) _) (cold S p l h')
    exact mul_inv_cancel_left₀ (by exact_mod_cast hm.ne') _
  exact ((roundC S _).symm.trans ((congr_arg (fineBook S 0 *ᵥ ·) he).trans (roundC S x)))
end YM.AnalyticNext.QuarticMatch.Hessian
