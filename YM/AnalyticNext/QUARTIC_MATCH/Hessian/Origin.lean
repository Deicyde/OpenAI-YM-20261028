import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Division
import YM.Work.B04

/-!
# Principal bounds against true mean and palette
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Hessian
open Filter Function Lattice Laurent Bloch Exterior Matrix Precision RG
open Pre.Centered YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ComplexConjugate InnerProductSpace
variable {c f : Side} (S : StepData c f)
local notation "M" => S.ratio.count
local notation "L" => (S.ratio.count.val:ℝ)
local notation "F" => (f.val:ℝ)
local notation "C" => (c.val:ℝ)

section chamber
variable {r s : ℕ}
def perch (z : Form c s) (p : Site c) := fun i => z (p,i)

variable {D : Matrix (Body s c) (Body r f) ℝ} {E : (p : Site c) → Site S.ratio.count → Frequency s r}
    (h : Runs (coarseBook c s) (fineBook S r) D (fiber (fun i => upAlias (E i)))) {x : Form f r}
    (hx : ToeF S x)
include hx
lemma funds_low (p) :
    perch (fiber (fun i => upAlias (E i))*ᵥ rootC S x) p= E p 0 *ᵥ chamber S (rootC S x) p 0 := by
  funext i; rw [perch,fiber_at,up_at, Finset.sum_eq_single (0:Site M)]; rfl
  · intro l _ hl
    rw [show (fun a : TypeFace r => rootC S x (p,l,a))=0 from funext (hx p l hl), mulVec_zero]; rfl
  simp

include h
lemma counts_low (B : ℝ) (hb : 0 ≤ B) (hC : ∀ p y, B*ell2 y ≤ ell2 (E p 0*ᵥ y)) :
    B*ell2 x ≤ L^2*ell2 (approached D *ᵥ x) := by
  have hk : ell2 (approached D *ᵥ x)=C^2*ell2 (fiber (fun i => upAlias (E i))*ᵥ rootC S x) := by
    have he : approached D *ᵥ x=coarseBook c s *ᵥ (fiber (fun i => upAlias (E i))*ᵥ rootC S x) := by
      have he := woven h (rootC S x); rwa [roundC] at he
    rw [he]; exact transacts (rotations_crew ..) _
  have he : L*C=F := by rw [mul_comm]; exact_mod_cast S.ratio.exact_size.symm
  rw [totalC S x,hk,mul_left_comm B,← mul_assoc (L^2),← mul_pow,he]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (sq_le_sq₀ (mul_nonneg hb (ell_nonneg _)) (ell_nonneg _)).mp
  rw [mul_pow,square_length,square_length,Fintype.sum_prod_type,Fintype.sum_prod_type,Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (0:Site M)]
  · have H := pow_le_pow_left₀ (mul_nonneg hb (ell_nonneg _)) (hC i (chamber S (rootC S x) i 0)) 2
    rw [← funds_low S hx, mul_pow,square_length,square_length] at H; exact H
  · intro p _ hp; simp only [hx i p hp,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
  simp

omit hx
/-- Correlation: low plane still covers all coarse site values. -/
lemma fills (ht : ∀ p, Surjective (fun v => E p 0*ᵥ v)) (y : Form c s) :
    ∃ a : Form f r, ToeF S a ∧ approached D*ᵥ a = y := by
  let R := coarseBook c s
  let u := inverseC R (stageVolume c)*ᵥ y
  choose z hz using (fun p : Site c => ht p (perch u p))
  let v : Spec S r := fun i => if i.2.1=0 then z i.1 i.2.2 else 0
  let a := fineBook S r*ᵥ v
  have he : rootC S a=v := roundH S v
  have ha : ToeF S a := by intro p l hl j; rw [he]; exact if_neg hl
  refine ⟨a,ha,?_⟩
  have hc : fiber (fun i => upAlias (E i))*ᵥ v=u := by
    funext ⟨p,i⟩
    have H := funds_low (E:=E) S ha p
    rw [he,show chamber S v p 0=z p from funext fun i => if_pos rfl] at H
    exact congr_fun (H.trans (hz p)) i
  unfold a; rw [woven h,hc]; exact (inverts (rotations_crew ..) _ 0).1
end chamber

def colorPrice (j : ℕ) := pass j*plankMin
lemma color_pos (j : ℕ) : 0 < colorPrice j := mul_pos (pass_pos j) plankMin_pos

abbrev package (p : Site c) (l : Site M) := massFilter S.patch (aliasAt (mon p) l)
abbrev touch (p : Site c) (l : Site M) := package S p l • (1:Frequency 0 0)
abbrev crossline (p : Site c) (l : Site M) := (S.patch.L.val:ℂ) •
    mask 1 (fun i => pullLine S.patch i (aliasAt (mon p) l))

lemma covalue (p) (y : TypeFace 0→ℂ) : pass S.patch.J * ell2 y ≤ ell2 (touch S p 0 *ᵥ y) := by
  unfold touch; rw [smul_mulVec,one_mulVec,ell_smul]; exact mul_le_mul_of_nonneg_right (credit S p) (ell_nonneg _)
lemma traverse (p) (y : TypeFace 1→ℂ) : (L*colorPrice S.patch.J)*ell2 y ≤ ell2 (crossline S p 0 *ᵥ y) := by
  have hh (i : TypeFace 1) : (mask 1 (fun a => pullLine S.patch a (aliasAt (mon p) (0:Site M)))*ᵥ y) i =
      pullLine S.patch (axisEquiv.symm i) (aliasAt (mon p) (0:Site M))*y i := by
    unfold Matrix.mulVec dotProduct; simp_rw [mask_value,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rw [crossline,smul_mulVec,ell_smul,norm_natCast, mul_assoc]
  apply mul_le_mul_of_nonneg_left (show colorPrice _*ell2 y ≤ _ from ?_) (side_pos S.patch.L).le
  apply (sq_le_sq₀ (mul_nonneg (color_pos _).le (ell_nonneg _)) (ell_nonneg _)).mp; rw [mul_pow,square_length,square_length,Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _; rw [hh,norm_mul,mul_pow]; exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (color_pos _).le (credit_start S p _) 2) (sq_nonneg _)

lemma fare (x : Form f 0) (h : ToeF S x) : pass S.patch.J*ell2 x ≤ L^2*ell2 (approached (palette S)*ᵥ x) :=
    counts_low S (E:=touch S) (contract S) h _ (pass_pos _).le (covalue S)
lemma fare_one (x : Form f 1) (h : ToeF S x) : colorPrice S.patch.J*ell2 x ≤ L*ell2 (approached (Precision.mean S)*ᵥ x) := by
  have he := counts_low S (E:=crossline S) (mean_runs S) h (L*colorPrice S.patch.J) (mul_nonneg (by positivity) (color_pos _).le) (traverse S)
  rw [pow_two,mul_assoc,mul_assoc] at he; exact le_of_mul_le_mul_left he (side_pos M)
lemma supplied (y : Form c 0) : ∃ a,ToeF S a ∧ approached (palette S)*ᵥ a=y := by
  apply fills S (E:=touch S) (contract S)
  intro p x
  have he : package S p 0 ≠ 0 := norm_pos_iff.mp ((pass_pos S.patch.J).trans_le (credit S p))
  refine ⟨(package S p 0)⁻¹ • x,?_⟩
  change touch S p 0 *ᵥ ((package S p 0)⁻¹ • x)=x
  rw [touch, smul_mulVec,one_mulVec,smul_smul,mul_inv_cancel₀ he,one_smul]
end YM.AnalyticNext.QuarticMatch.Hessian
