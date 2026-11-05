import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Counting
import YM.AnalyticNext.QUARTIC_MATCH.Pre.GaugeDir
import YM.Next.FREE_KERNELS.Dispatch

/-!
# The actual patch matrices in finite alias basis
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Hessian
open Filter Function Lattice Laurent Bloch Exterior Matrix Precision RG Work.F06
open Pre.Centered YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ComplexConjugate

variable {c f : Side} (S : StepData c f)

section run
variable {ι m k l : Type*} [Fintype ι] [Fintype m]
abbrev cubeF (m : Type*) := Co c (Co S.patch.L m)

def inverseC [DecidableEq ι] (r : Matrix m ι ℂ) (n : ℂ) : Matrix ι m ℂ := n⁻¹ • rᴴ
variable [DecidableEq m] [DecidableEq ι] {n : Side}
lemma inverts {r : Matrix m ι ℂ} (h : Crew r (stageVolume n)) (x : m→ℂ) (y : ι→ℂ) :
    r*ᵥ (inverseC r (stageVolume n) *ᵥ x)=x ∧ inverseC r (stageVolume n)*ᵥ (r*ᵥ y)=y := by
  rw [inverseC,mulVec_mulVec,mulVec_mulVec,Matrix.smul_mul,Matrix.mul_smul,h.2.2,h.2.1]; simp [stage_ne]
lemma transacts {r : Matrix m ι ℂ} (h : Crew r (stageVolume n)) (x : ι→ℂ) : ell2 (r*ᵥ x)= (n.val:ℝ)^2 * ell2 x := by
  have he := calc
    (((ell2 (r*ᵥ x))^2 : ℝ):ℂ) = dotProduct (star (r*ᵥ x)) (r*ᵥ x) := (complex_count _).symm
    _ = _ := by rw [adjoint_area, mulVec_mulVec,h.2.2,smul_mulVec,Matrix.one_mulVec,dotProduct_smul,complex_count]
  have hv : (ell2 (r*ᵥ x))^2=(n.val:ℝ)^4*ell2 x^2 := Complex.ofReal_injective (by push_cast at he ⊢; exact he)
  rw [show (n.val:ℝ)^4*ell2 x^2=((n.val:ℝ)^2*ell2 x)^2 from by ring] at hv
  exact sq_eq_sq₀ (ell_nonneg _) (mul_nonneg (sq_nonneg _) (ell_nonneg _)) |>.mp hv
omit [DecidableEq ι] [DecidableEq m] [Fintype m] in
lemma woven [Fintype k] [Fintype l] {r : Matrix m k ℂ} {s : Matrix ι l ℂ} {A : Matrix m ι ℝ}
    {B : Matrix k l ℂ} (h : Runs r s A B) (x : l→ℂ) : approached A*ᵥ (s*ᵥ x)=r*ᵥ (B*ᵥ x) := by rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,h]
omit [DecidableEq ι] [DecidableEq m] [Fintype m] in
lemma fiber_at (r : Site n→Matrix m ι ℂ) (x : Co n ι→ℂ) (i : Site n) (j) :
    (fiber r*ᵥ x) (i,j)=(r i*ᵥ (fun a => x (i,a))) j := by simp [Matrix.mulVec,dotProduct, fiber,Fintype.sum_prod_type,ite_mul]
omit [DecidableEq ι] [DecidableEq m] [Fintype m] in
lemma gather (m : Momentum→Matrix m ι ℂ) (x : cubeF S ι→ℂ) (p l i) :
    (braceAll S.ratio m*ᵥx) (p,l,i)=(m (aliasAt (mon p) l)*ᵥ (fun a => x (p,l,a))) i := by
  rw [braceAll,fiber_at,fiber_at]; rfl
omit [DecidableEq ι] [DecidableEq m] in
lemma gather_back (m : Momentum→Matrix m ι ℂ) (x : cubeF S _→ℂ) (p l i) :
    ((braceAll S.ratio m)ᴴ *ᵥ x) (p,l,i)=((m (aliasAt (mon p) l))ᴴ *ᵥ (fun a => x (p,l,a))) i := by
  rw [braceAll,fiber_H,fiber_at,fiber_H,fiber_at]; rfl
omit [DecidableEq ι] [DecidableEq m] [Fintype m] in
lemma up_at (m : Site n→Matrix m ι ℂ) (x : Co n ι→ℂ) (i) :
    (upAlias m *ᵥ x) i=∑ p : Site n, (m p *ᵥ fun x' => x (p,x')) i := by simp [upAlias,mulVec,dotProduct,Fintype.sum_prod_type]
end run

section ops
local notation "M" => S.patch.L
abbrev fineBook (r : ℕ) := readings S.ratio (TypeFace r)
abbrev coarseBook (c : Side) (r : ℕ) := rotations c (TypeFace r)
abbrev forward (r : ℕ) := braceAll S.ratio (signal 1 r)
abbrev paletteRun := fiber fun p : Site c => upAlias fun l : Site M => massFilter S.patch (aliasAt (mon p) l) • (1:Frequency 0 0)
abbrev meanRun := fiber fun p : Site c => upAlias fun l : Site M => (S.patch.L.val:ℂ) •
    mask 1 fun i => pullLine S.patch i (aliasAt (mon p) l)
lemma manages (r : ℕ) : Runs (fineBook S (r+1)) (fineBook S r) (d r f) (forward S r) := (cobound_true r).fine S.ratio S.patch.odd_side
lemma controls (r : ℕ) : Runs (fineBook S r) (fineBook S (r+1)) (d r f).transpose (forward S r)ᴴ := by
  have he := (manages S r).back (readings_crew ..) (readings_crew ..); rwa [div_self (stage_ne f),one_smul] at he
lemma mean_runs : Runs (coarseBook c 1) (fineBook S 1) (Precision.mean S) (meanRun S) := patch_service S
lemma contracted_real (a : Body 0 f → ℂ) (x : Body 0 c) : (approached (palette S) *ᵥ a) x=
    ∑ y : S.patch.Points, (S.patch.weight y:ℂ)*a (atPoint S x.1 y,vac) := by
  apply Complex.ext
  · have hm := palette_site S (fun i => (a i).re) x
    simpa [approached, Matrix.mulVec,dotProduct,Complex.mul_re,Complex.re_sum] using hm
  have hm := palette_site S (fun i => (a i).im) x; simpa [approached,Matrix.mulVec,dotProduct,Complex.mul_im,Complex.im_sum] using hm
lemma via_at (p : Site c) (x : Site c) (l : Site M) (y : S.patch.Points) :
    let q := aliasAt (mon p) l
    mode q (lift (atPoint S x y)) = mode q y.val*cell p x := by
  intro q
  have he : mode q (lift (atPoint S x y)) = mode q (y.val+ S.patch.L.val • lift x) := by
    apply mesh_alias S.ratio
    rw [wrap_lift,map_add]; rfl
  rw [he,mode_shift,← mode_scale,show S.patch.L.val • q=_ from alias_scale (mon p) l,mode_phase,mode_periodic,mul_one]; rfl
lemma contract : Runs (coarseBook c 0) (fineBook S 0) (palette S) (paletteRun S) := by
  unfold Runs; ext ⟨x,b⟩ ⟨p,l,i⟩
  rw [vac_only i,vac_only b]
  unfold coarseBook paletteRun
  change (approached (palette S) * fineBook S 0) (x,vac) (p,l,vac) =
    (rotations c (TypeFace 0) * fiber (fun p : Site c => upAlias (fun l : Site S.ratio.count =>
      massFilter S.patch (aliasAt (mon p) l) • (1: Frequency 0 0)))) (x,vac) (p,l,vac)
  rw [rot_fiber]; let q := aliasAt (mon p) l
  change (approached (palette S)*ᵥ fun v => fineBook S 0 v (p,l,vac)) (x,vac)=cell p x*((massFilter S.patch q) • (1:Frequency 0 0)) vac vac
  rw [contracted_real]
  simp only [fineBook,sample,if_true,Matrix.smul_apply, Matrix.one_apply_eq,smul_eq_mul,mul_one];
  change ∑ y, (S.patch.weight y:ℂ)* mode q (lift (atPoint S x y))=cell p x*massFilter S.patch q
  simp_rw [show ∀ y, mode q (lift (atPoint S x y)) = _ from fun y => via_at S p x l y]
  simp_rw [← mul_assoc,← Finset.sum_mul,pays_roll]; exact mul_comm ..
end ops
end YM.AnalyticNext.QuarticMatch.Hessian
