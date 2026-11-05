import YM.Next.FREE_KERNELS.Signal
import YM.PREC.Stacks

/-!
# Bridge arithmetic for exact physical matrices

Unnormalized DFT columns, counting *all* sites and types on the physical
matrix. Ratios positive. The two volume factors in `Runs.back` deliberately
separate (critical crossing a block).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false -- symmetric matrix APIs
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision
open scoped Topology BigOperators ComplexConjugate

variable {m n k m' n' k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype m'] [Fintype n'] [Fintype k']

def Runs (F : Matrix m m' ℂ) (G : Matrix n n' ℂ) (A : Matrix m n ℝ) (B : Matrix m' n' ℂ) := approached A * G=F * B

def Crew [DecidableEq m] [DecidableEq m'] (F : Matrix m m' ℂ) (v : ℂ) := v ≠ 0 ∧ F*Fᴴ=v • 1 ∧ Fᴴ*F=v • 1

namespace Runs
variable {F : Matrix m m' ℂ} {G : Matrix n n' ℂ} {H : Matrix k k' ℂ}
    {A B : Matrix m n ℝ} {X Y : Matrix m' n' ℂ}
lemma product {C : Matrix n k ℝ} {Z : Matrix n' k' ℂ} (h : Runs F G A X) (g : Runs G H C Z) : Runs F H (A*C) (X*Z) := by unfold Runs at *; rw [prom_mul, Matrix.mul_assoc, g,← Matrix.mul_assoc,h,Matrix.mul_assoc]
lemma minus (h : Runs F G A X) (g : Runs F G B Y) : Runs F G (A-B) (X-Y) := by
  unfold Runs at *
  have he : approached (A-B)=approached A-approached B := by ext i j; simp [approached]
  rw [he,Matrix.sub_mul,Matrix.mul_sub,h,g]
lemma smult (h : Runs F G A X) (c : ℝ) : Runs F G (c • A) ((c:ℂ) • X) := by unfold Runs at *; rw [show approached (c • A)=(c:ℂ) • approached A by ext i j; simp [approached],Matrix.smul_mul,Matrix.mul_smul,h]
lemma nil [DecidableEq m] [DecidableEq m'] (F : Matrix m m' ℂ) : Runs F F 1 1 := by unfold Runs; rw [show approached (1:Matrix m m ℝ)=1 by ext i j; by_cases h : i=j <;> simp [approached,Matrix.one_apply,h],Matrix.one_mul,Matrix.mul_one]
lemma back [DecidableEq m] [DecidableEq n] [DecidableEq m'] [DecidableEq n'] (h : Runs F G A X) {v u : ℂ} (hf : Crew F v) (hg : Crew G u) :
    Runs G F A.transpose ((v/u) • Xᴴ) := by
  unfold Runs at *
  have he : Gᴴ*(approached A)ᴴ=Xᴴ*Fᴴ := by rw [← Matrix.conjTranspose_mul,← Matrix.conjTranspose_mul,h]
  have hm : u • ((approached A)ᴴ*F)=v • (G*Xᴴ) := calc
    _ = (u • (1 : Matrix n n ℂ))*((approached A)ᴴ*F) := by rw [Matrix.smul_mul,Matrix.one_mul]
    _ = _ := by rw [← hg.2.1,Matrix.mul_assoc,← Matrix.mul_assoc Gᴴ,he,Matrix.mul_assoc,hf.2.2]; simp
  rw [prom_adj,Matrix.mul_smul]
  apply smul_right_injective _ hg.1; dsimp only; rw [hm,smul_smul,mul_div_cancel₀ _ hg.1]
lemma lands [DecidableEq n] [DecidableEq n'] (h : Runs F G A X) (g : Runs F G B X) {v : ℂ} (hg : Crew G v) : A=B := by
  unfold Runs at *; apply prom_inj; apply smul_right_injective _ hg.1
  have he := congr_arg (fun a => a*Gᴴ) (h.trans g.symm)
  simpa only [Matrix.mul_assoc,hg.2.1,Matrix.mul_smul, Matrix.mul_one] using he
end Runs

def stageVolume (n : Side) := (n.val:ℂ)^4
lemma stage_ne (n : Side) : stageVolume n≠0 := pow_ne_zero _ (side_ne _)
lemma self_swap [DecidableEq m] (F : Matrix m m ℂ) {v : ℂ} (h : v≠0) (g : F*Fᴴ=v • 1) : Fᴴ*F=v • 1 := by
  have he : F*(v⁻¹ • Fᴴ)=1 := by rw [Matrix.mul_smul, g,smul_smul,inv_mul_cancel₀ h,one_smul]
  have hh := mul_eq_one_comm.mp he; rw [Matrix.smul_mul] at hh; rw [← hh, smul_smul,mul_inv_cancel₀ h,one_smul]

lemma rotations_crew (n : Side) (m : Type*) [Fintype m] [DecidableEq m] : Crew (rotations n m) (stageVolume n) := by
  have he := rotations_gram n m; rw [Matrix.star_eq_conjTranspose] at he; exact ⟨stage_ne n,he,self_swap _ (stage_ne n) he⟩
lemma readings_crew {c f : Side} (s : Ratio c f) (m : Type*) [Fintype m] [DecidableEq m] : Crew (readings s m) (stageVolume f) := by
  let G := readings s m; let u := splitCo s m
  have h := readingsGram s m; change G*Gᴴ=_ at h
  refine ⟨stage_ne f,h,?_⟩
  let X := submatrix G u.symm id
  have hh : X*Xᴴ=stageVolume f • 1 := by
    ext i j
    have hx := congr_fun (congr_fun h (u.symm i)) (u.symm j)
    simpa only [X,stageVolume,mul_apply,submatrix_apply,Matrix.conjTranspose_apply,id_eq, Matrix.one_apply,Matrix.smul_apply,u.symm.injective.eq_iff] using hx
  have he := self_swap X (stage_ne _) hh
  ext i j
  have hx := congr_fun (congr_fun he i) j
  simp only [X,G,Matrix.smul_apply, Matrix.mul_apply,Matrix.conjTranspose_apply, Matrix.submatrix_apply,id_eq] at hx ⊢
  rw [← hx]
  exact (Equiv.sum_comp u.symm _).symm
lemma ratio_volume {c f : Side} (s : Ratio c f) : stageVolume f=stageVolume c*stageVolume s.count := by unfold stageVolume; rw [s.exact_size,Nat.cast_mul,mul_pow]

/-- Fiber identities with one fixed fin-type spectral side. -/
lemma fiber_mult {L : Side} (f : Site L → Matrix m n ℂ) (g : Site L → Matrix n k ℂ) :
    fiber f * fiber g=fiber (fun p => f p*g p) := by
  ext ⟨x,i⟩ ⟨y,j⟩
  rw [Matrix.mul_apply,Fintype.sum_prod_type]
  simp only [fiber, Matrix.of_apply,ite_mul,mul_ite,zero_mul,mul_zero]; split_ifs with h
  · subst y; simp [Matrix.mul_apply,eq_comm]
  have he (a : Site L) (b : n) : (if x=a then (if a=y then f x i b*g a b j else 0) else 0)=0 := by split_ifs <;> simp_all
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun a _ => ?_; split_ifs <;> simp_all
lemma fiber_H {L : Side} (f : Site L → Matrix m n ℂ) : (fiber f)ᴴ=fiber (fun i => (f i)ᴴ) := by
  ext ⟨x,i⟩ ⟨y,j⟩
  by_cases h : x=y <;> simp [fiber, *,eq_comm]
lemma fiber_weight {L : Side} (f : Site L → Matrix m n ℂ) (c : ℂ) : c • fiber f=fiber (fun i => c • f i) := by ext i j; simp [fiber, mul_ite]
lemma fiber_less {L : Side} (f g : Site L → Matrix m n ℂ) : fiber f-fiber g=fiber (fun i => f i-g i) := by
  ext ⟨x,i⟩ ⟨y,j⟩
  by_cases h : x=y <;> simp [fiber, *]
lemma fiber_one {L : Side} [DecidableEq m] : fiber (fun _ : Site L => (1:Matrix m m ℂ))=1 := by
  ext ⟨x,i⟩ ⟨y,j⟩; by_cases h : x=y <;> simp [fiber,Matrix.one_apply, *]

def downAlias {L : Side} (u : Site L → Matrix m n ℂ) : Matrix (Co L m) n ℂ := Matrix.of fun i a => u i.1 i.2 a
def upAlias {L : Side} (u : Site L → Matrix m n ℂ) : Matrix m (Co L n) ℂ := Matrix.of fun a i => u i.1 a i.2
lemma alias_inner {L : Side} (f : Site L → Matrix m n ℂ) (g : Site L → Matrix n k ℂ) : upAlias f * downAlias g = ∑ i, f i*g i := by ext i j; simp [upAlias,downAlias,Matrix.sum_apply,Matrix.mul_apply,Fintype.sum_prod_type]
lemma alias_after {L : Side} (f : Site L → Matrix m n ℂ) (g : Site L → Matrix n k ℂ) : fiber f * downAlias g=downAlias (fun i => f i*g i) := by ext ⟨x,i⟩ j; simp [fiber,downAlias,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul]
lemma alias_then {L : Side} (f : Site L → Matrix m n ℂ) (g : Matrix n k ℂ) : downAlias f*g=downAlias fun i => f i*g := by ext i j; rfl
lemma alias_up {L : Side} (f : Site L → Matrix m n ℂ) : (upAlias f)ᴴ= downAlias fun i => (f i)ᴴ := by ext i j; rfl
lemma alias_pay {L : Side} (f : Site L → Matrix m n ℂ) (c : ℂ) : c • downAlias f=downAlias fun i => c • f i := by ext i j; rfl
end YM.Next.Free
