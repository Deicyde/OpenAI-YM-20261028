import YM.Extra.WILSON_STARTUP.Transform
import YM.Work.F08.Rows

/-!
# Analytic row reflection turning the cutoff kinetic columns onto direct forms

Use `Z = full + stack(1,0)`, reflect by `2 Z (ZᵀZ)⁻¹ Zᵀ - 1` at physical
real coordinates. Isometric everywhere, gives `stack(1,0) d` on full*d
when metric*d = d. Gram inverse analytic without polar decomposition of the
given ell! Preserves harmonic, period, and both counting directions. This is
an auxiliary delivery for linear tower choice, NOT a nonlinear field rotation
or permission to forget paths in mainTerm. Cost width is pre-L and not
inferred from an inverse at fixed period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Polar
open Matrix Function Filter RG Wilson Lattice Bloch Laurent Work Work.F08 Precision Exterior Change
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {B : Bed} {p : Clip} {n : Side}

abbrev AxisRows := Row Layers2 (TypeFace 2)
abbrev Kinetic := Row (TypeFace 2) (TypeFace 2)
abbrev LiftRows := Row Layers2 Layers2
abbrev AxisBlock (n : Side) := Matrix (Co n Layers2) (Body 2 n) ℝ
abbrev FormBlock (n : Side) := Matrix (Body 2 n) (Body 2 n) ℝ

def upper (n : Side) : AxisBlock n := Craft.stack (1 : FormBlock n) (0 : FormBlock n)

def zRows (B : Bed) (p : Clip) : AxisRows := stackRows (scaleRows (Real.sqrt p.direct + 1) (unitRow _)) B.roots

def projector (B : Bed) (p : Clip) (P : Kinetic) : LiftRows := composeRows (composeRows (zRows B p) P) (transRows (zRows B p))
def orient (B : Bed) (p : Clip) (P : Kinetic) : LiftRows := minusRows (scaleRows 2 (projector B p P)) (unitRow _)

lemma fullStack (B : Bed) (p : Clip) (n : Side) : B.full p n = Craft.stack ((Real.sqrt p.direct) • (1 : FormBlock n)) (B.roots.acts n) := rfl

lemma stack_add (A B C D : FormBlock n) : Craft.stack A B + Craft.stack C D = Craft.stack (A+C) (B+D) := by ext ⟨x,i⟩ j; cases i <;> rfl
lemma stack_pair (A B C D : FormBlock n) : (Craft.stack A B)ᵀ * Craft.stack C D = Aᵀ * C + Bᵀ * D := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fintype.sum_prod_type]; simp_rw [Fintype.sum_sum_type,Finset.sum_add_distrib]; rfl

lemma z_acts (B : Bed) (p : Clip) (n : Side) : (zRows B p).acts n = B.full p n + upper n := by
  rw [zRows,acts_stack,acts_scale,acts_unit,fullStack,upper,stack_add, add_zero, add_smul,one_smul]

lemma z_positive (B : Bed) (p : Clip) (n : Side) : let M := (zRows B p).acts n
    Mᵀ * M = (Real.sqrt p.direct+1)^2 • 1 + ((B.roots.acts n)ᵀ * B.roots.acts n) := by
  dsimp; rw [zRows,acts_stack,acts_scale,acts_unit,stack_pair, transpose_smul,transpose_one, Matrix.smul_mul, Matrix.one_mul,smul_smul,← sq]

lemma same_exact (B : Bed) (p : Clip) (n : Side) {η Ω : ℝ} (h : Floor B p n η Ω) (hh : B.diagonal.acts n=1) :
    ((zRows B p).acts n)ᵀ * (B.full p n*d 1 n) = ((zRows B p).acts n)ᵀ*(upper n*d 1 n) := by
  rw [z_acts,Matrix.transpose_add,Matrix.add_mul,Matrix.add_mul]; repeat rw [← Matrix.mul_assoc]
  simp only [h.roots, h.same,hh,Matrix.one_mul]; simp only [fullStack,upper,stack_pair,Matrix.transpose_one,Matrix.transpose_zero, Matrix.zero_mul,
    Matrix.one_mul, transpose_smul, Matrix.mul_zero,Matrix.mul_one, add_zero]
  abel

section reflection
variable {ι τ ρ : Type} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]
    {Z : Matrix ι τ ℝ} {P : Matrix τ τ ℝ}
omit [DecidableEq ι] in
lemma projector_sym (h : P*(Zᵀ*Z)=1) : (Z*P*Zᵀ)ᵀ = Z*P*Zᵀ := by
  have hi := _root_.mul_eq_one_comm.mp h
  have ht := congr_arg transpose hi
  rw [transpose_mul,transpose_mul,transpose_transpose,transpose_one, ← h] at ht
  have he := (IsUnit.of_mul_eq_one _ hi).mul_left_inj.mp ht
  rw [transpose_mul,transpose_mul,transpose_transpose,he, ← Matrix.mul_assoc]

omit [DecidableEq ι] in
lemma projector_square (h : P*(Zᵀ*Z)=1) : (Z*P*Zᵀ)*(Z*P*Zᵀ) = Z*P*Zᵀ := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ Zᵀ Z,Matrix.mul_assoc Z P, h, Matrix.mul_one]

lemma orthog (h : P*(Zᵀ*Z)=1) : let X := (2:ℝ) • (Z*P*Zᵀ) - 1; Xᵀ*X=1 := by
  dsimp; simp only [two_smul ℝ, transpose_sub,transpose_one,transpose_add, projector_sym h,Matrix.sub_mul,Matrix.mul_sub,
    Matrix.add_mul,Matrix.mul_add,Matrix.one_mul, Matrix.mul_one,projector_square h]; abel

lemma reflect_exact {A C : Matrix ι ρ ℝ} (h : P*(Zᵀ*Z)=1) (R : Matrix τ ρ ℝ)
    (hS : Z*R = A+C) (hA : Zᵀ*A = Zᵀ*C) : ((2:ℝ) • (Z*P*Zᵀ) - 1)*A = C := by
  have he : A+C=Z*P* (Zᵀ* (A+C)) := by rw [← hS, ← Matrix.mul_assoc _ Z R, ← Matrix.mul_assoc (Z*P),Matrix.mul_assoc Z P (Zᵀ*Z),h, Matrix.mul_one]
  rw [Matrix.mul_add, ← hA, Matrix.mul_add, ← Matrix.mul_assoc,add_comm A] at he
  rw [Matrix.sub_mul, two_smul ℝ,Matrix.add_mul,Matrix.one_mul,← he]; abel
end reflection

lemma strip_z (B : Bed) (p : Clip) {η A : ℝ} (h : B.roots.strip η A) :
    (zRows B p).strip η (max ‖Real.sqrt p.direct + 1‖ A) := by
  have hh := strip_stack (strip_scale (α := TypeFace 2) strip_unit (Real.sqrt p.direct + 1)) h
  rwa [mul_one] at hh

lemma orient_ready (B : Bed) (p : Clip) (P : Kinetic) {A C η : ℝ} (hz : (zRows B p).strip η A) (hP : P.strip η C) (he : 0 < η) :
    let m := (Fintype.card (TypeFace 2) : ℝ)
    (orient B p P).strip η (2*(m*((m*(A*C))*A))+1) ∧ ∀ n : Side,
    let Z := (zRows B p).acts n
    (orient B p P).acts n = (2:ℝ) • (Z * P.acts n * Zᵀ)-1 := by
  have h := strip_compose he.le hz hP
  have hs := strip_compose he.le h (strip_trans hz)
  constructor
  · have hh := strip_minus (strip_scale hs 2) strip_unit
    rw [show ‖(2:ℝ)‖=2 by norm_num] at hh; exact hh
  intro n
  simp only
  rw [orient,projector,acts_minus he.le (strip_scale hs _) strip_unit,acts_scale, acts_unit,
    acts_compose he.le h (strip_trans hz),acts_compose he.le hz hP,acts_trans]

theorem orient_uniform (p : Clip) {A η : ℝ} (hA : 0 ≤ A) (hη : 0 < η) :
    ∃ τ C : ℝ, 0 < τ ∧ 0 ≤ C ∧ ∀ B : Bed, B.roots.strip η A → ∃ S : LiftRows, S.strip τ C ∧
      ∀ n : Side, (S.acts n)ᵀ * S.acts n = 1 ∧ ∀ a v : ℝ, Floor B p n a v → B.diagonal.acts n=1 →
        S.acts n * (B.full p n * d 1 n) = upper n * d 1 n := by
  let e := Real.sqrt p.direct+1
  obtain ⟨C,t,ht,hC,H⟩ := deliver (TypeFace 2) (e^2) η A (by unfold e; positivity) hη hA
  let τ := min η t
  let r := max ‖e‖ A
  let m : ℝ := Fintype.card (TypeFace 2)
  have hτ : 0 < τ := lt_min hη ht
  have hr := (norm_nonneg _).trans (le_max_left ‖e‖ A)
  refine ⟨τ,2*(m*((m*(r*C))*r))+1,hτ,by unfold r m; positivity,fun B h => ?_⟩
  obtain ⟨P,hp,hS⟩ := H _ h
  obtain ⟨hw,hv⟩ := orient_ready B p P (strip_z B p (strip_mono h (min_le_left ..) le_rfl)) (strip_mono hp (min_le_right ..) le_rfl) hτ
  refine ⟨orient B p P, hw,fun n => ?_⟩; rw [hv]
  have hz := hS n; rw [← show _ = e^2 • _ + _ from z_positive B p n] at hz
  exact ⟨orthog hz,fun a v ha hb => reflect_exact hz (d 1 n) (by rw [z_acts,Matrix.add_mul]) (same_exact B p n ha hb)⟩
end YM.WilsonStartup.Polar
