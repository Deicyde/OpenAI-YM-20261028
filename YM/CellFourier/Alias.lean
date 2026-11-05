import YM.CellFourier.Mesh

/-!
# Centered alias phases in one physical cell

Complex as well as real. `(aliasBlock L α)` works color/typewise on ANY
shape. No phase factor dropping when complex. Spectra & bounds of such blocks
must separately weight the total column. In particular ordinary adjoint
identities only at real p. Cross periodic wave phase convention compatible
with subdivision Ratio.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bloch
open Lattice Laurent Matrix Function Filter Set Complex
open scoped Topology BigOperators ComplexConjugate ContDiff Matrix.Norms.Frobenius

variable {L : Side} {α β γ : Type*}

def aliasAt (p : Momentum) (l : Site L) : Momentum := (L.val:ℂ)⁻¹ • p+mon l

@[simp] lemma alias_scale (p : Momentum) (l : Site L) : L.val • aliasAt p l=p+reciprocal (Lattice.lift l) := by
  unfold aliasAt; rw [smul_add,mon_phase,← Nat.cast_smul_eq_nsmul ℂ, smul_smul,mul_inv_cancel₀ (side_ne _),one_smul]

lemma alias_conj (p : Momentum) (l : Site L) : aliasAt (star p) l = star (aliasAt p l) := by
  unfold aliasAt
  simp [add_comm]

/-- normalization P_r=Σ phases P_ℓ -/
def aliasBlock (L : Side) (α : Type*) [DecidableEq α] (p : Momentum) : Matrix (Site L × α) (Site L × α) ℂ :=
    of fun x y => if x.2=y.2 then mode (aliasAt p y.1) (lift x.1) else 0

lemma alias_comp (p : Momentum) (l k : Site L) : mode (aliasAt p l) (lift k) = mode ((L.val:ℂ)⁻¹ • p) (lift k)*cell l k := by rw [aliasAt,mode_phase]; rfl

lemma alias_adj (p : Momentum) (l k : Site L) : star (mode (aliasAt (star p) l) (lift k)) = (mode (aliasAt p l) (lift k))⁻¹ := by rw [alias_conj,mode_adjoint,mode_opposite]

/-- Analytic star, valid for complex p; beware product shape. -/
def returned (f : Momentum → Matrix α β ℂ) (p : Momentum) := Matrix.conjTranspose (f (star p))
variable (L) (α : Type*) [Fintype α] [DecidableEq α]

theorem straightens (p : Momentum) : returned (aliasBlock L α) p * aliasBlock L α p=(L.val:ℂ)^4 • 1 := by
  ext ⟨l,a⟩ ⟨r,b⟩
  simp only [returned,mul_apply,conjTranspose_apply,aliasBlock,of_apply, Matrix.smul_apply,Matrix.one_apply,Fintype.sum_prod_type]
  rcases eq_or_ne a b with h|h
  · subst b
    simp only [Prod.mk.injEq,and_true,apply_ite (star : ℂ → ℂ),star_zero, ite_mul,mul_ite,
      zero_mul,mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      smul_eq_mul,mul_one]
    simp_rw [alias_adj,alias_comp]
    have he (x : Site L) : (mode ((L.val:ℂ)⁻¹ • p) (lift x) * cell l x)⁻¹ * (mode ((L.val:ℂ)⁻¹ • p) (lift x)*cell r x)=cell r x*(cell l x)⁻¹ := by field_simp
    simp_rw [he]; exact (orthogonal r l).trans (by simp [eq_comm])
  simp only [Prod.mk.injEq,h,and_false, ↓reduceIte,smul_zero]
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_; split_ifs <;> simp_all

theorem straighten' (p : Momentum) : aliasBlock L α p * returned (aliasBlock L α) p=(L.val:ℂ)^4 • 1 := by
  let a : ℂ := (L.val:ℂ)^4
  have hA : a≠0 := pow_ne_zero _ (side_ne _)
  have he : a⁻¹ • returned (aliasBlock L α) p * aliasBlock L α p=1 := by rw [smul_mul_assoc,straightens,← show a= _ from rfl, smul_smul, inv_mul_cancel₀ hA,one_smul]
  have hh := mul_eq_one_comm.mp he
  change _ = a • 1
  conv_rhs => rw [← hh]
  rw [mul_smul_comm, smul_smul, mul_inv_cancel₀ hA,one_smul]

/-- kills mistaken unit factor in P-star P in one cell. -/
theorem energy {β γ : Type*} (p : Momentum) (A : Momentum → Matrix (Site L × α) β ℂ) (B : Momentum → Matrix (Site L × α) γ ℂ) :
    returned (fun x => aliasBlock L α x * A x) p * (aliasBlock L α p * B p) = (L.val:ℂ)^4 • (returned A p * B p) := by
  unfold returned; simp only [Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (B p), show Matrix.conjTranspose _ * _= _ from straightens L α p]
  simp
end YM.Bloch
