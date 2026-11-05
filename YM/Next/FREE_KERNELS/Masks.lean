import YM.Next.FREE_KERNELS.Account
import YM.Work.F06.Cartan


/-!
# Diagonal exterior multiplier algebra

Sorted-blade, initial-corner convention of `YM.Exterior`; no moving origins.
Ordinary matrix operations. Adjoint used at real p; transpose identities below
can also be used algebraically with independent left multiplier.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate

abbrev Frequency (r s : ℕ) := Matrix (TypeFace r) (TypeFace s) ℂ

def inventory {r : ℕ} (u : TypeFace r) (q : Axis → ℂ) := ∏ i∈u.val, q i

def mask (r : ℕ) (q : Axis → ℂ) : Frequency r r := diagonal fun i => inventory i q

lemma mask_nil (t : Axis → ℂ) : mask 0 t=1 := by
  ext i j; rw [vac_only i,vac_only j]; simp [mask,inventory,vac]
lemma mask_value (t : Axis → ℂ) (a b : TypeFace 1) : mask 1 t a b=if a=b then t (axisEquiv.symm a) else 0 := by
  by_cases h : a=b <;> simp [mask,h]
  obtain ⟨x,rfl⟩ := axisEquiv.surjective b
  rw [axisEquiv.symm_apply_apply]; simp [inventory,axisEquiv,coord]
lemma mask_trans (r : ℕ) (q : Axis → ℂ) : (mask r q).transpose=mask r q := Matrix.diagonal_transpose _
lemma mask_adj (r : ℕ) (q : Axis → ℂ) : (mask r q)ᴴ=mask r (star q) := by
  unfold mask; ext i j; simp [inventory,Matrix.conjTranspose_apply,Matrix.diagonal_apply,eq_comm]; split_ifs with h <;> simp [*]

lemma inventory_one {r : ℕ} (u : TypeFace r) : inventory u (fun _ => 1)=1 := by simp [inventory]
lemma inventory_mul {r : ℕ} (u : TypeFace r) (x y : Axis → ℂ) : inventory u (fun i => x i*y i)= inventory u x* inventory u y := by unfold inventory; exact Finset.prod_mul_distrib

lemma inventory_scale {r : ℕ} (u : TypeFace r) (x : Axis → ℂ) (c : ℂ) : inventory u (fun i => c*x i)=c^r*inventory u x := by rw [inventory_mul]; simp [inventory,u.property]
lemma inventory_pos {r : ℕ} (u : TypeFace r) (x : Axis → ℂ) (h : ∀ i, Silver (x i)) : Silver (inventory u x) := by
  have he (s : Finset Axis) : Silver (∏ i∈s, x i) := by
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty]; exact Silver.one
    | insert a s ha ih => rw [Finset.prod_insert ha]; exact (h a).mul ih
  exact he _


lemma mask_one (r : ℕ) : mask r (fun _ => 1)=1 := by ext i j; simp [mask,inventory_one,Matrix.one_apply]
lemma mask_mul (r : ℕ) (x y : Axis → ℂ) : mask r x*mask r y=mask r (fun i => x i*y i) := by
  unfold mask; rw [Matrix.diagonal_mul_diagonal]; simp only [inventory_mul]
lemma mask_scale (r : ℕ) (x : Axis → ℂ) (c : ℂ) : mask r (fun i => c*x i)=c^r • mask r x := by
  ext i j; unfold mask; simp only [Matrix.smul_apply, inventory_scale, Matrix.diagonal_apply,smul_eq_mul,mul_ite,mul_zero]
lemma mask_undo (r : ℕ) (t : Axis → ℂ) (h : ∀ i, t i ≠ 0) :
    mask r t * mask r (fun i => (t i)⁻¹)=1 ∧ mask r (fun i => (t i)⁻¹)*mask r t=1 := by simp only [mask_mul,inv_mul_cancel₀ (h _),mul_inv_cancel₀ (h _),mask_one, and_self]

lemma mask_left (r : ℕ) (t : Axis → ℂ) (a : Axis) : mask (r+1) t*left ℂ r a = t a • (left ℂ r a*mask r t) := by
  ext i j; simp only [mask,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.smul_apply,smul_eq_mul,left,Matrix.of_apply]
  by_cases h : a∈i.val <;> simp only [h,↓reduceDIte,mul_zero,zero_mul]
  split
  · next he =>
      subst j
      have he : inventory i t=t a*inventory (Exterior.remove a i h) t := (Finset.mul_prod_erase _ t h).symm
      rw [he]; ring
  simp
lemma mask_insert (r : ℕ) (t q : Axis → ℂ) : mask (r+1) t*wedge r q=wedge r (fun i => t i*q i)*mask r t := by
  unfold wedge; rw [Matrix.sum_mul,Matrix.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul,Matrix.smul_mul,mask_left,smul_smul,mul_comm]

lemma wedge_smul (r : ℕ) (t : Axis → ℂ) (b : ℂ) : wedge r (fun i => b*t i)=b • wedge r t := by unfold wedge; simp [Finset.smul_sum, smul_smul]

lemma wedge_adj (r : ℕ) (t : Axis → ℂ) : (wedge r t)ᴴ=(wedge r (star t)).transpose := by
  unfold wedge; ext i j; simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul,star_sum,Pi.star_apply]
  refine Finset.sum_congr rfl fun a _ => ?_; unfold left; rw [star_mul, mul_comm, of_apply]; split_ifs <;> simp [parity]

lemma cartan_entry (n : ℕ) (x : Axis → ℂ) (i : Axis) : wedge n x * (left ℂ n i).transpose +
    (left ℂ (n+1) i).transpose*wedge (n+1) x=x i • 1 := by
  apply Matrix.toLin'.injective; apply LinearMap.ext; intro v
  change (_+_) *ᵥ v=_ *ᵥ v
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,Work.F06.cartan,Matrix.smul_mulVec,Matrix.one_mulVec]
lemma crossed (n : ℕ) (x y : Axis → ℂ) :
    (wedge (n+1) x).transpose*wedge (n+1) y =
      (∑ i, x i*y i) • 1 - wedge n y * (wedge n x).transpose := by
  rw [eq_sub_iff_add_eq]
  have hh (n : ℕ) : (wedge n x).transpose=∑ i,x i • (left ℂ n i).transpose := by unfold wedge; rw [Matrix.transpose_sum]; simp only [Matrix.transpose_smul]
  rw [hh,hh, Matrix.sum_mul,Matrix.mul_sum,← Finset.sum_add_distrib, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_; rw [Matrix.smul_mul, Matrix.mul_smul,← smul_add,add_comm (_ * wedge (n+1) y),cartan_entry,smul_smul]

/-- Potential-on-potential Schur numerator. -/
lemma blade_price (x y t : Axis → ℂ) :
    (wedge 1 x).transpose*mask 2 t*wedge 1 y=(∑ i, x i*(t i*y i)) • mask 1 t -
      mask 1 t * wedge 0 y * (wedge 0 x).transpose * mask 1 t := by
  rw [Matrix.mul_assoc,mask_insert,← Matrix.mul_assoc,crossed, sub_mul, smul_mul_assoc, one_mul,
    mask_insert,mask_nil,Matrix.mul_one]
end YM.Next.Free
