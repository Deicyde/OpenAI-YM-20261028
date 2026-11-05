import YM.CellFourier.Shuttle

/-!
# Shifted fiber algebra, raw cell phases, arbitrary reindexing of components

Trace counting is over the full finite-dimensional real position basis after
complexification (no extra division by two). Harmonic occurs exactly once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Filter Function Bloch Lattice Laurent
open scoped Topology BigOperators

abbrev Grid (n : Side) (E a : Type) := E ≃ Co n a

variable {n : Side} {E F H a b c : Type} [DecidableEq a] [DecidableEq b] [DecidableEq c]
  {e : Grid n E a} {f : Grid n F b} {h : Grid n H c}

def plane (e : Grid n E a) (p : Site n) : Matrix E a ℂ := of fun x i => if (e x).2 = i then cell p (e x).1 else 0

def pick (e : Grid n E a) (p : Site n) : Matrix a E ℂ := ((n.val:ℂ)^4)⁻¹ • (plane e (-p)).transpose

variable [Fintype a] [Fintype b] [Fintype c] [Fintype E] [Fintype F] [Fintype H]

omit [Fintype E] in lemma plane_apply (e : Grid n E a) (p : Site n) (v : a → ℂ) (x : E) :
    (plane e p *ᵥ v) x = cell p (e x).1 * v (e x).2 := by simp [plane,mulVec,dotProduct,ite_mul]

lemma pick_plane (e : Grid n E a) (p q : Site n) : pick e p * plane e q = if p=q then 1 else 0 := by
  ext i j
  rw [mul_apply, ← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  simp only [pick,plane, Matrix.smul_apply, of_apply, transpose_apply,smul_eq_mul,Equiv.apply_symm_apply]
  by_cases he : i=j
  · subst j
    simp only [mul_ite,ite_mul,mul_zero,zero_mul, Finset.sum_ite_eq',Finset.mem_univ,if_true,mul_assoc,← Finset.mul_sum]
    have hs (x : Site n) : cell (-p) x * cell q x = cell q x * (cell p x)⁻¹ := by
      rw [cell_duality (-p),cell_inverse,cell_duality x p,mul_comm]
    simp_rw [hs, orthogonal]; by_cases he : q=p <;> simp [*, Ne.symm, side_ne n]
  rw [show (if p=q then 1 else (0:Matrix a a ℂ)) i j=0 by split <;> simp [he]]
  exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun r _ => by by_cases h : r=i <;> simp [*]

omit [Fintype E] in
lemma plane_pick [DecidableEq E] (e : Grid n E a) : ∑ p, plane e p * pick e p = 1 := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply,pick, Matrix.smul_apply, plane,transpose_apply,of_apply,smul_eq_mul,mul_ite, mul_zero,ite_mul,zero_mul, Matrix.one_apply]
  by_cases ht : (e i).2 = (e j).2
  · calc
      _ = ∑ p : Site n, ((n.val:ℂ)^4)⁻¹ * (cell (e i).1 p * (cell (e j).1 p)⁻¹) := Finset.sum_congr rfl fun p _ => by
        rw [Fintype.sum_eq_single (e j).2 (fun x hx => if_neg (Ne.symm hx))]
        rw [if_pos rfl, if_pos ht,cell_duality,cell_duality (-p),cell_inverse]; ring
      _ = _ := by rw [← Finset.mul_sum,orthogonal]; split
                  next he => rw [if_pos (e.injective (Prod.ext he ht)),inv_mul_cancel₀ (pow_ne_zero _ (side_ne _))]
                  next he => rw [if_neg (fun hij => he (congr_arg Prod.fst (congr_arg e hij))),mul_zero]
  · rw [if_neg (fun hij => ht (congr_arg Prod.snd (congr_arg e hij)))]
    exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun x _ => by by_cases h : x=(e i).2 <;> simp [*,Ne.symm]

def Routed (e : Grid n E a) (f : Grid n F b) (q p : Site n) (M : Matrix E F ℂ) (W : Matrix a b ℂ) : Prop :=
    M * plane f p = plane e q * W
namespace Routed
variable {p q r : Site n} {M : Matrix E F ℂ} {W : Matrix a b ℂ}

omit [Fintype E] in
lemma of_vector (h : ∀ x : b → ℂ, M *ᵥ plane f p *ᵥ x = plane e q *ᵥ W *ᵥ x) : Routed e f q p M W := by
  apply Matrix.ext_iff_mulVec.mpr; intro x; rw [← mulVec_mulVec,← mulVec_mulVec,h]

omit [Fintype E] in
lemma vector (h : Routed e f q p M W) (x : b → ℂ) : M *ᵥ plane f p *ᵥ x = plane e q *ᵥ W *ᵥ x := by rw [mulVec_mulVec, mulVec_mulVec,h]

omit [Fintype E] [Fintype b] in
lemma zero : Routed e f q p 0 0 := by unfold Routed; rw [Matrix.zero_mul,Matrix.mul_zero]
lemma one [DecidableEq E] : Routed e e p p 1 1 := by unfold Routed; rw [Matrix.one_mul,Matrix.mul_one]

omit [Fintype E] [Fintype b] in
lemma add {B : Matrix E F ℂ} {T} (h : Routed e f q p M W) (h' : Routed e f q p B T) : Routed e f q p (M+B) (W+T) := by
  unfold Routed; rw [Matrix.add_mul,Matrix.mul_add, h,h']

omit [Fintype E] [Fintype b] in
lemma smul (s : ℂ) (h : Routed e f q p M W) : Routed e f q p (s • M) (s • W) := by
  unfold Routed; rw [Matrix.smul_mul,Matrix.mul_smul,h]

omit [Fintype E] [Fintype b] in
lemma neg (h : Routed e f q p M W) : Routed e f q p (-M) (-W) := by simpa using h.smul (-1)

omit [Fintype E] [Fintype c] in
lemma mul {B T} (hM : Routed e f q p M W) (h' : Routed f h p r B T) : Routed e h q r (M*B) (W*T) := by
  unfold Routed; rw [Matrix.mul_assoc, h',← Matrix.mul_assoc,hM,Matrix.mul_assoc]

lemma inv [DecidableEq E] {M : Matrix E E ℂ} {W : Matrix a a ℂ} (h : Routed e e p p M W) (hm : IsUnit M) (hw : IsUnit W) :
    Routed e e p p M⁻¹ W⁻¹ := by
  have ht := congr_arg (fun X : Matrix E a ℂ => M⁻¹ * X * W⁻¹) h
  change M⁻¹ * (M * _) * W⁻¹ = _ at ht
  rw [← Matrix.mul_assoc _ M, M.nonsing_inv_mul (M.isUnit_iff_isUnit_det.mp hm),Matrix.one_mul,
    Matrix.mul_assoc,Matrix.mul_assoc _ W, W.mul_nonsing_inv (W.isUnit_iff_isUnit_det.mp hw),Matrix.mul_one] at ht
  exact ht.symm

omit [Fintype b] in
lemma projected (h : Routed e f q p M W) (r : Site n) : pick e r * M * plane f p = if r=q then W else 0 := by
  rw [Matrix.mul_assoc,h, ← Matrix.mul_assoc, pick_plane]; split <;> simp

omit [Fintype b] in
lemma paired (h : Routed e f q p M W) (r : Site n) : (plane e r).transpose * M * plane f p = if -r=q then (n.val : ℂ)^4 • W else 0 := by
  have he : (plane e r).transpose = (n.val:ℂ)^4 • pick e (-r) := by rw [pick,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ (side_ne _)),one_smul,neg_neg]
  rw [he, Matrix.smul_mul,Matrix.smul_mul,h.projected]; split <;> simp

lemma sum_projected [DecidableEq F] {W : Site n → Matrix a b ℂ} (h : ∀ p, Routed e f (p+q) p M (W p)) (p : Site n) : pick e (p+q) * M = W p * pick f p := by
  rw [← Matrix.mul_one (_ * M),← plane_pick f, Matrix.mul_sum]
  calc
    _ = ∑ i, if i=p then W i * pick f i else 0 := Finset.sum_congr rfl fun i _ => by
      rw [← Matrix.mul_assoc, (h i).projected]; split_ifs <;> simp_all
    _ = _ := by simp

lemma transpose [DecidableEq F] {W : Site n → Matrix a b ℂ} (h : ∀ p, Routed e f (p+q) p M (W p)) (p : Site n) :
    Routed f e (p+q) p M.transpose (W (-(p+q))).transpose := by
  have he := sum_projected h (-(p+q))
  have hr := pow_ne_zero 4 (side_ne n)
  rw [show -(p+q)+q=-p by abel,pick,pick,neg_neg,neg_neg, Matrix.smul_mul, Matrix.mul_smul,
    smul_right_inj (inv_ne_zero hr)] at he
  simpa only [transpose_mul,transpose_transpose] using! congr_arg Matrix.transpose he

lemma trace [DecidableEq E] {M : Matrix E E ℂ} {W : Site n → Matrix a a ℂ} (h : ∀ p, Routed e e (p+q) p M (W p)) :
    M.trace = if q=0 then ∑ p : Site n,(W p).trace else 0 := by
  rw [← Matrix.mul_one M,← plane_pick e,Matrix.mul_sum, Matrix.trace_sum]
  split <;> rename_i he
  · apply Finset.sum_congr rfl; intro i _
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle,(h i).projected,he,add_zero, if_pos rfl]
  · apply Finset.sum_eq_zero; intro i _
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle,(h i).projected, if_neg (by simpa [eq_comm] using he),Matrix.trace_zero]

lemma isUnit [DecidableEq E] {M : Matrix E E ℂ} {W : Site n → Matrix a a ℂ} (h : ∀ p, Routed e e p p M (W p)) (hw : ∀ p, IsUnit (W p)) :
    IsUnit M := by
  have he : M * (∑ p, plane e p * (W p)⁻¹ * pick e p) = 1 := by
    rw [Matrix.mul_sum]; convert! plane_pick e using 1
    refine Finset.sum_congr rfl fun p _ => ?_; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,h p, Matrix.mul_assoc (plane e p),
      Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (hw p)), Matrix.mul_one]
  exact (IsUnit.mul_iff.mp (he.symm ▸ isUnit_one)).1
end Routed
end YM.Push.Loops
