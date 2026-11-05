import YM.WilsonBulk.Heat.Meaning

set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical ENNReal BigOperators
open Function Finset Equiv
open MvPolynomial (X C pderiv)
variable {n k m r : ℕ} {α β : Type} [Fintype α] (G : Page α 2)

-- extensivity polynomial differential calculation. ∂_y after ∂_x.
def laplace (G : Page α 2) : Formula α →ₗ[ℝ] Formula α :=
    ∑ x,∑ y,(G (two x y)/2) • ((pderiv y).toLinearMap.comp (pderiv x).toLinearMap)
def airing (G : Page α 2) (f g : Formula α) : Formula α :=
    ∑ x,∑ y, (G (two x y)/2) • (pderiv x f*pderiv y g)
lemma laplace_eval (p : Formula α) : laplace G p=∑ x,∑ y,(G (two x y)/2) • (pderiv y (pderiv x p)) := by
  simp only [laplace,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply]; rfl
lemma airing_sum_l {ι : Type} (s : Finset ι) (f : ι→ Formula α) (g : Formula α) :
    airing G (∑ i∈s,f i) g= ∑ i∈s,airing G (f i) g := by
  unfold airing; simp only [map_sum,sum_mul, Finset.smul_sum]
  rw [sum_comm (s:=s)]; refine sum_congr rfl fun i _=> sum_comm
lemma airing_sum_r {ι : Type} (s : Finset ι) (f : ι→ Formula α) (g : Formula α) :
    airing G g (∑ i∈s,f i)= ∑ i∈s,airing G g (f i) := by
  unfold airing; simp only [map_sum,mul_sum, Finset.smul_sum]; rw [sum_comm (s:=s)]; refine sum_congr rfl fun i _=> sum_comm
@[simp] lemma airing_zero_left (u : Formula α) : airing G 0 u=0 := by simp [airing]
@[simp] lemma airing_zero_right (u : Formula α) : airing G u 0=0 := by simp [airing]
@[simp] lemma laplace_scalar (a : Page α 0) : laplace G (script a)=0 := by simp [laplace_eval,script_scalar]
@[simp] lemma air_scalar_left (u : Page α 0) (v : Formula α) : airing G (script u) v=0 := by simp [airing,script_scalar]
@[simp] lemma air_scalar_right (u : Page α 0) (v : Formula α) : airing G v (script u)=0 := by simp [airing,script_scalar]
lemma laplace_linear (v : Page α 1) (h : Regular v) : laplace G (script v)=0 := by
  rw [laplace_eval]; simp_rw [script_deriv v h,script_scalar, Nat.cast_add,Nat.cast_zero,Nat.cast_one,zero_add,one_smul]; simp

-- polynomial versions of the Sheet props: stitch exact antisym free. Cost pays Γ as positive.
lemma dabble_margin (u : Page α (n+2)) : dabble G u = ∑ y,∑ x, G (two x y) • margin (margin u x) y := by
  ext1 v
  rw [dabble_read]; simp only [tsum_fintype,Finset.sum_apply,Pi.smul_apply,margin,smul_eq_mul]
  apply sum_congr rfl fun y _=> sum_congr rfl fun x _=> mul_comm ..
lemma fold_lap (u : Page α (n+2)) (h : Regular u) : laplace G (script u)=script (lap G u) := by
  unfold lap; rw [script_polish, script_scale, dabble_margin, laplace_eval, sum_comm]; simp_rw [script_deriv _ h, Derivation.map_smul, script_deriv _ (h.margin _), script_sum,script_scale,Finset.smul_sum]
  apply sum_congr rfl fun y _=>sum_congr rfl fun x _=>?_; simp_rw [smul_smul]; congr 1; unfold dab; ring

def weave (u : Page α k) (v : Page α n) : Page α (k+n) := fun w=> u (snip k n w)* v (keep k n w)
lemma weave_script (u : Page α k) (v : Page α n) : script (weave u v) = script u * script v := by
  unfold script; rw [typeset_fin_plus]; simp only [weave,snip_append,keep_append,field_append,map_mul,sum_mul,mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun a _=> ?_); apply sum_congr rfl; intro b _; ring
lemma bracket_span (u : Page α (k+1)) (v : Page α (n+1)) : bracket G u v =∑ y,∑ x,G (two x y) • weave (margin u x) (margin v y) := by
  ext1 p; refine legs_plus (k:=k) (fun p=> bracket G u v p=(∑ y,∑ x,G (two x y) • weave (margin u x) (margin v y)) p) ?_ p
  intro a b; rw [bracket_read]; simp only [tsum_fintype,Finset.sum_apply,Pi.smul_apply,weave,snip_append,keep_append,margin,smul_eq_mul,sum_mul]; exact sum_congr rfl fun a _=> sum_congr rfl fun b _=> by ring
lemma fold_air (u : Page α (k+1)) (v : Page α (n+1)) (hu : Regular u) (hv : Regular v) : airing G (script u) (script v)=script (bridge G u v) := by
  unfold bridge; rw [script_polish,script_scale,bracket_span]; unfold airing; rw [sum_comm]; simp only [script_sum,script_deriv _ hu,script_deriv _ hv,script_scale,Finset.smul_sum,weave_script]
  apply sum_congr rfl fun y _=> sum_congr rfl fun x _=> ?_; rw [smul_mul_assoc, mul_smul_comm]; simp_rw [smul_smul]; congr 1; unfold brush; push_cast; ring
end YM.WilsonBulk.Sheet
