import YM.Planned.PRIMARY_INTEGRAL_295.Positions
import YM.Work.B06

/-! # Translating the homogeneous cover polynomials -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Place
open Function Labels WardBin
open scoped BigOperators ContDiff Topology Matrix.Norms.Frobenius

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {n m k : ℕ}

abbrev Slices (n : ℕ) := Fin n → Bool

def away (s : Slices n) := ∑ i, if s i then (1:ℕ) else 0

def home (s : Slices n) := ∑ i, if s i then (0:ℕ) else 1

lemma covers (s : Slices n) : away s + home s=n := by
  rw [away,home,← Finset.sum_add_distrib]
  have he (i : Fin n) : (if s i then (1:ℕ) else 0)+(if s i then (0:ℕ) else 1)=1 := by
    split <;> rfl
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin]; simp

def forSlice (A : Tensor.T F E n) (s : Slices n) (x v : F) : E := A fun i => if s i then v else x

lemma forSlice_home (A : Tensor.T E4 E n) (s : Slices n) (v : E4) :
    (fun x => forSlice A s x v) ∈ exactDegree E (home s) := by
  apply multi_pure A (fun i x => if s i then v else x) (fun i => if s i then 0 else 1)
  intro i
  by_cases h : s i=true
  · simp only [h, if_true]; exact exact_constant v
  simp only [h]; exact exact_id

lemma slice_scale (A : Tensor.T F E n) (s : Slices n) (x v : F) (r q : ℝ) :
    forSlice A s (r • x) (q • v) = (r^(home s)*q^(away s)) • forSlice A s x v := by
  let f i := if s i then 0 else (1:ℕ)
  let g i := if s i then 1 else (0:ℕ)
  unfold forSlice; rw [show (fun i => if s i then q • v else r • x)=fun i => (r^(f i)*q^(g i)) • if s i then v else x from
    funext fun i => by cases h:s i <;> simp [f,g,h],A.map_smul_univ]
  simp_rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; rfl

lemma slice_diagonal (A : Tensor.T F E n) (x v : F) (t : ℝ) :
    Tensor.diagonal A (x+t•v)=∑ s:Slices n, t^(away s) • forSlice A s x v := by
  have h (x v : F) : Tensor.diagonal A (x+v)=∑ s:Slices n, forSlice A s x v := by
    let f (_i : Fin n) (b : Bool) := if b then v else x
    rw [Tensor.diagonal,show (fun _ : Fin n => x+v)=(fun i => ∑ b, f i b) by simp [f,add_comm], A.map_sum f]; rfl
  rw [h]; refine Finset.sum_congr rfl fun s _ => ?_
  simpa using slice_scale A s x v 1 t

lemma slice_center (A : Tensor.T F E n) (x v : F) :
    Tensor.diagonal A x=∑ s:Slices n, if away s=0 then forSlice A s x v else 0 := by
  calc
    _ = ∑ s:Slices n, (0:ℝ)^(away s) • forSlice A s x v := by simpa using slice_diagonal A x v 0
    _ = _ := Finset.sum_congr rfl fun b _ => by split <;> simp_all

lemma slice_velocity (A : Tensor.T F E n) (x v : F) : fderiv ℝ (Tensor.diagonal A) x v =
    ∑ s : Slices n, if away s = 1 then forSlice A s x v else 0 := by
  have he : leading 1 (fun t : ℝ => Tensor.diagonal A (x+t•v))=fderiv ℝ (Tensor.diagonal A) x v := by
    have hp : HasDerivAt (fun t : ℝ => x+t•v) v 0 := by
      simpa using! ((hasDerivAt_id' (0:ℝ)).smul_const v).const_add x
    have hv : HasFDerivAt (Tensor.diagonal A) (fderiv ℝ (Tensor.diagonal A) x) x :=
      ((Tensor.diag_smooth A 1).contDiffAt.differentiableAt one_ne_zero).hasFDerivAt
    simpa only [leading, iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, inv_one,one_smul, comp_def] using
      (hv.comp_hasDerivAt_of_eq 0 hp (show x=x+(0:ℝ)•v by simp)).deriv
  rw [← he,funext (slice_diagonal A x v),lead_sum (n:=1) _ _ (by intros; exact (monoSmooth ..).contDiffAt)]
  simp only [lead_monomial, eq_comm]

lemma pure_step {f : E4 → E} (h : f ∈ exactDegree E n) (v : E4) :
    (fun x => f (x+v)-f x) ∈ rangeLt E n := by
  obtain ⟨A,rfl⟩ := can_write.1 h
  let q s (x : E4) := if away s=0 then 0 else forSlice A s x v
  have he (x : E4) : Tensor.diagonal A (x+v)-Tensor.diagonal A x=∑ s:Slices n,q s x := by
    rw [show Tensor.diagonal A (x+v)=∑ s:Slices n, forSlice A s x v by simpa using slice_diagonal A x v 1,
      slice_center A x v,← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun b _ => by unfold q; split <;> simp
  rw [show (fun x => Tensor.diagonal A (x+v)-Tensor.diagonal A x)=∑ s:Slices n, q s from
    funext fun x => by rw [Finset.sum_apply]; exact he x]
  apply Submodule.sum_mem; intro b _
  by_cases h : away b=0
  · unfold q; simp [h,show (fun _ : E4 => (0:E))=0 from rfl]
  unfold q; simp only [if_neg h]; exact exact_le_band (by have := covers b;omega) (forSlice_home A b v)

lemma pure_tangent_step {f : E4 → E} (h : f ∈ exactDegree E (n+1)) (v : E4) :
    (fun x => f (x+v)-f x-fderiv ℝ f x v) ∈ rangeLt E n := by
  obtain ⟨A,rfl⟩ := can_write.1 h
  let q s (x : E4) := if away s ≤ 1 then 0 else forSlice A s x v
  have he (x : E4) : Tensor.diagonal A (x+v) - Tensor.diagonal A x - fderiv ℝ (Tensor.diagonal A) x v =∑ s,q s x := by
    rw [show Tensor.diagonal A (x+v)=∑ s, forSlice A s x v by simpa using slice_diagonal A x v 1,
      slice_center A x v, slice_velocity, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro b _; unfold q
    by_cases he : away b ≤ 1
    · rcases (show away b=0 ∨ away b=1 by omega) with h|h <;> simp [h]
    rw [if_neg he,if_neg (by omega : ¬ away b=0),if_neg (by omega : ¬ away b=1)]; simp
  rw [show (fun x : E4 => Tensor.diagonal A (x+v) - Tensor.diagonal A x - fderiv ℝ (Tensor.diagonal A) x v) = ∑ s, q s from funext fun x => by rw [Finset.sum_apply]; exact he x]
  apply Submodule.sum_mem; intro b _
  by_cases he : away b ≤ 1
  · unfold q; simp [he,show (fun _ : E4 => (0:E))=0 from rfl]
  unfold q; simp only [if_neg he]; exact exact_le_band (by have := covers b;omega) (forSlice_home A b v)

lemma pure_direction {f : E4 → E} (h : f ∈ exactDegree E (n+1)) (v : E4) :
    (fun x : E4 => fderiv ℝ f x v) ∈ exactDegree E n := by
  obtain ⟨A,hA,rfl⟩ := pure_sym h
  have he : (fun x : E4 => fderiv ℝ (Tensor.diagonal A) x v) = ((n+1 : ℕ) : ℝ) • Tensor.diagonal (A.curryLeft v) := by
    funext x; rw [Tensor.differential_diagonal A hA,Pi.smul_apply,Nat.cast_smul_eq_nsmul]; rfl
  rw [he]; exact Submodule.smul_mem _ _ (simple _)

lemma band_step {f : E4 → E} (h : f ∈ rangeLt E (n+1)) (v : E4) : (fun x => f (x+v)-f x)∈ rangeLt E n := by
  classical
  obtain ⟨P,hP,rfl⟩ := range_decompose h
  rw [show (fun x : E4 => (∑ i,P i) (x+v)-(∑ i,P i) x)=(∑ i, fun x => P i (x+v)- P i x) by
    funext; simp only [Finset.sum_apply,Finset.sum_sub_distrib]]
  apply Submodule.sum_mem; intro b _
  exact grows E (Nat.le_of_lt_succ b.isLt) (pure_step (hP b) v)

lemma band_shift {f : E4 → E} (h : f ∈ rangeLt E n) (v : E4) : (fun x => f (x+v)) ∈ rangeLt E n := by
  rw [show (fun x => f (x+v)) = (fun x => f (x+v)-f x)+f by ext; simp]
  exact Submodule.add_mem _ (band_step (grows E (Nat.le_succ n) h) v) h

end YM.Planned.PrimaryIntegral295.Place
