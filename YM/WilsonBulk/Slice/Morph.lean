import YM.WilsonBulk.Series.Picture
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Wick expansion under regular nonlinear change of tree coordinates I

Track formal Jacobian and material derivative across private positions.
General matrix algebra over Tape, including spectator variables and arbitrary
numbers of orders. No Cauchy estimate nor convergence of analytic density
assumed here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open scoped Classical BigOperators
open PowerSeries Matrix Finset Function
variable {A M : Type} [CommRing A] [CommRing M] [Algebra ℝ A]
variable {α β ι : Type}
lemma D_prod (D : Derivation ℝ A A) [DecidableEq β] (s : Finset β) (f : β→ A) :
    D (∏ i∈s,f i) = ∑ i∈s,∏ j∈s, update f i (D (f i)) j := by
  induction s using Finset.induction with
  | empty=> simp
  | insert i s hi ih=>
    rw [prod_insert hi,sum_insert hi,prod_insert hi,Function.update_self, D_leib,ih, prod_update_of_notMem hi,mul_sum]; simp_rw [prod_insert hi]; congr 1; exact sum_congr rfl fun a ha=> by rw [update_of_ne (ne_of_mem_of_not_mem ha hi).symm]
lemma D_matrix (D : Derivation ℝ A A) [DecidableEq α] [Fintype α] (H : Matrix α α A) :
    D H.det = ∑ j:α, (H.updateCol j (fun i=> D (H i j))).det := by
  simp only [det_apply, Units.smul_def,map_sum, map_zsmul,D_prod,Finset.smul_sum]; rw [sum_comm]; refine sum_congr rfl fun i _=>sum_congr rfl fun a _=> ?_; apply congr_arg; refine prod_congr rfl fun j _=> ?_; by_cases hj : j=i
  · subst j; simp
  rw [update_of_ne hj,Matrix.updateCol_ne hj]
lemma D_diag (D : Derivation ℝ A A) [DecidableEq α] [Fintype α] (H : Matrix α α A) (C : α→α→ A) (h : ∀ i j,D (H i j)=∑ k,H i k*C j k) : D H.det=H.det*∑ i,C i i := by
  rw [D_matrix,mul_sum]; refine sum_congr rfl fun j _=> ?_; rw [show (fun i=> D (H i j))=(fun i=>∑ k:α,C j k • H i k) from funext fun i=> (h i j).trans (sum_congr rfl fun _ _=>mul_comm ..), det_updateCol_sum]; exact mul_comm ..

namespace Sheet
variable [Fintype α]
-- use private LEFT
abbrev Chamber (α ι : Type) := α ⊕ ι -- ink index field
abbrev StageD (α ι : Type) := Tape (Chamber α ι)

-- change along velocity v in source chart
abbrev inflow (i : α) := player (Sum.inl i : Chamber α ι)
abbrev gaugeHess (T : α→StageD α ι) : Matrix α α (StageD α ι) := Matrix.of (fun i j=>inflow j (T i))
def airs (v : α→StageD α ι) : Derivation ℝ (StageD α ι) (StageD α ι) := ∑ i, v i • inflow i
lemma airs_apply (f : StageD α ι) (v : α→StageD α ι) : airs v f= ∑ i,v i * inflow i f := by
  unfold airs; induction (univ (α:=α)) using Finset.induction with
  | empty=> simp
  | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; simp [ih]
def flow (v : α→StageD α ι) : Derivation ℝ (StageD α ι) (StageD α ι) := clockD _ - airs v
lemma flow_apply (f : StageD α ι) (v : α→StageD α ι) : flow v f=clockD _ f-∑ i,v i * inflow i f := by rw [← airs_apply]; rfl
lemma flow_det [DecidableEq α] (v T : α→StageD α ι) (h : ∀ i, flow v (T i)=0) : flow v (gaugeHess T).det=(gaugeHess T).det*∑ i,inflow i (v i) := by
  have he i := h i; simp_rw [flow_apply,sub_eq_zero] at he
  set G:= gaugeHess T
  apply D_diag (flow v) G (fun j k=> inflow j (v k))
  intro i j; rw [flow_apply]; dsimp only [G,gaugeHess,Matrix.of_apply]
  rw [show (clockD _) (inflow j (T i)) = inflow j (clockD _ (T i)) from (clock_adjunct _ _).symm, he,map_sum, sub_eq_iff_eq_add, ← sum_add_distrib]; refine sum_congr rfl fun k _=>?_ ; rw [D_leib,inflow,inflow,player_live,mul_comm (player _ (v k))]
lemma flow_tide {f : StageD α ι} (hf : constantCoeff f=0) (v : α→StageD α ι) : flow v (tide f) = tide f * flow v f := by
  rw [flow_apply,flow_apply,differentiate_time hf, mul_sub,mul_sum]; apply congr_arg (tide f * clockD _ f - ·); refine sum_congr rfl fun i _=> ?_; simp only [inflow,player,differentiating _ hf]; rw [mul_left_comm]

-- submit internally only
abbrev privateName (i : α) : StageD α ι:= named (Sum.inl i)
def switch (T : α→StageD α ι) : StageD α ι →ₐ[ℝ]StageD α ι := submit (Sum.elim T (fun i : ι=> named (Sum.inr i)))
section
omit [Fintype α]
lemma switch_X (T : α→StageD α ι) : switch T X=X := submit_X _
lemma switch_to (T : α→StageD α ι) (i : α) : switch T (privateName i)=T i := submit_named ..
lemma switch_side (T : α→StageD α ι) (i : ι) : switch T (named (Sum.inr i))=named (Sum.inr i) := submit_named ..
end
lemma flow_C (v : α→StageD α ι) (x : Formula (Chamber α ι)) : flow v (C x)= -∑ i,v i* C (MvPolynomial.pderiv (Sum.inl i) x) := by simp only [flow_apply,clock_C,inflow,player,parallelD_C,zero_sub]
lemma flow_switch [Fintype ι] (v T : α→StageD α ι) (h : ∀ i,flow v (T i)=0) (f : StageD α ι) : flow v (switch T f)=switch T (clockD _ f) := by
  rw [switch,chain]; simp_rw [Fintype.sum_sum_type]; dsimp only [Sum.elim]; simp_rw [h,mul_zero,sum_const_zero,zero_add]
  have hb (i : ι) : flow v (named (Sum.inr i))=0 := by simp [named,flow_C]
  rw [show flow v X=1 from by simp [flow_apply,clock_X, inflow,player,parallelD_X]]; simp_rw [hb,mul_zero,mul_one,sum_const_zero,add_zero]
-- construct velocity when compensated clock-preserving transform has invertible Jacobian (over complete series ring at any spectator)
def breeze [DecidableEq α] (T : α→StageD α ι) : α→StageD α ι := (gaugeHess T)⁻¹ *ᵥ (fun i=> clockD _ (T i))
lemma breeze_fits [DecidableEq α] (T : α→StageD α ι) (h : IsUnit (gaugeHess T).det) : ∀ i, flow (breeze T) (T i)=0 := by
  have he : (gaugeHess T)*ᵥ (breeze T)=fun i=> clockD _ (T i) := by rw [breeze,mulVec_mulVec,Matrix.mul_nonsing_inv _ h,one_mulVec]
  intro i; rw [flow_apply,sub_eq_zero]; refine Eq.trans (congr_fun he.symm i) (sum_congr rfl fun j _=> mul_comm ..)
end Sheet
end YM.WilsonBulk
