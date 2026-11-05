import YM.Marker.Console

/-!
# Radius budgets inside nilpotent marker ring

Think l¹, weight `w^T`. Even c^|T| may be fatal, account for exact costs.
These operations do NOT divide each K by its vacuum value. `jump` used to
write high-order monomials split. Fixed-arbitrary forbidden sets downward
closed. Contributions distinguished separately; this ring is for evaluation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Marker.Poly
open Function Finset
open scoped Topology BigOperators
variable {V : Type*} [DecidableEq V] {R : Census V}

@[simp] lemma one_part (x : R.Mode) : (1 : Poly R).part x=if x=R.quiet then 1 else 0 := part_send ..
lemma part_mul (a b : Poly R) (i) : (a*b).part i=∑ x,∑ y,if merges x y i then a.part x*b.part y else 0 := product a b i

lemma merge_vac (x y : R.Mode) : merges x y R.quiet ↔ x=R.quiet ∧ y=R.quiet := by
  change Disjoint x.val y.val ∧ x.val ∪ y.val=∅ ↔ _
  simp only [Finset.union_eq_empty]
  constructor
  · rintro ⟨-,a,b⟩; exact ⟨Subtype.ext a, Subtype.ext b⟩
  rintro ⟨rfl,rfl⟩; simp [Census.quiet]

@[simp] lemma quiet_mul (a b : Poly R) : (a*b).part R.quiet=a.part R.quiet*b.part R.quiet := by simp [part_mul,merge_vac,ite_and]

/-- multiplication by scalar embedded. -/
def bead (R : Census V) : ℂ →+* Poly R where
  toFun := send R.quiet
  map_one' := rfl
  map_add' a b := by ext i; rw [part_plus]; simp only [part_send]; split <;> simp
  map_zero' := send_zero _
  map_mul' a b := by
    ext i
    change (send _ _).part _ = (prod _ _).part _
    rw [cart,part_send]; simp [eq_comm]

lemma product_bead (a : Poly R) (c : ℂ) : bead R c * a=c • a := by
  ext i
  rw [part_mul,sum_eq_single R.quiet]
  · simp [bead]
  · intro j _ hj; simp [bead, hj]
  simp

instance : Algebra ℂ (Poly R) where
  algebraMap := bead _
  commutes' _ _ := mul_comm ..
  smul_def' a b := (product_bead b a).symm

-- No implicit `NormedRing`. default sup only for finite algebraic continuity
-- & summability (require Weighted along actual `w` separately).
instance : NormedAddCommGroup (Poly R) := inferInstanceAs (NormedAddCommGroup (R.Mode → ℂ))
instance : NormedSpace ℂ (Poly R) := inferInstanceAs (NormedSpace ℂ (R.Mode → ℂ))
instance : FiniteDimensional ℂ (Poly R) := inferInstanceAs (FiniteDimensional ℂ (R.Mode → ℂ))
instance : CompleteSpace (Poly R) := inferInstanceAs (CompleteSpace (R.Mode → ℂ))

def get (x : R.Mode) : Poly R →L[ℂ] ℂ where
  toFun a := a.part x
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_apply x

@[fun_prop] lemma part_cont (x : R.Mode) : Continuous fun a : Poly R => a.part x := (get x).cont

instance : ContinuousMul (Poly R) := by
  constructor
  change Continuous (fun a : Poly R × Poly R => (a.1*a.2).part)
  apply continuous_pi; intro i; simp only [part_mul]; refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ => ?_
  split <;> fun_prop

def toll (w : V → ℝ) (x : R.Mode) := ∏ i∈x.val,w i

def price (w : V → ℝ) (a : Poly R) := ∑ i,toll w i * ‖a.part i‖
variable {w : V → ℝ} (hw : ∀ x, 0<w x)

include hw in lemma worth (x : R.Mode) : 0 < toll w x := prod_pos fun i _ => hw i
include hw in lemma nonnegative (x : Poly R) : 0≤price w x := sum_nonneg fun i _ => mul_nonneg (worth hw i).le (norm_nonneg _)
@[fun_prop] lemma price_cont (w : V → ℝ) : Continuous fun a : Poly R => price w a := by unfold price; fun_prop

@[simp] lemma solo (x : R.Mode) (v : ℂ) : price w (send x v)=toll w x*‖v‖ := by
  unfold price; rw [sum_eq_single x]
  · simp
  · intro i _ h; simp [h]
  simp
@[simp] lemma quiet_toll : toll w R.quiet=1 := by simp [toll,Census.quiet]
@[simp] lemma solo_toll (x : V) : toll w (R.fire x)=w x := by simp [toll,Census.fire]
@[simp] lemma one_price : price w (1 : Poly R)=1 := by change price w (send R.quiet 1) = _; simp
@[simp] lemma zero_price : price w (0 : Poly R)=0 := by unfold price; simp only [part_nil,norm_zero,mul_zero,sum_const_zero]
@[simp] lemma adapted (x : Poly R) (c : ℂ) : price w (c • x)=‖c‖* price w x := by simp [price,Finset.mul_sum,mul_left_comm]

lemma multiplier (a b c : R.Mode) (h : merges a b c) : toll w c=toll w a*toll w b := by unfold toll; rw [← h.2,Finset.prod_union h.1]
include hw

lemma member (x : R.Mode) (a : Poly R) : toll w x*‖a.part x‖≤price w a :=
    Finset.single_le_sum (fun i _ ↦ mul_nonneg (worth hw i).le (norm_nonneg (a.part i))) (mem_univ _)

/-- finite type bound, use only to prove convergence NOT for size estimates
when growing number of markers. -/
lemma equivalent_norm : ∃ r : ℝ, 0 ≤ r ∧ ∀ a : Poly R, ‖a‖ ≤ price w a*r := by
  haveI : Nonempty R.Mode := ⟨R.quiet⟩
  obtain ⟨y, -, hy⟩ := Finset.exists_min_image Finset.univ (toll w (R:=R)) Finset.univ_nonempty
  refine ⟨(toll w y)⁻¹,inv_nonneg.mpr (worth hw y).le,fun a => ?_⟩
  have hn := worth hw y
  rw [← div_eq_mul_inv]
  change ‖a.part‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (nonnegative hw a) hn.le)).2
  intro i
  rw [le_div_iff₀ hn,mul_comm]
  exact (mul_le_mul_of_nonneg_right (hy i (mem_univ _)) (norm_nonneg _)).trans (member hw i a)

lemma addition (a b : Poly R) : price w (a+b) ≤ price w a+price w b := by
  unfold price; rw [← Finset.sum_add_distrib]; refine sum_le_sum fun i _ => ?_; rw [←mul_add,part_plus]; exact
    mul_le_mul_of_nonneg_left (norm_add_le _ _) (worth hw i).le

lemma batch {X : Type*} (T : Finset X) (a : X → Poly R) : price w (∑ i∈ T,a i) ≤ ∑ i ∈ T, price w (a i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp only [sum_empty,zero_price]; rfl
  | @insert i t hi h => rw [sum_insert hi,sum_insert hi]; exact (addition hw ..).trans (by gcongr)

lemma binary (x y : R.Mode) (i j : ℂ) : price w (send x i*send y j) ≤ toll w x*‖i‖*(toll w y*‖j‖) := by
  by_cases h : ∃ z, merges x y z
  · obtain ⟨z,h⟩ := h
    rw [show send x i*send y j=send z (i*j) by
      ext a; rw [part_send]; change (prod _ _).part _ = _; rw [cart]
      split_ifs with he hh hh
      · rfl
      · exact False.elim (hh (Subtype.ext (he.2.symm.trans h.2)))
      · exact False.elim (he (hh.symm ▸ h))
      rfl]
    rw [solo,multiplier _ _ _ h,norm_mul]; exact le_of_eq (by ring)
  rw [show send x i*send y j=0 by
    ext a; change (prod _ _).part _=0; rw [cart]; split_ifs with he; exact False.elim (h ⟨_,he⟩); rfl, zero_price]
  exact mul_nonneg (mul_nonneg (worth hw _).le (norm_nonneg _)) (mul_nonneg (worth hw _).le (norm_nonneg _))

lemma multiplication (a b : Poly R) : price w (a*b) ≤ price w a*price w b := by
  unfold price

  change price w (a*b) ≤ _
  conv_lhs => rw [← studs a,← studs b,sum_mul]
  apply le_trans (batch hw ..)
  rw [sum_mul]; refine sum_le_sum fun i _ => ?_
  rw [mul_sum,mul_sum]; exact (batch hw ..).trans (sum_le_sum fun j _ ↦ binary hw ..)

lemma multiple {X : Type*} (T : Finset X) (a : X → Poly R) : price w (∏ i∈ T,a i) ≤ ∏ i∈T, price w (a i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp only [prod_empty,one_price]; rfl
  | @insert i t hi h => rw [prod_insert hi,prod_insert hi]; exact (multiplication hw ..).trans (mul_le_mul_of_nonneg_left h (nonnegative hw _))

lemma powers (a : Poly R) (k : ℕ) : price w (a^k) ≤ price w a^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,pow_succ]; exact (multiplication hw ..).trans (mul_le_mul_of_nonneg_right ih (nonnegative hw _))
end YM.Marker.Poly
