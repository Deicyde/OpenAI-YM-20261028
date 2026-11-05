import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Moment

/-!
# Canonical interpolation attaching one vertex to the rooted block

θ in `0..π/2`. Rotate all the currently fused arguments one way at
*the same time*, so no loss of their internal covariance; their joint
law on the outside endpoint actually factors including all duplicate
coordinates. The change pushes standard of a fresh doubled dimension,
not a singular covariance derivative.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open MeasureTheory ProbabilityTheory Filter Function Set Finset
open YM.Multi.Vacuum.Gauss Probe Quadratic Moment
open scoped Topology BigOperators

variable {I J V : Type} [Fintype J] [DecidableEq V]
namespace Spin

def high := Real.pi/2
lemma high_pos : 0 < high := half_pos Real.pi_pos
lemma cos_pos {x : ℝ} (h : x∈Set.Icc (0:ℝ) high) : 0 ≤ Real.cos x :=
  Real.cos_nonneg_of_mem_Icc ⟨le_trans (by have := Real.pi_pos; linarith) h.1,h.2⟩
lemma sin_pos {x : ℝ} (h : x∈Set.Icc (0:ℝ) high) : 0 ≤ Real.sin x :=
  Real.sin_nonneg_of_nonneg_of_le_pi h.1 (h.2.trans (half_le_self (Real.pi_pos.le)))

/-- Scale & concatenate two uses of the row. -/
def duet (a b : ℝ) (q : Row J) : Row (J ⊕ J) := Sum.elim (a • q) (b • q)

lemma duet_cross (a b c d : ℝ) (q p : Row J) : crossed (duet a b q) (duet c d p)=(a*c+b*d)*crossed q p := by
  unfold crossed duet; rw [Fintype.sum_sum_type, add_mul]
  simp only [Pi.smul_apply,smul_eq_mul,Sum.elim_inl,Sum.elim_inr,Finset.mul_sum]
  congr 1 <;> (apply sum_congr rfl; intro i _; ring)
lemma duet_read (a b : ℝ) (q : Row J) (x : Row (J ⊕ J)) : crossed (duet a b q) x =
    a * crossed q (fun i => x (.inl i)) + b * crossed q (fun i => x (.inr i)) := by
  unfold crossed duet; rw [Fintype.sum_sum_type]; simp [Finset.mul_sum,Pi.smul_apply, mul_assoc]

variable (A : Finset V) (q : Rows V I J)

def path (x : ℝ) : Rows V I (J ⊕ J) := fun i a => if i∈A then duet (Real.sin x) (Real.cos x) (q i a) else duet 1 0 (q i a)

def flux (x : ℝ) : Rows V I (J ⊕ J) := fun i a => if i∈A then duet (Real.cos x) (-Real.sin x) (q i a) else duet 0 0 (q i a)

def discount (x : ℝ) (i j : V) : ℝ := if (i∈A ↔ j∈A) then 1 else Real.sin x

lemma clear (x : ℝ) (i j : V) (a b : I) : crossed (path A q x i a) (path A q x j b)=discount A x i j * crossed (q i a) (q j b) := by
  have hi := Real.sin_sq_add_cos_sq x; rw [pow_two,pow_two] at hi
  by_cases he : i∈A <;> by_cases hh : j∈A <;> simp [discount,path,he,hh,duet_cross,hi]
lemma under (x : ℝ) (i j : V) (a b : I) : |crossed (path A q x i a) (path A q x j b)| ≤ |crossed (q i a) (q j b)| := by
  rw [clear,abs_mul]; unfold discount; split
  · simp
  exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)
lemma clear_rate (x : ℝ) (i j : V) (a b : I) : crossed (path A q x j b) (flux A q x i a) =
    if i ∈ A ∧ j ∉ A then Real.cos x * crossed (q i a) (q j b) else 0 := by
  by_cases he : i∈A <;> by_cases hh : j∈A <;> simp [path,flux,he,hh,duet_cross,crossed_comm (q i a)]
  left; ring
lemma same (x : ℝ) (i : V) (a : I) : squares (path A q x i a)=squares (q i a) := by
  rw [← crossed_self,clear]; simp [discount,crossed_self]
lemma stable (x : ℝ) (i : V) (a : I) : squares (flux A q x i a) ≤ squares (q i a) := by
  rw [← crossed_self]; unfold flux; split
  · rw [duet_cross,crossed_self,show _ + (-Real.sin x)*(-Real.sin x)=1 from ?_,one_mul];
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [duet_cross]; simpa using squares_nn (q i a)

omit [Fintype J] in
lemma rate (i : V) (a : I) (t : ℝ) : HasDerivAt (fun t => path A q t i a) (flux A q t i a) t := by
  apply hasDerivAt_pi.mpr
  intro b; unfold path flux; split
  · cases b with
    | inl b => exact (Real.hasDerivAt_sin t).mul_const _
    | inr b => exact (Real.hasDerivAt_cos t).mul_const _
  rename_i he
  -- split binder separately
  cases b <;> simp only [duet,Pi.smul_apply, smul_eq_mul, one_mul,zero_mul,Sum.elim_inr,Sum.elim_inl] <;>
    exact hasDerivAt_const ..

variable {v : Probes V I} {T s : Finset V} {w : V → Row I} {H : V → ℕ → ℝ}

section
variable [Fintype I]
lemma keeps (hx : base q T w) (t : ℝ) : base (path A q t) T w := by
  apply base.of (fun i hi => hx.nn hi)
  intro i hi a; apply le_trans _ (hx.le hi a)
  exact sum_le_sum fun j hj => sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (under A q t ..) (hx.nn hj b)
lemma same_charge (t : ℝ) : due s (path A q t) w = due s q w := by unfold due; simp_rw [same]
end

section
variable (s : Finset V) (v : Probes V I)
private def parts : Row (J⊕J) ≃ᵐ Row J × Row J := MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)
private lemma origin : MeasurePreserving (parts (J:=J)) (standard (J⊕J)) ((standard J).prod (standard J)) :=
  measurePreserving_sumPiEquivProdPi (fun _ => gaussianReal 0 1)

omit [DecidableEq V] in
private lemma simple (F : Finset V) (x : Row (J⊕J)) {L M : ℝ} (k : Rows V I (J⊕J))
    (h : ∀ i ∈ F, ∀ a : I, k i a= duet L M (q i a)) : values F k v x=values F q v
      (L • (parts x).1+M • (parts x).2) := by
  apply prod_congr rfl
  intro i hi; apply congrArg (v i)
  funext j; unfold mapRows; rw [h _ hi,duet_read,crossed]
  unfold crossed; simp_rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul, mul_add,sum_add_distrib,Finset.mul_sum]
  have he : parts x=(fun i => x (.inl i),fun i => x (.inr i)) := rfl
  rw [he]
  congr 1 <;> (apply sum_congr rfl; intro k _; ring)

private lemma first_law (F : Row J → ℂ) :
    (∫ x, F (parts x).1 ∂standard (J⊕J))= ∫ x,F x ∂standard J := by
  rw [← show (fun x : Row (J⊕J) => (fun z : Row J × Row J => F z.1* (1:ℂ)) (parts x))=(fun x => F (parts x).1) from by simp]
  rw [(origin (J:=J)).integral_comp' (fun z => F z.1*(1:ℂ)),integral_prod_mul F (fun _ : Row J => 1)]; simp

lemma final_total : total s (path A q high) v=total s q v := by
  have hx x := simple q v s x (path A q high) (L:=1) (M:=0) (fun i hi j => by simp [path,high])
  simp only [one_smul, zero_smul, add_zero] at hx; unfold total; simp_rw [hx]; exact first_law _

lemma alone_total (t : ℝ) (ht : Disjoint s A) : total s (path A q t) v=total s q v := by
  have hx x := simple q v s x (path A q t) (L:=1) (M:=0) (fun i hi j => if_neg (fun e => disjoint_left.mp ht hi e))
  simp only [one_smul, zero_smul, add_zero] at hx; unfold total; simp_rw [hx]; exact first_law _

lemma apart_total (F W : Finset V) (hF : F⊆A) (hW : Disjoint W A) :
    total (F ∪ W) (path A q 0) v=total F q v*total W q v := by
  have hr (x : Row (J⊕J)) : values (F ∪ W) (path A q 0) v x =
      (fun z : Row J × Row J => values W q v z.1*values F q v z.2) (parts x) := by
    have h₁ := simple q v F x (path A q 0) (L:=0) (M:=1) (fun i hi j => by simp [path,hF hi])
    have h₂ := simple q v W x (path A q 0) (L:=1) (M:=0) (fun i hi j => if_neg (fun e => disjoint_left.mp hW hi e))
    rw [show values (F∪W) (path A q 0) v x= _ * values W (path A q 0) v x from prod_union (hW.symm.mono_left hF), h₂]
    change values F (path A q 0) v x * _=_
    rw [h₁]; simp only [one_smul,zero_smul,add_zero,zero_add,mul_comm]
  unfold total; rw [funext hr,origin.integral_comp', integral_prod_mul,mul_comm]
end
end Spin
end YM.Primitives.GCC
