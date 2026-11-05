import YM.Laurent.Art
import YM.Push.FREE_RESOLVENT.Weights
import YM.Work.F08.Rows



/-!
# Tori and periodized rows

We price using native torus max-distance (also give l¹). A cover row
at displacement z puts its *input* at x + wrap z. Charged also after
restriction/lifting to a principal set. Comparing unequal periods uses
actual tails of the SAME cover coefficient, not least-image summation.
Cut a Row on cover `size` (one-norm) when viewing it as a stencil.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice Laurent Bloch Work.F08 Matrix
open scoped BigOperators
variable {α β ι : Type*} {n : Side}

def native (n : Side) : Cost (Site n) where
  d x y := (separation x y : ℝ)
  nonneg x y := by positivity
  self x := by simp
  comm x y := by rw [separation_comm]
  triangle x y z := by exact_mod_cast separation_triangle x y z

def taxi (n : Side) : Cost (Site n) where
  d x y := (size (lift (y-x)) : ℝ)
  nonneg x y := by positivity
  self x := by simp [size,lift]
  comm x y := by rw [← neg_sub x y]; simp only [lift,size,Pi.neg_apply,ZMod.natAbs_valMinAbs_neg]
  triangle x y z := by
    have h : size (lift (z-x)) ≤ size (lift (y-x)) + size (lift (z-y)) := by
      rw [show z-x=(y-x)+(z-y) by abel]
      unfold size; rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      exact (ZMod.natAbs_valMinAbs_add_le ((y-x) i) ((z-y) i)).trans (Int.natAbs_add_le ..)
    exact_mod_cast h

lemma own_size (x : Cover) (i : Axis) : (x i).natAbs ≤ size x := Finset.single_le_sum
  (f:=fun i => (x i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma wrap_size (n : Side) (x : Cover) : size (lift (wrap n x)) ≤ size x := by
  refine Finset.sum_le_sum fun i _ => ?_
  change (lift (wrap n x) i).natAbs ≤ (x i).natAbs
  by_contra! he
  have ht := lift_centers (wrap n x) i
  have hy : lift (wrap n x) i = x i := (ZMod.valMinAbs_spec _ _).2 ⟨rfl, by
    change -(n.val:ℤ) < x i * 2 ∧ x i * 2 ≤ n.val
    omega⟩
  omega

lemma native_le_taxi (x y : Site n) : (native n).d x y ≤ (taxi n).d x y := by
  have h : separation x y ≤ size (lift (y-x)) := by
    rw [separation_comm]; unfold separation pdist; exact Finset.sup_le (fun i _ => own_size _ i)
  change ((separation x y:ℕ):ℝ) ≤ ((size _:ℕ):ℝ)
  exact_mod_cast h

lemma taxi_le_native (x y : Site n) : (taxi n).d x y ≤ 4*(native n).d x y := by
  have h : size (lift (y-x)) ≤ 4 * separation x y := by
    rw [separation_comm]
    calc
      _ ≤ ∑ _i : Axis, separation y x := Finset.sum_le_sum fun i _ => component_le (y-x) i
      _ = _ := by simp [Axis]
  change ((size _:ℕ):ℝ) ≤ 4*((separation x y:ℕ):ℝ)
  exact_mod_cast h

lemma wrap_bound (x : Site n) (z : Cover) : (taxi n).d x (x+wrap n z) ≤ size z := by
  change ((size (lift (_-_))) : ℝ) ≤ _
  rw [add_sub_cancel_left]; exact_mod_cast wrap_size n z

/-- Volume prices, independent of n (include volume at n=1); `sheetPay`
for a single position type, `torusPay` for all fibers including columns if
priced on the transpose. -/
def sheetPay (s : ℝ) := (2*((1+s)/s))^(Fintype.card Axis)
def torusPay (α : Type*) [Fintype α] (s : ℝ) := (Fintype.card α : ℝ)*sheetPay (s/4)

lemma sheetPay_pos (s : ℝ) (hs : 0 < s) : 0 < sheetPay s := by unfold sheetPay; positivity
lemma torusPay_nn (α : Type*) [Fintype α] (s : ℝ) (hs : 0 < s) : 0 ≤ torusPay α s :=
  mul_nonneg (by positivity) (sheetPay_pos _ (by linarith)).le

lemma taxi_volume (x : Site n) (s : ℝ) (hs : 0 < s) :
    ∑ y, (taxi n).weight (-s) x y ≤ sheetPay s := by
  classical
  let ρ (y : Site n) := lift (y-x)
  let F (z : Cover) := Real.exp (-s*size z)
  have hk : YM.RG.SumBudget F (sheetPay s) := Width.compactPay _ hs
  have hi : Function.Injective ρ := by
    intro y w h; have he := congr_arg (wrap n) h; unfold ρ at he; simpa using he
  calc
    _ = ∑ z ∈ Finset.univ.image ρ, F z := (Finset.sum_image hi.injOn).symm
    _ ≤ _ := (hk.2.1.sum_le_tsum _ (fun i _ => hk.1 i)).trans hk.2.2

lemma volume (n : Side) (α : Type*) [Fintype α] (s : ℝ) (hs : 0 < s) :
    (native n).Volume (Prod.fst : Site n × α → _) s (torusPay α s) := by
  constructor; intro x
  have h (y : Site n) : (native n).weight (-s) x y ≤ (taxi n).weight (-(s/4)) x y := by
    apply Real.exp_monotone
    nlinarith only [mul_le_mul_of_nonneg_left (taxi_le_native x y) hs.le]
  rw [Fintype.sum_prod_type]; simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun y _ => h y).trans (taxi_volume x _ (by linarith))) (by positivity)

/-- Lifted strip norm is enough for actual row AND column norms with no rate loss. -/
lemma physical_rows [Fintype β] {s M : ℝ} {A : Row α β} (h : A.strip s M) (hs : 0 ≤ s) (n : Side) :
    (taxi n).Rows Prod.fst Prod.fst s ((Fintype.card β:ℝ)*M) (A.acts n) := by
  constructor; rintro ⟨x,i⟩
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine le_trans (Finset.sum_le_sum (g:= fun _ => M) fun j _ => ?_) (le_of_eq (by simp))
  let F (z) := ‖A i j z‖
  let W (y) := (taxi n).weight s x y
  have hh : Width s M (A i j) := h i j
  have he : Summable F := (hh.unweighted hs).2.1
  have hpt (y : Site n) : |(A.acts n) (x,i) (y,j)| ≤ sift F n x y := by
    let P (z) := if y=x+wrap n z then A i j z else 0
    have hw : (fun z => if y=x+wrap n z then F z else 0) = fun z => ‖P z‖ := by
      funext z; by_cases h : y=x+wrap n z <;> simp [P,h,F]
    unfold sift; rw [hw]
    exact norm_tsum_le_tsum_norm (show Summable (fun z => ‖P z‖) from hw ▸ summable_sift he x y)
  have ht (z) : F z * W (x+wrap n z) ≤ Real.exp (s*size z)*F z := by
    rw [mul_comm (F z)]
    exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (wrap_bound x z) hs)) (norm_nonneg _)
  have hsum := Summable.of_nonneg_of_le (fun z => mul_nonneg (by unfold F; positivity) ((taxi n).weight_nn ..)) ht hh.2.1
  change ∑ y, W y*_ ≤ M
  calc
    _ ≤ ∑ y, sift F n x y * W y := Finset.sum_le_sum fun y _ => by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hpt y) ((taxi n).weight_nn ..)
    _ = ∑' z, F z * W (x+wrap n z) := sift_action he n x _
    _ ≤ M := (hsum.tsum_le_tsum ht hh.2.1).trans hh.2.2

lemma physical_cols [Fintype α] {s M : ℝ} {A : Row α β} (h : A.strip s M) (hs : 0 ≤ s) (n : Side) :
    (taxi n).Rows Prod.fst Prod.fst s ((Fintype.card α:ℝ)*M) (A.acts n).transpose := by
  rw [← acts_trans]; exact physical_rows (strip_trans h) hs n

lemma taxi_schur [Fintype α] {s M : ℝ} {A : Row α α} (h : A.strip s M) (hs : 0 ≤ s) (n : Side) :
    (taxi n).Schur Prod.fst Prod.fst s ((Fintype.card α:ℝ)*M) (A.acts n) :=
  ⟨physical_rows h hs n, physical_cols h hs n⟩

lemma downgrade {a : α → Site n} {b : β → Site n} [Fintype β] {A : Matrix α β ℝ} {s M : ℝ}
    (h : (taxi n).Rows a b s M A) (hs : 0 ≤ s) : (native n).Rows a b s M A := by
  constructor; intro i
  apply le_trans (Finset.sum_le_sum fun j _ => ?_) (h.bound i)
  exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (native_le_taxi ..) hs)) (abs_nonneg _)

lemma physical [Fintype α] {s M : ℝ} {A : Row α α} (h : A.strip s M) (hs : 0 ≤ s) (n : Side) :
    (native n).Schur Prod.fst Prod.fst s ((Fintype.card α:ℝ)*M) (A.acts n) :=
  ⟨downgrade (physical_rows h hs n) hs, downgrade (physical_cols h hs n) hs⟩

/-- True-length cut on numerical Row (native cover displacements). -/
def shorten (R : ℕ) (A : Row α β) : Row α β := fun i j z => if size z ≤ R then A i j z else 0

lemma strip_shorten {s M : ℝ} {A : Row α β} (h : A.strip s M) (R : ℕ) : (shorten R A).strip s M := by
  intro i j; unfold Width
  apply budget_minor (h i j) (fun _ => by positivity)
  intro z; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  by_cases he : size z ≤ R <;> simp [shorten, he]

lemma strip_tail {s M γ : ℝ} {A : Row α β} (h : A.strip s M) (R : ℕ) (hg : γ ≤ s) :
    (minusRows A (shorten R A)).strip γ (Real.exp ((γ-s)*R)*M) := by
  intro i j; unfold Width
  let C := Real.exp ((γ-s)*R)
  have hc := Real.exp_pos ((γ-s)*R)
  let F := fun z => Real.exp (s*size z)*‖A i j z‖
  have hb : RG.SumBudget (fun z => C*F z) (C*M) := ⟨fun z => mul_nonneg hc.le ((h i j).1 z),
      (h i j).2.1.mul_left _, by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (h i j).2.2 hc.le⟩
  refine budget_minor hb (fun _ => by positivity) ?_
  intro z; by_cases he : size z ≤ R
  · simp only [minusRows,shorten,he,↓reduceIte,sub_self,norm_zero,mul_zero]; exact hb.1 z
  simp only [minusRows,shorten,he,↓reduceIte,sub_zero,F,← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold C; rw [← Real.exp_add, Real.exp_le_exp]
  have he' : (R:ℝ) ≤ size z := by exact_mod_cast Nat.le_of_lt (lt_of_not_ge he)
  linarith only [mul_le_mul_of_nonpos_left he' (sub_nonpos.mpr hg)]

lemma size_centers (n : Side) (x : Cover) {R : ℕ} (h : size x ≤ R) (he : 2*R < n.val) :
    lift (wrap n x) = x := by
  refine lift_eq_iff.mpr ⟨rfl,fun i => ?_⟩
  have hi := own_size x i
  omega

/-- If the shortened cover stencil embeds, its actual entries along
retained displacements are precisely the common stencil. -/
lemma cut_lift (A : Row α β) (x : Site n) (z : Cover) (i : α) (j : β) (R : ℕ)
    (h : size z ≤ R) (he : 2*R < n.val) :
    (shorten R A).acts n (x,i) (x+wrap n z,j) = A i j z := by
  rw [Row.acts, Matrix.of_apply, tsum_eq_single z]
  · simp [shorten,h]
  intro v hv
  split_ifs with hs; swap; · rfl
  simp only [add_right_inj] at hs
  unfold shorten; rw [if_neg]; intro hw; exact hv (by
    rw [← size_centers n v hw he, ← hs]; exact size_centers n z h he)

lemma lift_comparison [Fintype β] {s M : ℝ} {A : Row α β} (h : A.strip s M) (hs : 0 ≤ s)
    (x : Site n) (z : Cover) (i : α) (j : β) (R : ℕ) (hz : size z ≤ R) (he : 2*R < n.val) :
    |A.acts n (x,i) (x+wrap n z,j)-A i j z| ≤ (Fintype.card β:ℝ)*(Real.exp (-s*R)*M) := by
  have hh := physical_rows (strip_tail h R hs) le_rfl n
  rw [acts_minus hs h (strip_shorten h R)] at hh
  simpa only [Cost.weight_zero, one_mul, Matrix.sub_apply, cut_lift A x z i j R hz he, zero_sub] using
    hh.weighted (x,i) (x+wrap n z,j)

end YM.FreeResolvent
