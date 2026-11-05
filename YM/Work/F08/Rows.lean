import YM.Bid.Craft
import YM.Work.F08.Width

/-!
Operations at a single scale (used also with residues as indices on a
cross row when composing on the coarse side).  The count in the estimate for
composition is the count of intermediate types, not multiplied by the
period volume.  Products are real kernel products in the counting measure.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.F08
open Lattice Laurent Bloch
open scoped BigOperators

variable {α β ξ : Type*} {η η' A A' B : ℝ} {P R : Row α β} {Q : Row β ξ}

lemma strip_mono (hP : P.strip η A) (he : η' ≤ η) (hb : A ≤ A') : P.strip η' A' :=
  fun i j ↦ (hP i j).mono he hb

/-- Cover convolution, + displacement convention. -/
def composeRows [Fintype β] (P : Row α β) (Q : Row β ξ) : Row α ξ := fun i j z ↦
  ∑ b, routed id (P i b) (fun _ ↦ Q b j) z

lemma strip_compose [Fintype β] (he : 0 ≤ η) (hP : P.strip η A) (hQ : Q.strip η B) :
    (composeRows P Q).strip η (Fintype.card β * (A * B)) := by
  intro i j
  exact width_sum_finite fun b ↦
    width_routed (d := id) he (fun _ ↦ le_rfl) (hP i b) (fun _ ↦ hQ b j)

lemma acts_compose [Fintype β] (he : 0 ≤ η) (hP : P.strip η A) (hQ : Q.strip η B)
    (n : Side) : (composeRows P Q).acts n = P.acts n * Q.acts n := by
  ext ⟨x,i⟩ ⟨y,j⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  change sift (fun z ↦ ∑ b, routed id _ _ z) n x y =
    ∑ b, ∑ w, sift (P i b) n x w * sift (Q b j) n w y
  have hs (b : β) := (width_routed (d := id) he (fun a ↦ le_rfl) (hP i b)
    (fun _ ↦ hQ b j)).summable he
  rw [sift_sum_finite hs]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  calc
    _ = ∑' a, P i b a * sift (Q b j) n (x + wrap n a) y :=
      sift_routed (d := id) he (fun a ↦ le_rfl) (hP i b) (fun _ ↦ hQ b j) n x y
    _ = _ := (sift_action ((hP i b).summable he) n x (fun w ↦ sift (Q b j) n w y)).symm

def minusRows (P R : Row α β) : Row α β := fun i j z ↦ P i j z - R i j z

lemma strip_minus (hP : P.strip η A) (hR : R.strip η B) :
    (minusRows P R).strip η (A + B) := by
  intro i j
  let W (z : Cover) := Real.exp (η * size z)
  let F (z : Cover) := W z * ‖P i j z‖
  let G (z : Cover) := W z * ‖R i j z‖
  have hF : RG.SumBudget F A := hP i j
  have hG : RG.SumBudget G B := hR i j
  have hh : RG.SumBudget (fun z ↦ F z + G z) (A + B) := by
    refine ⟨fun z ↦ add_nonneg (hF.1 z) (hG.1 z), hF.2.1.add hG.2.1, ?_⟩
    rw [Summable.tsum_add hF.2.1 hG.2.1]
    exact add_le_add hF.2.2 hG.2.2
  unfold Width
  refine budget_minor hh (fun _ ↦ by positivity) fun z ↦ ?_
  calc
    W z * ‖P i j z - R i j z‖ ≤ W z * (‖P i j z‖ + ‖R i j z‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le ..) (Real.exp_pos _).le
    _ = F z + G z := by unfold F G; rw [mul_add]

lemma acts_minus (he : 0 ≤ η) (hP : P.strip η A) (hR : R.strip η B)
    (n : Side) : (minusRows P R).acts n = P.acts n - R.acts n := by
  ext ⟨x,i⟩ ⟨y,j⟩
  change sift (minusRows P R i j) n x y = sift (P i j) n x y - sift (R i j) n x y
  unfold sift
  rw [← (summable_sift ((hP i j).summable he) x y).tsum_sub
    (summable_sift ((hR i j).summable he) x y)]
  refine tsum_congr fun z ↦ ?_
  split <;> simp [minusRows]

def scaleRows (l : ℝ) (P : Row α β) : Row α β := fun i j z ↦ l * P i j z

lemma strip_scale (hP : P.strip η A) (l : ℝ) : (scaleRows l P).strip η (‖l‖ * A) := by
  intro i j
  let F (z : Cover) := Real.exp (η * size z) * ‖P i j z‖
  have hh : RG.SumBudget F A := hP i j
  unfold Width
  rw [show (fun z : Cover ↦ Real.exp (η * size z) * ‖scaleRows l P i j z‖) =
    fun z ↦ ‖l‖ * F z by funext z; dsimp only [scaleRows, F]; rw [norm_mul]; ring]
  refine ⟨fun z ↦ mul_nonneg (norm_nonneg _) (hh.1 _), hh.2.1.mul_left _, ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hh.2.2 (norm_nonneg _)

lemma acts_scale (P : Row α β) (l : ℝ) (n : Side) :
    (scaleRows l P).acts n = l • P.acts n := by
  ext ⟨x,i⟩ ⟨y,j⟩
  change sift (scaleRows l P i j) n x y = l * sift (P i j) n x y
  unfold sift
  rw [← tsum_mul_left]
  refine tsum_congr fun z ↦ ?_
  split <;> simp [scaleRows]

/-- Transpose on the torus reverses displacement. -/
def transRows (P : Row α β) : Row β α := fun i j z ↦ P j i (-z)

lemma strip_trans (hP : P.strip η A) : (transRows P).strip η A := by
  intro i j
  let F (z : Cover) := Real.exp (η * size z) * ‖P j i z‖
  let e := Equiv.neg Cover
  have hh : RG.SumBudget F A := hP j i
  unfold Width
  rw [show (fun z : Cover ↦ Real.exp (η * size z) * ‖transRows P i j z‖) =
    F ∘ (e : Cover → Cover) by funext z; simp [size_neg, transRows, F, e]]
  exact ⟨fun z ↦ hh.1 (e z), e.summable_iff.mpr hh.2.1, (e.tsum_eq F).trans_le hh.2.2⟩

lemma acts_trans (P : Row α β) (n : Side) :
    (transRows P).acts n = (P.acts n).transpose := by
  ext ⟨x,i⟩ ⟨y,j⟩
  change sift (transRows P i j) n x y = sift (P j i) n y x
  unfold sift
  let F (z : Cover) := if x = y + wrap n z then P j i z else 0
  change _ = ∑' z, F z
  rw [← (Equiv.neg Cover).tsum_eq F]
  refine tsum_congr fun z ↦ ?_
  have he : y = x + wrap n z ↔ x = y + -(wrap n z) := by
    constructor
    · intro H; rw [H]; simp [add_assoc]
    intro H; rw [H]; simp [add_assoc]
  simp [F, he, transRows]

def stackRows (P : Row α β) (U : Row ξ β) : Row (α ⊕ ξ) β :=
  fun i j z ↦ i.elim (fun a ↦ P a j z) (fun c ↦ U c j z)

lemma strip_stack {U : Row ξ β} (hP : P.strip η A) (hU : U.strip η B) :
    (stackRows P U).strip η (max A B) := by
  rintro (a|c) j
  · exact (hP a j).mono le_rfl (le_max_left ..)
  exact (hU c j).mono le_rfl (le_max_right ..)

lemma acts_stack (P : Row α β) (U : Row ξ β) (n : Side) :
    (stackRows P U).acts n = Craft.stack (P.acts n) (U.acts n) := by
  ext ⟨x,i⟩ ⟨y,j⟩; cases i <;> rfl

def unitRow (α : Type*) [DecidableEq α] : Row α α := fun i j z ↦
  if z = 0 then if i = j then 1 else 0 else 0

lemma strip_unit [DecidableEq α] : (unitRow α).strip η 1 := by
  intro i j
  let F (z : Cover) := Real.exp (η * size z) * ‖unitRow α i j z‖
  have hz (z : Cover) (h : z ≠ 0) : F z = 0 := by simp [F, unitRow, h]
  change RG.SumBudget F 1
  refine ⟨fun z ↦ ?_, summable_of_ne_finset_zero (s := {0}) ?_, ?_⟩
  · unfold F; positivity
  · intro z h; exact hz z (by simpa using h)
  rw [tsum_eq_single 0 hz]
  by_cases hi : i = j <;> simp [F, unitRow, hi, size]

lemma acts_unit [DecidableEq α] (n : Side) : (unitRow α).acts n = 1 := by
  ext ⟨x,i⟩ ⟨y,j⟩
  rw [Row.acts, Matrix.of_apply, tsum_eq_single 0, Matrix.one_apply]
  · by_cases he : x = y <;> simp [unitRow, *, eq_comm]
  intro z hz
  simp [unitRow, hz]

end YM.Work.F08
