import YM.RG08.Flat.Differences
import YM.Push.ABSOLUTE_SUMS.Array

/-!
# Input/output width transfer across resolutions

`routed` uses the true integer carry. On a plateau the same width must often
be obtainable at output despite a width loss at fine differentiation/lifting.
We pay coarse exponential weights from fine ones using `L*size(carry)`, not
from a fixed, geometrically decreasing strip at every step.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Finset Laurent Lattice Wilson Bloch Matrix Precision
open Next.Free Work.F08 Push.AbsoluteSums RG
open scoped Topology BigOperators

lemma block_carry {L : Side} (r : Site L) (a : Cover) :
    L.val*size (carry r a) ≤ size a + 4*L.val := by
  have h (i : Axis) : L.val*(carry r a i).natAbs ≤ (a i).natAbs + L.val := by
    have he := congr_fun (carry_spec r a) i
    simp only [Pi.add_apply, Pi.mul_apply, Pi.natCast_apply,nsmul_eq_mul] at he
    have hu := lift_centers r i
    have hv := lift_centers (arrives r a) i
    rw [show L.val * (carry r a i).natAbs = ((L.val:ℤ) * carry r a i).natAbs from by
      rw [Int.natAbs_mul, Int.natAbs_natCast]]
    omega
  have H : L.val * size (carry r a) ≤ size a + (Fintype.card Axis)*L.val := by
    unfold size
    rw [Finset.mul_sum]
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using
      Finset.sum_le_sum (s:=Finset.univ) (fun i _ => h i)
  exact H

lemma size_scaled {L : Side} (r : Site L) (a z : Cover) {η σ : ℝ}
    (he : 0 ≤ η) (h : η ≤ L.val*σ) :
    η*size z ≤ σ*size a + 4*η + η*size (z-carry r a) := by
  let d := carry r a
  have hc : (L.val:ℝ)*(size d:ℝ) ≤ size a + 4*L.val := by exact_mod_cast block_carry r a
  have hl : 0 < (L.val:ℝ) := by positivity
  have hu : η*size d ≤ σ*size a + 4*η := by
    apply le_of_mul_le_mul_right _ hl
    calc
      _ = η*(L.val* (size d:ℝ)) := by ring
      _ ≤ η*(size a + 4*L.val) := mul_le_mul_of_nonneg_left hc he
      _ = η*size a + 4*η*L.val := by ring
      _ ≤ L.val*σ*size a + 4*η*L.val := by gcongr
      _ = _ := by ring
  have hx : size z ≤ size (z-d) + size d := by
    nth_rewrite 1 [← sub_add_cancel z d]
    exact size_add ..
  have hv : (size z:ℝ) ≤ size (z-d) + size d := by exact_mod_cast hx
  change η * _ ≤ _ + η*size (z-d)
  nlinarith only [hu,mul_le_mul_of_nonneg_left hv he]

section Budgets
variable {α β E : Type*}

/-- Project after summing an internal argument; keep absolute budgets. -/
lemma budget_onto_rows {g : α×β → ℝ} {A : ℝ} (h : SumBudget g A) :
    SumBudget (fun x : α => ∑' y : β, g (x,y)) A :=
  ⟨fun _ => tsum_nonneg fun _ => h.1 _,
    ((summable_prod_of_nonneg h.1).mp h.2.1).2, h.2.1.tsum_prod.symm.trans_le h.2.2⟩

/-- General coefficient convolution usage: weights strict to avoid any
    unconditional sums on zero weight fibers. -/
lemma budget_projection [NormedAddCommGroup E] {g : α×β → E} {A : ℝ}
    (w : β → ℝ) (hw : ∀ i, 0 < w i)
    (h : SumBudget (fun i : α×β => w i.2 * ‖g i‖) A) :
    SumBudget (fun x : β => w x * ‖∑' y : α, g (y,x)‖) A := by
  have he := budget_pull (Equiv.prodComm β α) (Equiv.prodComm β α).injective h
  refine budget_mono (budget_onto_rows he) (fun i => mul_nonneg (hw i).le (norm_nonneg _)) ?_
  intro i
  change w i*_ ≤ ∑' y : α, w i*‖g (y,i)‖
  rw [tsum_mul_left]
  have hy : Summable (fun y : α => w i * ‖g (y,i)‖) :=
    ((summable_prod_of_nonneg he.1).mp he.2.1).1 i
  exact mul_le_mul_of_nonneg_left
    (norm_tsum_le_tsum_norm <| (summable_mul_left_iff (hw i).ne').mp hy) (hw i).le

end Budgets

/-- Row routing after spending pre-block width. No multiplicity cost from
    old fine aggregation. -/
theorem carry_price {L : Side} {η σ A B : ℝ} (r : Site L) (he : 0 ≤ η)
    (h : η ≤ L.val*σ) {f : Cover → ℝ} {g : Cover → Cover → ℝ}
    (hf : Width σ A f) (hg : ∀ a, Width η B (g a)) :
    Width η (Real.exp (4*η) * A * B) (routed (carry r) f g) := by
  let d := carry r
  let K := Real.exp (4*η)
  let w (z : Cover) := Real.exp (η*size z)
  let u (z : Cover) := Real.exp (σ*size z)
  have hp (a z) : w z ≤ K*u a*w (z-d a) := by
    unfold w K u; rw [← Real.exp_add,← Real.exp_add]
    exact Real.exp_le_exp.mpr (by rw [add_comm (4*η)]; exact size_scaled r a z he h)
  have hb : 0 ≤ B := budget_nonneg (hg 0)
  let b (a z : Cover) := g a (z-d a)
  have hk a : SumBudget (fun z => w (z-d a)*‖b a z‖) B := by
    let e := Equiv.addRight (-d a)
    simpa [e,b,sub_eq_add_neg] using
      budget_pull e e.injective (show SumBudget (fun z => w z*‖g a z‖) B from hg a)
  have hh a : 0 ≤ K*(u a*‖f a‖) := by unfold u K; positivity
  change SumBudget (fun z => w z * ‖∑' y, f y * b y z‖) _
  let l (a : Cover) := K*(u a*‖f a‖)
  apply budget_projection (g:=fun i : Cover×Cover => f i.1 * b i.1 i.2) _ (fun i => Real.exp_pos _)
  refine budget_rows _ (fun a => l a * B) (fun a => ?_) ?_
  · refine budget_mono (budget_scale (hh a) (hk a)) (fun z => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ?_
    intro z
    apply (mul_le_mul_of_nonneg_right (hp a z) (norm_nonneg (f a*b a z))).trans_eq
    rw [norm_mul]; ring
  rw [show (fun a => l a*B)=(fun a => B*l a) from funext fun a => mul_comm ..,
    mul_comm _ B]
  exact budget_scale hb (budget_scale (Real.exp_pos _).le hf)

section Matrix
variable {L c f : Side} {σ τ A B : ℝ}
variable {α β γ : Type*} [Fintype α]

lemma strip_routed {P : Row γ α} {Q : Cross L α β} (he : 0 ≤ τ)
    (ht : τ ≤ L.val*σ) (hP : P.strip σ A) (hQ : Q.strip τ B) :
    (fineCompose P Q).strip τ (Fintype.card α * (Real.exp (4*τ)*A*B)) := by
  rintro ⟨r,i⟩ j
  exact width_sum_finite fun k => carry_price r he ht (hP i k) (fun a => hQ _ _)

lemma composed_left (g : Ratio c f) {P : Cross g.count α β} {Q : Cross g.count α γ}
    (hp : Whole P) (hq : Whole Q) :
    (composeRows (transRows P) Q).acts c = (installed g P)ᵀ * installed g Q := by
  have hT : Whole (transRows P) := by
    obtain ⟨v,D,hD,h⟩ := hp; exact ⟨v,D,hD,strip_trans h⟩
  rw [hT.acts hq, acts_trans]
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, installed,Matrix.submatrix_apply,id_eq]
  exact (Equiv.sum_comp (splitCo g α) fun k => P.acts c k i * Q.acts c k j).symm

end Matrix
end YM.RG08
