import YM.Next.RANK.Prayer
import YM.Next.RANK.Stride

/-! Replace low pair covariance comparison on the Origin derivatives of arcs
by ordinary Maxwell tensor at the normalized positions in k layout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Prayer
open Function Lattice Wilson RG Maxwell Maxwell.Wick Labels Normal Beamer Perch Configuration   Filter 
open scoped Topology BigOperators Classical

variable {G : Gauge} {d n : ℕ}
variable {x : Points n}
open Finset

lemma shocks (x : Degree G) (r) (j : KeyIn G d) :
    Beamer.amount r x * gesture x (arbor d r j) = Beamer.amount r x*((r^Labels.generation j.val)⁻¹*gesture x (tester j.val)) := by rw [arbor,map_smul,smul_eq_mul]
lemma overcast (x : Degree G) {r} (hr : 0<r) :
    (∀ j : KeyIn G d,j.val.1 < x.degree → Beamer.amount r x * gesture x (arbor d r j)=0) ∧ (∀ j : KeyIn G d,j.val.1=x.degree → Beamer.amount r x*gesture x (arbor d r j)=gesture x (tester j.val)) := by
  constructor <;> intro j h <;> rw [shocks x r j]
  · rw [tester,gesture_over x h (axes G _ _),mul_zero,mul_zero]
  unfold Beamer.amount Labels.generation; rw [h]; field_simp
lemma towering (x : Degree G) {r} (hr : 1≤r) (j : KeyIn G d) :
    (‖Beamer.amount r x*gesture x (arbor d r j)‖) ≤ ‖gesture x (tester j.val)‖ := by
  have hp := zero_lt_one.trans_le hr; by_cases hx : j.val.1 < x.degree
  · rw [(overcast x hp).1 j hx,norm_zero]; exact norm_nonneg _
  rw [shocks x, ← mul_assoc,norm_mul, ← div_eq_mul_inv,Real.norm_of_nonneg (div_nonneg (show 0 ≤ Beamer.amount r x from (pow_pos hp _).le) (pow_pos hp _).le)]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [div_le_one (by positivity)]; unfold Beamer.amount generation; gcongr; omega
lemma skyward (x : Degree G) {r} (hr : 1≤r) (j : KeyIn G d) (h : j.val.1 ≠ x.degree) :
    r* (‖Beamer.amount r x * gesture x (arbor d r j)‖) ≤ ‖gesture x (tester j.val)‖ := by
  have hp := zero_lt_one.trans_le hr
  rcases lt_or_gt_of_ne h with hw|hw
  · rw [(overcast x hp).1 j hw,norm_zero,mul_zero]; exact norm_nonneg _
  rw [shocks x,← mul_assoc,norm_mul,← div_eq_mul_inv,Real.norm_of_nonneg (div_nonneg (show 0 ≤ Beamer.amount r x from pow_nonneg hp.le _) (by positivity : 0 ≤ r^(Labels.generation j.val))), ← mul_assoc]
  apply mul_le_of_le_one_left (norm_nonneg _); rw [← mul_div_assoc,div_le_one (by positivity)]
  unfold Beamer.amount generation; rw [mul_comm r, ← pow_succ]; exact pow_le_pow_right₀ hr (by omega)
lemma at_curve {C : KeyIn G d → KeyIn G d → ℝ} (r : ℝ) (x y : Degree G) :
    amount r x * amount r y * (mourn (gesture x) (gesture y) (arc d r C))=∑ i : KeyIn G d,∑ j,
      C i j * ((amount r x*gesture x (arbor d r i))*(amount r y * gesture y (arbor d r j))) := by
  unfold arc; simp_rw [map_sum,map_smul,Finset.mul_sum]
  apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
  change _* ((C i j) • gesture x (fun X => gesture y (arbor d r i X • arbor d r j)))= _
  simp_rw [map_smul]
  rw [show (fun X => arbor d r i X • _)=(gesture y (arbor d r j)) • (arbor d r i) from funext fun a => mul_comm (arbor d r i a) (gesture y (arbor d r j)),map_smul]; simp only [smul_eq_mul]; ring

section
variable (x : Points n) (L S : Hub G d 0) {i j : Fin n}

def wand (L : Hub G d 0) := Finset.univ.filter fun i : KeyIn G d => i.val.1 = L.val.degree
private def view (x) (hx : x∈conf n) (i j : Fin n) (L S : Hub G d 0) (r : ℝ) := fun a b : KeyIn G d =>
    ((currentX hx G d).cov (i,a) (j,b)).re * ((amount r L.val * gesture L.val (arbor d r a)) * (amount r S.val * gesture S.val (arbor d r b)))



private def cap (w : Hub G d 0) (i : Fin (Labels.dim G w.val.degree)) := (fan i w.property.2.2 w.property.2.1).val
private lemma booth (w : Hub G d 0) : wand w=univ.image (cap w) := by
  ext p; simp only [wand,mem_filter,true_and,mem_univ,mem_image]; rcases p with ⟨⟨j,v⟩,h⟩
  constructor
  · intro H; change j=w.val.degree at H; subst j; exact ⟨_,rfl⟩
  rintro ⟨q,hp⟩; exact congr_arg (fun p : KeyIn G d => p.val.1) hp.symm
private lemma still (w : Hub G d 0) : Function.Injective (cap w) := fun _ _ H => eq_of_heq ((Sigma.mk.inj (congr_arg Subtype.val H)).2)

lemma deck (hx : x∈conf n) (h : i ≠ j) {r : ℝ} (hr : 0<r) : ∑ a∈ wand L, ∑ b∈ wand S, view x hx i j L S r a b=light L.val S.val (x i) (x j) := by
  simp_rw [booth L,booth S, sum_image (still L).injOn,sum_image (still S).injOn]; refine Eq.trans (b:=_) ?_ (measured hx h L S)
  apply sum_congr rfl; intro b _; apply sum_congr rfl; intro a _; unfold view
  rw [(overcast L.val hr).2 (cap L b) rfl,(overcast S.val hr).2 (cap S a) rfl]; rfl

/-- Loss in sample subleading terms uniform as long free covariance remains bounded. -/
theorem fence : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Points n) (hx : x∈conf n) (i j : Fin n), i≠j → ∀ D : ℝ, 0 ≤ D →
    (∀ a b, |((currentX hx G d).cov (i,a) (j,b)).re|≤D) → ∀ r : ℝ,1≤r →
    r* ‖amount r L.val*amount r S.val*mourn (gesture L.val) (gesture S.val) (collect d hx r G i j)-light L.val S.val (x i) (x j)‖ ≤ C*D := by
  let X (P : Hub G d 0) (i : KeyIn G d):= ‖gesture P.val (tester i.val)‖
  let A : Finset (KeyIn G d × KeyIn G d) := wand L ×ˢ wand S
  let B (z : KeyIn G d×KeyIn G d) := X L z.1*X S z.2
  let u:= univ \ A
  refine ⟨∑ z∈u,B z,sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _), fun x hx i j h D hD hX r hr => ?_⟩
  rw [← deck x L S hx h (zero_lt_one.trans_le hr)]; let v := view x hx i j L S r
  have hv : amount r L.val*amount r S.val * _ =∑ k,∑ t, v k t := at_curve r L.val S.val
  rw [collect,hv]
  let R:= fun z : KeyIn G d × KeyIn G d => v z.1 z.2
  rw [show (∑ k,∑ t, v k t)=∑ z,R z from (Fintype.sum_prod_type R).symm, show (∑ a∈ wand L, ∑ b∈ wand S, view x hx i j L S r a b)=∑ z∈A,R z from (sum_product (wand L) (wand S) R).symm]
  rw [← sum_sdiff (subset_univ A)]
  have he (z : KeyIn G d × KeyIn G d) (h : z ∈ u) : r*‖R z‖ ≤ B z * D := by
    have hz : ¬ (z.1.val.1=L.val.degree ∧ z.2.val.1=S.val.degree) := by simpa [A,u,wand] using h
    unfold R v view; rw [norm_mul,norm_mul]
    let a := z.1
    let b := z.2
    let c := ‖((currentX hx G d).cov (i,a) (j,b)).re‖
    let H (x : Hub G d 0) (i : KeyIn G d) := ‖amount r x.val*gesture x.val (arbor d r i)‖
    have hh : r*(H L a*H S b)≤X L a*X S b := by
      by_cases he : a.val.1=L.val.degree
      · rw [mul_left_comm]; exact mul_le_mul (towering _ hr a) (skyward _ hr b (fun h => hz ⟨he,h⟩)) (mul_nonneg (zero_le_one.trans hr) (norm_nonneg _)) (norm_nonneg _)
      rw [← mul_assoc]; exact mul_le_mul (skyward _ hr _ he) (towering _ hr _) (norm_nonneg _) (norm_nonneg _)
    change r*(c*(H L a*H S b))≤_
    rw [mul_left_comm,mul_comm c]; apply mul_le_mul hh _ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)); simpa [c, Real.norm_eq_abs] using hX a b
  simp only [add_sub_cancel_right]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (zero_le_one.trans hr)).trans
  rw [mul_sum,sum_mul]; exact sum_le_sum he
end
end YM.Next.Rank.Prayer
