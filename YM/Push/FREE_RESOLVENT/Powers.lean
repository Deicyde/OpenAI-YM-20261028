import YM.Push.FREE_RESOLVENT.JetWindows

/-!
# Real all-order bounds on routed products for the inverse prices

Work with packet of bounded directions first; unhit real letter is
UNITARY (don't charge a Frobenius growth `dim^length`!). Summable even for
arbitrarily small assigned positive exponential rate. Provide op norms for
use with infinite-length path sums but don't infer a size before proving the
ℓ² color factor at evaluation.

Aux regularization in next module will allow using this Global
jet lemma even when bounds only needed near zero.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid  TestD Filter Function Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f c : Side} {S : StepData c f} {k : ℕ} {σ V A : ℝ}

section multiline
variable {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H] [NormedSpace ℝ E] [NormedSpace ℝ H]

lemma slot_op {X : E [×k]→L[ℝ] H} {M : ℝ} (hm : 0 ≤ M) (h : ∀ v : Fin k → E, (∀ i, ‖v i‖ ≤ 1) → ‖X v‖ ≤ M) :
    ‖X‖ ≤ M := by
  apply ContinuousMultilinearMap.opNorm_le_bound hm; intro m
  let v : Fin k → E := fun i => ‖m i‖⁻¹ • m i
  have he (i) : m i = ‖m i‖ • v i := by
    by_cases hx : m i=0
    · simp [hx,v]
    unfold v; rw [smul_inv_smul₀]; exact (norm_pos_iff.mpr hx).ne'
  have hv : ‖X v‖ ≤ M := h v (fun i => by
    by_cases hx : m i=0
    · simp [v,hx]
    unfold v; rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ ((norm_pos_iff.mpr hx).ne')])
  nth_rw 1 [funext he]
  rw [X.map_smul_univ, norm_smul,Real.norm_of_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_left hv (Finset.prod_nonneg fun _ _ => norm_nonneg _)).trans_eq (mul_comm _ _)

/-- Express full op test by packets of *labels*. Use every actual occurrence. -/
lemma list_op {F : E → H} {B : ℝ} {x} (hB : 0 ≤ B) (h : ∀ l : List (Fin k), ∀ v : Fin k → E,
    l.length=k → (∀ i, ‖v i‖ ≤ 1) → ‖jet v F l x‖ ≤ B) : ‖iteratedFDeriv ℝ k F x‖ ≤ B := by
  apply slot_op hB; intro v hv
  have hs := h (List.finRange k) v List.length_finRange hv
  suffices he : jet v F (List.finRange k) x=iteratedFDeriv ℝ k F x v from he ▸ hs
  have he : ∀ (n m : ℕ) (u : Fin n → E) (h : Fin m → E) (hh : n=m),
      (∀ i, h i=u (Fin.cast hh.symm i)) → iteratedFDeriv ℝ n F x u=iteratedFDeriv ℝ m F x h := by
    rintro n _ u h rfl ha; rw [show h = u from funext ha]
  unfold jet; symm
  exact he _ _ _ _ List.length_finRange.symm (fun i => by simp)

end multiline

section travel
variable {τ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def patchMoney (G : Gauge) (k : ℕ) (σ A : ℝ) (j : ℕ) := ‖(1 : G.Mat)‖*(1+(2^k*A)/(Real.exp σ-1))^j
lemma patch_nn (G : Gauge) (k : ℕ) {σ A : ℝ} (h : 0 < σ) (ha : 0 ≤ A) (j : ℕ) : 0 ≤ patchMoney G k σ A j := by
  have hh := sub_pos.mpr ((Real.one_lt_exp_iff).mpr h)
  unfold patchMoney; positivity
lemma patch_le (h : 0 < σ) (ha : 0 ≤ A) : Monotone (patchMoney G k σ A) := by
  have hh : 1 ≤ 1+(2^k*A)/(Real.exp σ-1) := le_add_of_nonneg_right (div_nonneg (by positivity)
    (sub_nonneg.mpr ((Real.one_lt_exp_iff).mpr h).le))
  intro i j h; unfold patchMoney; gcongr

variable {U : E → Config G f}
lemma travel_cd (hf : ∀ (b : Step) (x : Site f), ContDiff ℝ k (fun y => G.mat (b.read (U y) x))) (w : Walk) (x : Site f) :
    ContDiff ℝ k (fun y => G.mat (travel (U y) x w)) := by
  induction w generalizing x with
  | nil => exact contDiff_const
  | cons b w ih => simp_rw [travel,G.mat_mul]; exact (hf b x).mul (ih _)

lemma assembled_jets {t : τ → E} {p : E} (hf : ∀ (b : Step) (x : Site f), ContDiff ℝ k (fun y => G.mat (b.read (U y) x)))
    (ha : 0 ≤ A) (hs : 0 < σ) (ht : ∀ (b : Step) (x : Site f) (l : List τ), l.length ≤ k →
      ‖jet t (fun y => G.mat (b.read (U y) x)) l p‖ ≤ A) (w : Walk) (x : Site f) (l : List τ) (he : l.length ≤ k) :
    ‖jet t (fun y => G.mat (travel (U y) x w)) l p‖ ≤ patchMoney G k σ A l.length * Real.exp (σ*w.length) := by
  induction w generalizing l x with
  | nil =>
    cases l
    · rw [zeroth]; simp [travel,patchMoney]
    rename_i i l
    rw [show (fun y => G.mat (travel (U y) x [])) = fun _ => 1 by ext; simp [travel], jet_const t _ (List.cons_ne_nil i l), norm_zero]
    exact mul_nonneg (patch_nn G k hs ha _) (Real.exp_pos _).le
  | cons b w ih =>
    let F := fun y => G.mat (b.read (U y) x)
    let H := fun y => G.mat (travel (U y) (x+b.vec) w)
    let r := pureR l
    let N (m : Masks l) : G.Mat := jet t F (lo l m) p * jet t H (hi l m) p
    let R := Real.exp (σ*w.length)
    let P : ℕ → ℝ := patchMoney G k σ A
    have hP n : 0 ≤ P n := patch_nn G k hs ha n
    have hr : 0 ≤ R := (Real.exp_pos _).le
    have hh (m : Masks l) : ‖jet t H (hi l m) p‖ ≤ P (hi l m).length * R := ih _ _ ((len_high ..).trans he)
    have hm : ‖N r‖ ≤ P l.length*R := by
      unfold N; rw [show lo l r=[] from lo_right _, zeroth]
      rw [Gauge.mul_frob_eq (F p) _ (G.mat_star_mul _)]
      refine (hh _).trans_eq ?_; unfold r; rw [hi_right]
    have hq : jet t (fun y => G.mat (travel (U y) x (b::w))) l p = ∑ m, N m := by
      simp_rw [travel, G.mat_mul]
      exact leibniz t (ContinuousLinearMap.mul ℝ G.Mat) l (smooth_of_le (hf b x).contDiffAt he)
        (smooth_of_le (travel_cd hf w (x+b.vec)).contDiffAt he)
    rw [hq]; cases hl : l.length with
    | zero =>
      obtain rfl : l=[] := List.length_eq_zero_iff.mp hl
      refine (le_of_eq (show ‖∑ m, N m‖=‖N r‖ from ?_)).trans (hm.trans ?_)
      · congr 1; change ∑ m : Unit, N m=N (); simp
      simp only [List.length_nil,List.length_cons]
      exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ w.length) hs.le)) (hP _)
    | succ j =>
      have hb (m : Masks l) (h : m ∈ Finset.univ.erase r) : ‖N m‖ ≤ A*(P j*R) := by
        have hi := lo_ne (show m ≠ pureR l from Finset.ne_of_mem_erase h)
        have hl : (hi' : True) → (TestD.hi l m).length ≤ j := fun _ => by have := lengths l m; have := List.length_pos_iff.mpr hi; omega
        unfold N
        exact (norm_mul_le ..).trans (mul_le_mul (ht b x (lo l m) ((len_low ..).trans he))
          ((hh m).trans (mul_le_mul_of_nonneg_right (patch_le hs ha (hl trivial)) hr)) (norm_nonneg _) ha)
      let C := (2:ℝ)^k * A
      have hv : (∑ i ∈ Finset.univ.erase r, ‖N i‖) ≤ (2:ℝ)^k * (A*(P j*R)) := by
        refine (Finset.sum_le_sum (fun i h => hb i h)).trans ?_
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hw : ↑(Finset.univ.erase r).card ≤ ((2:ℝ)^k) := by
          exact_mod_cast ((Finset.card_le_univ _).trans ((card l).le.trans (pow_le_pow_right₀ (by norm_num) he)))
        exact mul_le_mul_of_nonneg_right hw (mul_nonneg ha (mul_nonneg (hP _) hr))
      have hM : C*P j ≤ P (j+1)*(Real.exp σ - 1) := by
        have hC : 0 ≤ C := mul_nonneg (by positivity) ha
        have hw : 0 < Real.exp σ-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hs)
        rw [show P (j+1)=P j*(1+C/(Real.exp σ-1)) by unfold C P patchMoney; rw [pow_succ]; ring]
        calc
          _ = (P j*(C/(Real.exp σ-1)))*(Real.exp σ-1) := by field_simp
          _ ≤ _ := by gcongr; exacts [hP j, le_add_of_nonneg_left zero_le_one]
      rw [hl] at hm
      change _ ≤ P (j+1) * Real.exp _
      refine (norm_sum_le _ _).trans ?_
      rw [← Finset.add_sum_erase (s:=Finset.univ) (fun m => ‖N m‖) (Finset.mem_univ r)]
      apply (add_le_add hm hv).trans
      rw [List.length_cons, Nat.cast_add_one,mul_add, Real.exp_add,mul_one]
      have hp := mul_le_mul_of_nonneg_right hM hr
      dsimp only [C,R] at *; linarith
end travel
end YM.FreeResolvent.Affine
