import YM.Pert.Fourier.Band
import Mathlib.Analysis.Calculus.MeanValue
/-! Higher finite difference cost; repeated use in momentum summation by parts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open Function Filter Set Topology Metric
open scoped ContDiff
section
variable {E Y : Type*} [NormedAddCommGroup E] [NormedAddCommGroup Y]
-- Normed groups abelian for cancellation
def punch (e : E) (n : ℕ) (f : E → Y) : E → Y :=
    n.rec f fun _ g x => g (x+e) - g x
lemma punch_zero (n : ℕ) (e : E) : ∀ x, punch e n (0 : E→Y) x=0 := by
  unfold punch; induction n with | zero => exact fun _ => rfl | succ n ih => intro x; dsimp; rw [ih,ih,sub_self]
end
section
universe u v
variable {E : Type u} {Y : Type v} [NormedAddCommGroup E] [NormedAddCommGroup Y] [NormedSpace ℝ E] [NormedSpace ℝ Y]

def nob (X : Set E) (x e : E) (n : ℕ) := x∈X ∧ ∀ j<n, x+j • e+e∈X
lemma nob_in {X : Set E} {x e : E} {n : ℕ} (h : nob X x e n) {i : ℕ} (hi : i≤n) : nob X x e i := ⟨h.1,fun j hj => h.2 j (lt_of_lt_of_le hj hi)⟩
lemma nob_step {X : Set E} {x e : E} {n : ℕ} (h : nob X x e (n+1)) : nob X (x+e) e n := ⟨by simpa using! h.2 0 (by omega),fun j hj => by
  rw [show x+e+j • e = x+(j+1) • e by rw [add_comm j 1,add_nsmul,one_nsmul,add_assoc]]; exact h.2 _ (by omega)⟩
def Smooth (n : ℕ) {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (X : Set E) (f : E→Y) : Prop := ∀ x∈X, ContDiffAt ℝ n f x
-- Parametric iterates of the derivative, so that mean value never has an improper segment.
lemma puncture (n : ℕ) (S : Set E) (hS : Convex ℝ S) : ∀ {Y : Type (max u v)} [i₁ : NormedAddCommGroup Y] [i₂ : NormedSpace ℝ Y] (x e : E) (C : ℝ) (f : E → Y), nob S x e n → Smooth n S f → (∀ x∈S, ‖iteratedFDeriv ℝ n f x‖ ≤ C) → ‖punch e n f x‖ ≤ ‖e‖^n * C := by
  induction n with
  | zero => intro Y i j x e C f h _ hC; simpa only [norm_iteratedFDeriv_zero,punch,pow_zero,one_mul] using! hC x h.1
  | succ n ih =>
    intro Y _h _h2 x e C f h hw hv
    have hx := h.1; have he := h.2 0 (by omega); rw [zero_smul,add_zero] at he
    have hP (x) (hx : nob S x e n) : ‖punch e n (fderiv ℝ f) x‖ ≤ ‖e‖^n*C := ih x e C (fderiv ℝ f) hx (fun z hz => ?_) (fun z hz => ?_)
    rotate_left
    · apply (hw z hz).fderiv_right; norm_cast
    · rw [norm_iteratedFDeriv_fderiv]; apply hv z hz
    have hder {i : ℕ} : ∀ (_ : i≤n) (z : E) (_ : nob S z e i), HasFDerivAt (punch e i f) (punch e i (fderiv ℝ f) z) z := by
      induction i with
      | zero => intro hi z hz; exact (hw _ hz.1 |>.differentiableAt (by norm_cast)).hasFDerivAt
      | succ i I =>
        intro hii z hz
        let q : E → E := fun t => t+e
        have w : HasFDerivAt q (ContinuousLinearMap.id ℝ E) z := (hasFDerivAt_id _).add_const e
        have e1 := I (by omega) (z+e) (nob_step hz)
        have e2 := I (by omega) z (nob_in hz (by omega))
        simpa using! (e1.comp z w).sub e2
    let X := {z : E | nob S z e n}
    have hcon : Convex ℝ X := by
      intro z hz w hw a b ha hb hab
      have add (p : E) (hp : z+p∈S) (hv : w+p∈S) : a • z + b • w + p ∈ S := by rw [show a • z + b • w + p = a • (z+p) + b • (w+p) by rw [smul_add,smul_add,add_add_add_comm,← add_smul,hab,one_smul]]; exact hS hp hv ha hb hab
      exact ⟨by simpa using add 0 (by simpa using hz.1) (by simpa using hw.1),fun j hj => by rw [add_assoc]; exact add _ (by rw [← add_assoc]; exact hz.2 j hj) (by rw [← add_assoc]; exact hw.2 j hj)⟩
    have hb (z) (hz : z∈X) := hder (i:=n) (by omega) z hz
    have H := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=punch e n f) (s:=X) (fun z hz => (hb z hz).differentiableAt) (fun z hz => by rw [(hb z hz).fderiv]; exact hP z hz) hcon (x:=x) (y:=(x+e)) (nob_in h (by omega)) (nob_step h)
    rw [add_sub_cancel_left] at H; rw [pow_succ, mul_right_comm _ ‖e‖ C]; exact H

end
end YM.Pert.Band
