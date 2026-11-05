import Mathlib.Analysis.Calculus.TaylorIntegral
import YM.Push.FINITE_DETECTION.Harmonic
import YM.Work.B06


/-! Leading coefficient and translations of real symmetric homogeneous tensors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Kelvin
open Tensor Analysis Function Set Filter ContinuousMultilinearMap
open scoped Topology BigOperators ContDiff
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {x : E4}
    {s : E4 → ℝ} {g : E4 → E4} {j l : ℕ}

def dressed (Y : T E4 F j) (s : E4 → ℝ) (g : E4 → E4) := fun y => s y • Tensor.diagonal Y (g y)

def multiplier (s : E4 → ℝ) (g : E4 → E4) (v : E4) (i : Axis) := fun y => s y * (D v g y) i
lemma dressed_smooth (Y : T E4 F j) (hs : smoothAt s x) (hg : smoothAt g x) :
    smoothAt (dressed Y s g) x := hs.smul ((diag_smooth Y ∞).contDiffAt.comp x hg)
lemma multiplier_smooth (v i) (hs : smoothAt s x) (hg : smoothAt g x) : smoothAt (multiplier s g v i) x :=
  hs.mul ((Maxwell.compAxis i).contDiff.contDiffAt.comp x (dSmooth hg v (by simp)))

lemma term_rate (Y : T E4 F (j+1)) (hY : Sym Y) (hs : smoothAt s x) (hg : smoothAt g x) (v : E4) :
    D v (dressed Y s g) =ᶠ[𝓝 x]
      ((j+1 : ℝ) • ∑ i : Axis, dressed (Y.curryLeft (basis i)) (multiplier s g v i) g) + dressed Y (D v s) g := by
  filter_upwards [(hs.of_le (allOrders 1)).eventually (by simp), (hg.of_le (allOrders 1)).eventually (by simp)] with y hy hz
  have hs := hy.differentiableAt (by simp)
  have hg := hz.differentiableAt (by simp)
  have h := ((diag_smooth Y ∞).differentiable (by simp)).differentiableAt (x := g y)
  change fderiv ℝ (fun t => s t • (Tensor.diagonal Y ∘ g) t) y v = _
  rw [fderiv_fun_smul hs (h.comp y hg), fderiv_comp y h hg, add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    differential_diagonal _ hY, ContinuousLinearMap.smulRight_apply]
  change s y • ((j+1) • (Y.curryLeft (D v g y)) (fun _ => g y)) + D v s y • Tensor.diagonal Y (g y) = _
  rw [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_add,Nat.cast_one,smul_comm (s y)]
  simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply,dressed,multiplier,Tensor.diagonal]
  congr 2
  conv_lhs => arg 2; arg 1; arg 2; rw [← space_expand (D v g y)]
  rw [_root_.map_sum,sum_apply,Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul,smul_apply,mul_smul]

lemma term_step (Y : T E4 F (j+1)) (hY : Sym Y) (hs : smoothAt s x) (hg : smoothAt g x) (v : E4) (u : Fin l → E4) :
    coeff (dressed Y s g) (l+1) x (Fin.cons v u) = ((l:ℝ)+1)⁻¹ •
      (((j+1 : ℝ) • ∑ i : Axis, coeff (dressed (Y.curryLeft (basis i)) (multiplier s g v i) g) l x u) +
      coeff (dressed Y (D v s) g) l x u) := by
  let f (i : Axis) := dressed (Y.curryLeft (basis i)) (multiplier s g v i) g
  have hF (i) := show smoothAt (f i) x from dressed_smooth _ (multiplier_smooth _ _ hs hg) hg
  have hsum : smoothAt (∑ i : Axis, f i) x := by simp_rw [smoothAt, Finset.sum_fn]; exact ContDiffAt.sum (fun i _ => hF i)
  rw [coeff_apply_cons ((dressed_smooth Y hs hg).of_le (allOrders _)), GermCoeff l (term_rate Y hY hs hg v)]
  change ((↑(l+1 : ℕ) : ℝ))⁻¹ • coeff (((j+1 : ℝ) • ∑ i : Axis, f i) + dressed Y (D v s) g) l x u = _
  rw [coeff_add (f := ((j+1:ℝ) • ∑ i : Axis, f i)) (hsum.const_smul (j+1 : ℝ) |>.of_le (allOrders _))
    ((dressed_smooth Y (dSmooth hs _ (by simp)) hg).of_le (allOrders _)), coeff_smul _ (hsum.of_le (allOrders _)),
    coeff_sum _ _ _ _ (fun i _ => (hF i).of_le (allOrders _))]
  simp only [add_apply, smul_apply,sum_apply,Nat.cast_add,Nat.cast_one]; rfl

lemma lower_term (Y : T E4 F j) (hY : Sym Y) (hs : smoothAt s x) (hg : smoothAt g x) (hx : g x = 0) {l : ℕ} (hl : l < j) :
    coeff (dressed Y s g) l x = 0 := by
  ext1 u
  induction l generalizing s j with
  | zero => rw [coeff_apply_zero]; simp [dressed, Tensor.diagonal,hx,Y.map_coord_zero (m := fun _ => 0) (⟨0,hl⟩ : Fin j) (rfl : (0 : E4) = 0)]
  | succ l ih =>
    cases j with
    | zero => omega
    | succ j =>
      rw [← Fin.cons_self_tail u,term_step Y hY hs hg]
      simp [ih Y hY (dSmooth hs _ (by simp)) (by omega : l<j+1) (Fin.tail u),
        show ∀ i, coeff (dressed (Y.curryLeft (basis i)) (multiplier s g (u 0) i) g) l x (Fin.tail u) = 0 from
          fun i => ih _ (freeze_sym Y hY _) (multiplier_smooth _ _ hs hg) (by omega) _]

lemma head_term (Y : T E4 F j) (hY : Sym Y) (hs : smoothAt s x) (hg : smoothAt g x) (hx : g x = 0) (u : Fin j → E4) :
    coeff (dressed Y s g) j x u = s x • Y (fderiv ℝ g x ∘ u) := by
  induction j generalizing s with
  | zero => rw [coeff_apply_zero]; exact congr_arg (fun v => s x • Y v) (Subsingleton.elim ..)
  | succ j ih =>
    conv_lhs => rw [← Fin.cons_self_tail u, term_step Y hY hs hg,lower_term Y hY (dSmooth hs _ (by simp)) hg hx (lt_add_one j)]
    simp_rw [ih _ (freeze_sym Y hY _) (multiplier_smooth _ _ hs hg)]
    rw [zero_apply,add_zero,smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
    rw [← Fin.cons_self_tail (fderiv ℝ g x ∘ u), ← curryLeft_apply]
    conv_rhs => rw [← space_expand ((fderiv ℝ g x ∘ u) 0),_root_.map_sum,sum_apply,Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul,smul_apply,multiplier,mul_smul]; rfl

lemma diag_response (Y : T E4 F j) (hY : Sym Y) (x : E4) : coeff (Tensor.diagonal Y) j x = Y := by
  induction j generalizing x with
  | zero => ext1 u; rw [coeff_apply_zero]; exact congr_arg Y (Subsingleton.elim ..)
  | succ j ih =>
    ext1 u; rw [← Fin.cons_self_tail u,coeff_apply_cons ((diag_smooth Y _).contDiffAt)]
    let Z := Y.curryLeft (u 0)
    have he : D (u 0) (Tensor.diagonal Y) = ((j:ℝ)+1) • Tensor.diagonal Z := funext fun y => by
      rw [D,differential_diagonal _ hY, ← Nat.cast_smul_eq_nsmul ℝ]; simp [Tensor.diagonal,Z]
    rw [he, coeff_smul _ ((diag_smooth _ _).contDiffAt),ih Z (freeze_sym _ hY _),smul_apply,smul_smul]
    push_cast; rw [inv_mul_cancel₀ (by positivity),one_smul,curryLeft_apply]

lemma diag_above (Y : T E4 F j) (hY : Sym Y) (x : E4) : iteratedFDeriv ℝ (j+1) (Tensor.diagonal Y) x = 0 := by
  have he : iteratedFDeriv ℝ j (Tensor.diagonal Y) = fun _ => (j.factorial : ℝ) • Y := funext fun z => by
    conv_rhs => rw [← diag_response Y hY z,coeff,smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
  simp [iteratedFDeriv_succ_eq_comp_left,he]; ext; rfl

lemma diag_translate [CompleteSpace F] (Y : T E4 F j) (hY : Sym Y) (x y : E4) :
    Tensor.diagonal Y (x+y) = ∑ i ∈ Finset.range (j+1), Tensor.diagonal (coeff (Tensor.diagonal Y) i x) y := by
  rw [map_add_eq_sum_add_integral_iteratedFDeriv (n := j) (fun _ _ => (diag_smooth Y _).contDiffAt)]
  simp [diag_above Y hY,Tensor.coeff,Tensor.diagonal]
end YM.Push.FiniteDetection.Kelvin
