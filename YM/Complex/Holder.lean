import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Matrix.Order



/-!
# Trace estimates for finite interpolation

Verify the finite-quadrature proposal around : prove finite-dimensional
trace estimate without Schatten infinite approximation, so matrix inequality also
applies at any sign complex time. Uses L2 OPERATOR norm on *the matrices here*,
not the Frobenius norm used on gauge matrices. Prove abstract three lines trace
interpolation engine. No SVD/Poisson citation needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Holder
open MeasureTheory Filter Function Set Complex Matrix
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.L2Operator
open Complex.HadamardThreeLines
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
abbrev M (ι : Type*) := Matrix ι ι ℂ

/-- Multiplicative inputs within the strip. -/
structure Flex (ι : Type*) [DecidableEq ι] [Fintype ι] where
  walk : ℂ → M ι
  smooth : Differentiable ℂ walk
  ball (t) : t.re ∈ Icc (0:ℝ) 1 → ‖walk t‖ ≤ 1
  border (t) : t.re=1 → ∀ C : M ι, ‖C‖ ≤ 1 → ‖(walk t*C).trace‖ ≤ 1

def combine {n} (a : Fin n → M ι) := (List.ofFn a).prod

lemma blank (v : Fin 0 → M ι) : combine v=1 := by simp [combine]
lemma stem {n} (v : Fin (n+1) → M ι) : combine v = v 0 * combine (Fin.tail v) := by
  simp [combine,List.ofFn_succ]; rfl

lemma contract_mul {X Y : M ι} (h : ‖X‖ ≤ 1) (H : ‖Y‖ ≤ 1) : ‖X*Y‖ ≤ 1 :=
  (Matrix.l2_opNorm_mul X Y).trans <| mul_le_one₀ h (norm_nonneg Y) H

lemma contract_one : ‖(1 : M ι)‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def,map_one]
  exact ContinuousLinearMap.norm_id_le

theorem contract_prod {n} (F : Fin n → M ι) (h : ∀ i, ‖F i‖ ≤ 1) : ‖combine F‖ ≤ 1 := by
  induction n with
  | zero => rw [blank]; exact contract_one
  | succ n ih => rw [stem]; apply contract_mul (h 0) (ih _ (fun i => h i.succ))

lemma traceL : ∃ C : ℝ, ∀ A : M ι, ‖A‖ ≤ 1 → ‖A.trace‖ ≤ C := by
  let T : M ι →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  exact ⟨‖T‖,fun x h => (T.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg _) h)⟩
omit [DecidableEq ι] in
@[fun_prop] lemma dtrace : Differentiable ℂ (Matrix.trace (n := ι) (R := ℂ)) :=
  (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap.differentiable

lemma dproduct {n} (a : ℂ → Fin n → M ι) (h : ∀ i, Differentiable ℂ (fun x => a x i)) :
    Differentiable ℂ (fun x => combine (a x)) := by
  induction n with
  | zero => simp only [blank]; exact differentiable_const _
  | succ n ih =>
    simp only [stem]
    apply (h 0).mul (ih _ (fun i => h i.succ))

private def toward (r : ℝ) (η t : ℂ) := ((((η.re/(1-r):ℝ):ℂ))*(1-t))+↑η.im*I

private lemma actual {r : ℝ} {η t : ℂ} (_ : r<1) : (toward r η t).re= (η.re/(1-r))*(1-t.re) := by simp [toward,-Complex.ofReal_div]

private lemma advance {r : ℝ} (h : r<1) (η : ℂ) : toward r η r=η := by
  apply Complex.ext
  · rw [actual h,ofReal_re,div_mul_cancel₀ _ (by linarith)]
  simp [toward,-Complex.ofReal_div]

private theorem holder_core {n : ℕ} : ∀ (c : M ι) (v : Fin n → Flex ι)
    (z : Fin n → ℂ), ‖c‖ ≤ 1 → (∀ i, (z i).re ∈ Icc 0 1) → ∑ i, (z i).re=1 →
    ‖(c*combine (fun i => (v i).walk (z i))).trace‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro c v z hc hz h
    let t := (z 0).re
    let q := v 0
    let w := Fin.tail v
    let y := Fin.tail z
    let Y (r : Fin n → ℂ) := combine (fun i => (w i).walk (r i))
    rw [stem]; change ‖(c*(q.walk (z 0)*Y y)).trace‖ ≤ _
    rcases lt_or_eq_of_le (show t≤1 from (hz 0).2) with hh|ht
    · let g (x : ℂ) := q.walk (x+↑(z 0).im*I)
      let b (x : ℂ) (i : Fin n) := toward t (z i.succ) x
      let E (x : ℂ) := (c*(g x*Y (b x))).trace
      have hf : Differentiable ℂ E := by
        unfold E
        have hV : Differentiable ℂ (fun x => Y (b x)) := dproduct (fun x i => (w i).walk (b x i)) (fun i =>
          (w i).smooth.comp (show Differentiable ℂ (fun x => b x i) from by unfold b toward; fun_prop))
        have hU := q.smooth.comp (show Differentiable ℂ (fun (x : ℂ) => x+↑(z 0).im*I) from by fun_prop)
        have hr := (differentiable_const c).mul (hU.mul hV)
        exact (dtrace (ι := ι)).comp hr
      have hs : ∑ i : Fin n, (z i.succ).re = 1-t := by
        rw [Fin.sum_univ_succ] at h; unfold t; linarith
      have hx (i : Fin n) : (z i.succ).re ≤ 1-t := hs ▸ Finset.single_le_sum (fun i _ => (hz i.succ).1) (Finset.mem_univ i)
      have hm (x : ℂ) (hr : x.re ∈ Icc 0 1) (i : Fin n) : (b x i).re ∈ Icc 0 1 := by
        unfold b; rw [actual hh]
        have hH := div_nonneg (show 0 ≤ (z i.succ).re from (hz i.succ).1) (sub_nonneg.mpr hh.le)
        have hT : 0 ≤ 1-x.re := sub_nonneg.mpr hr.2
        exact ⟨mul_nonneg hH hT,mul_le_one₀ ((div_le_one (sub_pos.mpr hh)).mpr (hx i)) hT (sub_le_self _ hr.1)⟩
      have hg (x : ℂ) (hr : x.re ∈ Icc 0 1) : ‖g x‖ ≤ 1 := q.ball _ (by simpa using hr)
      have hG (x : ℂ) (hr : x.re ∈ Icc 0 1) : ‖Y (b x)‖ ≤ 1 := contract_prod _ fun i => (w i).ball _ (hm x hr i)
      obtain ⟨D,hD⟩ := traceL (ι := ι)
      have hB : BddAbove ((norm ∘ E) '' verticalClosedStrip 0 1) := ⟨D,by rintro _ ⟨x,hx,rfl⟩; exact hD _ (contract_mul hc (contract_mul (hg x hx) (hG x hx)))⟩
      have h0 (x : ℂ) (hr : x ∈ Complex.re ⁻¹' {0}) : ‖E x‖ ≤ 1 := by
        change x.re=0 at hr
        have hy : x.re ∈ Icc 0 1 := by rw [hr]; simp
        unfold E; rw [← mul_assoc]
        apply ih (c*g x) w (b x) (contract_mul hc (hg x hy)) (hm x hy)
        simp only [b, actual hh,hr,sub_zero,mul_one, ← Finset.sum_div, hs,div_self (sub_pos.mpr hh).ne']
      have h1 (x : ℂ) (hr : x ∈ Complex.re ⁻¹' {1}) : ‖E x‖ ≤ 1 := by
        change x.re=1 at hr
        unfold E; rw [Matrix.trace_mul_comm, mul_assoc]; unfold g
        exact q.border _ (by simp [hr]) _ (contract_mul (hG x (by simp [hr])) hc)
      have hav := norm_le_interp_of_mem_verticalClosedStrip₀₁' E (z := (t:ℂ)) (by
        show ((t:ℂ)).re ∈ Icc 0 1; exact ⟨(hz 0).1,hh.le⟩) hf.diffContOnCl hB h0 h1
      rw [show E (t:ℂ)=(c*(q.walk (z 0)*Y y)).trace by
        simp only [E,g,t,re_add_im]
        rw [show b ((z 0).re:ℂ) = y from funext fun i => advance hh (z i.succ)]] at hav
      simpa only [Real.one_rpow, mul_one] using hav
    rw [Matrix.trace_mul_comm, mul_assoc]
    exact q.border _ ht _ (contract_mul (contract_prod _ (fun i => (v i.succ).ball _ (hz i.succ))) hc)

def family (W : List (Flex ι × ℂ)) := (W.map (fun p => p.1.walk p.2)).prod

theorem convexStrip {n : ℕ} (V : Fin n → Flex ι) (h : Fin n → ℂ) (hm : ∀ i, (h i).re∈Icc 0 1)
    (ht : ∑ i, (h i).re=1) : ‖(combine (fun i => (V i).walk (h i))).trace‖ ≤ 1 := by
  simpa only [one_mul] using holder_core (1:M ι) V h contract_one hm ht

end YM.Holder
