import YM.PertExtension.Normalized

/-! Nonnegative Taylor and Laurent powers, no power-log equivalence hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace YM.PertExtension.Series.Tested
open Filter Set Metric MeasureTheory
open scoped ContDiff Topology BigOperators Classical
local notation "smallScale" => Tested.germ

variable {R : Type*} {k j : ℕ}
section General
variable [NormedAddCommGroup R][NormedSpace ℝ R] {f g : ℝ→R}{a : ℕ→R}
lemma bill_const (c : R) : Bill 0 fun _=>c := ⟨‖c‖,norm_nonneg _,by apply Eventually.of_forall; simp⟩
lemma bill_sum {I:Type*}(s : Finset I) (f : I→ℝ→R)(h : ∀ i∈s, Bill k (f i)) : Bill k (∑ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty=> exact ⟨0,le_rfl,Eventually.of_forall (by simp)⟩
  | insert i s hi ih=>rw [Finset.sum_insert hi];exact bill_add (h _ (Finset.mem_insert_self ..)) (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
namespace Aspiration
variable (ha : Aspiration f a)
include ha
lemma bounded : Bill 0 f  := by
                                obtain ⟨C,hC,h⟩:=ha 0; refine ⟨C+‖a 0‖,by positivity,?_⟩
                                filter_upwards [h,eventually_small (t:=1) one_pos] with t ht hp
                                obtain ht:=show ‖f t-a 0‖≤C*t by simpa [peval,Zone.eval] using ht
                                simp only [pow_zero,mul_one];exact (le_of_eq (congr_arg _ (sub_add_cancel (f t) (a 0)).symm)).trans ((norm_add_le ..).trans (add_le_add (ht.trans (mul_le_of_le_one_right hC hp.2.le)) le_rfl))

lemma vanish {w}(hf : Bill w f)(h : k<w) : a k=0:=by
  induction k using Nat.strong_induction_on with
  | _ k ih=>
    obtain ⟨C,hC,hf⟩:=bill_ge hf (Nat.add_one_le_of_lt h)
    obtain ⟨D,hD,ha⟩:=ha k
    have he (t : ℝ) : peval a k t=t^k • a k:=by
      unfold peval Zone.eval; rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun j hj=>?_),zero_add]
      change t^j • a j=0;rw [ih j ..,smul_zero]<;>have hj:=Finset.mem_range.mp hj<;>omega
    simp_rw [Pi.sub_apply,he] at ha
    by_contra! hv
    let ε:=‖a k‖/(C+D+1)
    have hp : 0<ε := div_pos (norm_pos_iff.mpr hv) (by positivity)
    obtain ⟨t,hf,ha,ht,hε⟩:=(hf.and (ha.and (eventually_small hp))).exists
    have htq : ‖a k‖≤(C+D)*t := by
      apply le_of_mul_le_mul_left (a:=t^k) ?_ (pow_pos ht k)
      have h := add_le_add hf ha
      calc
         _ = ‖t^k • a k‖ := by rw [norm_smul, Real.norm_eq_abs,abs_of_pos (pow_pos ht _)]
         _ ≤ ‖f t‖ + ‖f t-t^k • a k‖ := le_trans (le_of_eq (show ‖_‖=‖f t-(f t-t^k • a k)‖ by congr 1;abel)) (norm_sub_le ..)
         _ ≤ _ := h.trans_eq (by rw [pow_succ];ring)
    have hε:=(lt_div_iff₀ (show 0<C+D+1 by positivity)).mp hε
    linarith

/-- Laurent shift after a genuine vanishing statement; no division of the
remainder by a negative power without simultaneously increasing the order. -/
lemma shift {w} (hv : ∀ i,w>i → a i=0) : Aspiration (fun (t:ℝ)=>(t⁻¹)^w • f t) (fun j=>a (w+j)) := by
  intro k; obtain ⟨C,hC,h⟩:=ha (w+k)
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_pos] with t h hp
  have ht : peval a (w+k) t = t^w • peval (fun i => a (w+i)) k t := by
    have he : ∑ i∈Finset.range w,t^i • a i=0:=Finset.sum_eq_zero (fun i hi=> by change t^i • a i=0; rw [hv i (Finset.mem_range.mp hi),smul_zero])
    simp only [peval,Zone.eval,add_assoc w k 1]; rw [Finset.sum_range_add _ w (k+1),he,zero_add,Finset.smul_sum]
    apply Finset.sum_congr rfl fun i _ => by simp [pow_add,smul_smul]
  change ‖((t⁻¹)^w • f t)-_‖≤_
  rw [show ((t⁻¹)^w • f t)-_=(t⁻¹)^w • (f t-peval a (w+k) t) by rw [ht,smul_sub,smul_smul,←mul_pow,inv_mul_cancel₀ hp.ne',one_pow,one_smul],norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  grw [show ‖f t - peval a (w+k) t‖ ≤ _ from h]; rw [pow_add t, pow_add t, inv_pow]; field_simp; simp [pow_add, mul_assoc]

end Aspiration
end General
section Field
variable [NormedRing R][NormedAlgebra ℝ R] {f g : ℝ→R}
lemma bill_mul (hf : Bill k f)(hg : Bill j g) : Bill (k+j) fun t=> f t * g t := by
  obtain ⟨C,hC,hf⟩:=hf;obtain ⟨D,hD,hg⟩:=hg;refine ⟨C*D,mul_nonneg hC hD,?_⟩
  filter_upwards [hf,hg,eventually_pos] with t hf hg ht
  exact (norm_mul_le ..).trans <| (mul_le_mul hf hg (norm_nonneg _) (by positivity)).trans_eq <| by rw [pow_add];ring
lemma bill_pow (hf : Bill k f)(m : ℕ) : Bill (m*k) (f^m) := by induction m with
  | zero=> simp;exact bill_const ..
  | succ m ih=> simpa only [Nat.add_mul,Nat.one_mul, Nat.pow_succ, Pi.pow_apply, pow_succ] using! bill_mul ih hf
end Field
section CommRing
variable [NormedCommRing R][NormedAlgebra ℝ R]
lemma bill_product {I :Type*}(s : Finset I)(k : I→ℕ)(f : I→ℝ→R)(h : ∀ i∈s, Bill (k i) (f i)) : Bill (∑ i∈s,k i) (∏ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty=>simp;exact bill_const ..
  | insert i s hi ih=> rw [Finset.prod_insert hi,Finset.sum_insert hi]; exact bill_mul (h i (Finset.mem_insert_self ..)) (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
end CommRing

section Jet
open Radial
variable {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
def RadialOrder (n : ℕ)(f : E→R)[NormedAddCommGroup R]:Prop:= ∀ u,Bill n (fun t : ℝ=>f (t • u))
theorem directions {f : E→ℝ}(hf : ContDiffAt ℝ ∞ f 0)(u : E): Aspiration (fun t : ℝ=>f (t • u)) (fun j=>jet f j u) := by
  intro n; obtain ⟨δ,C,hδ,hC,h⟩:= deposition f n hf
  refine ⟨C*‖u‖^(n+1),by positivity,?_⟩
  filter_upwards [eventually_small (show 0<δ/(‖u‖+1) from div_pos hδ (by have := norm_nonneg u; linarith))] with t ht
  have hu := (lt_div_iff₀ (show 0<‖u‖+1 by have := norm_nonneg u; linarith)).mp ht.2
  exact h u t ht.1 (by linarith [ht.1])
lemma zero_first {f : E→ℝ}(hf : ContDiffAt ℝ ∞ f 0)(h0 : f 0 = 0): RadialOrder 1 f := by
  intro u; convert directions hf u 0 using 1
  funext x;simp [peval,Zone.eval,h0]
lemma jets_vanish {f : E→ℝ}(hf : ContDiffAt ℝ ∞ f 0)(h : RadialOrder j f){k}(hk : k<j) : jet f k=0 := funext fun x=>(directions hf x).vanish (h x) hk
end Jet

end YM.PertExtension.Series.Tested
