import YM.Pert.Warp.Initial
import YM.Extra.FREE_DETECTOR_ALGEBRA.Removal
/-! Derivations deleting one linear leg of the Maxwell symbol. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
noncomputable section
namespace YM.Pert.Warp
open Align Maxwell Function MvPolynomial Extra.FD.Pair Wick
variable {G : Gauge} {r d : ℕ}

def coeffL (a : Labels.Key G) (i : Fin (legDim G a.1)) : ℝ := kTape a (frame G a.1 i)
def slotL (a : Labels.Key G) (i : Fin (legDim G a.1)) : Slot G := ⟨a.1,i⟩
lemma k_expand (a : Labels.Key G) : kTape a = ∑ i:Fin (legDim G a.1), coeffL a i • coordinateLeg (slotL a i) := by
  let f := kTape a
  apply LinearMap.ext; intro v
  conv_lhs=> rw [← (frame G a.1).sum_repr v]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]; erw [LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro i _; exact mul_comm ..
lemma readL (a : Labels.Key G) : reduceEq (MvPolynomial.X (R:=ℂ) a) = ∑ i:Fin (legDim G a.1), (coeffL a i: ℂ) • (MvPolynomial.X (slotL a i): WickPol G) := by
  unfold reduceEq coeffL slotL kTape; simp_rw [MvPolynomial.aeval_X,MvPolynomial.smul_eq_C_mul];rfl
lemma ker_expand (z : E4) (hz:z≠0) (a b:Labels.Key G) : legKernel (kTape a) (kTape b) z = ∑ i:Fin (legDim G a.1),∑ j:Fin (legDim G b.1), coeffL a i *(coeffL b j * legKernel (coordinateLeg (slotL a i)) (coordinateLeg (slotL b j)) z) := by
  let B := pairing (G:=G) (j:=a.1) (l:=b.1) hz
  conv_lhs=> change B _ _; rw [k_expand a,k_expand b]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]; rw [← Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)] -- wrong arg
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  exact (congrArg (fun U: Probe G b.1 →ₗ[ℝ] ℝ => U _) (B.map_smul (coeffL a i) (coordinateLeg (slotL a i)))).trans (congrArg ((coeffL a i)* ·) ((B (coordinateLeg (slotL a i))).map_smul ..))

def ladder (a : Labels.Key G) (x y : E4) : Derivation ℂ (WickPol G) (WickPol G) := ∑ i, (coeffL a i : ℂ) • extractVar (slotL a i) x y
lemma ladder_trace (a : Labels.Key G) (x y) (p): ladder a x y p = ∑ i, (coeffL a i : ℂ) • extractVar (slotL a i) x y p := by
  unfold ladder
  -- coeFnAddMonoidHom args? #check
  have := congrFun (map_sum (Derivation.coeFnAddMonoidHom : Derivation ℂ (WickPol G) (WickPol G) →+ (WickPol G→WickPol G)) (fun i => (coeffL a i:ℂ) • extractVar (slotL a i) x y) (Finset.univ:Finset (Fin (legDim G a.1)))) p
  rw [Finset.sum_apply] at this
  apply this.trans; apply Finset.sum_congr rfl; rintro i _; exact Derivation.smul_apply ..
lemma ladder_X (a b : Labels.Key G) {x y : E4} (h : x-y≠0): ladder a x y (reduceEq (MvPolynomial.X b)) = MvPolynomial.C (↑(legKernel (kTape a) (kTape b) (x-y))) := by
  let D := ladder a x y
  have e (i) : D ( (coeffL b i:ℂ) • (MvPolynomial.X (slotL b i) : WickPol G)) = (coeffL b i:ℂ) • ∑ j, (coeffL a j:ℂ) • C (entry (slotL a j) (slotL b i) x y) := by rw [D.map_smul]; change (coeffL b i:ℂ) • ladder a x y _ = _; rw [ladder_trace]; simp only [extractVar,MvPolynomial.mkDerivation_X]
  rw [readL, map_sum,ker_expand _ h]; change ∑ i, D ((coeffL b i:ℂ) • (X (slotL b i) : WickPol G)) = C ↑(∑ i, ∑ j, (coeffL a i)*(coeffL b j * legKernel _ _ _) : ℝ) -- explicit later
  push_cast; simp_rw [map_sum,map_mul,e,Finset.smul_sum,MvPolynomial.smul_eq_C_mul, mul_left_comm (C ((coeffL b _):ℂ))]
  exact Finset.sum_comm


def window (z : Points r) (a b : Labels.Key G) (i j : Fin r) := (↑(legKernel (kTape a) (kTape b) (z i-z j)) : ℂ)
lemma take_line (z : Points r) (hz:z∈conf r) (a : Labels.Key G) (i : Fin r) (W : Fin r→WickPol G) :
    replace z W i (W i * reduceEq (MvPolynomial.X a)) = ∑ k:Others i,replace z W k (ladder a (z i) (z k) (W k)) := by
  rw [readL,Finset.mul_sum,map_sum]
  simp only [mul_smul_comm,map_smul,remove z hz,ladder_trace, map_sum,Finset.smul_sum]
  exact Finset.sum_comm

lemma D_prod {Q : Type*} [CommRing Q] [Algebra ℂ Q] (D : Derivation ℂ Q Q) {κ : Type*} [DecidableEq κ] (s : Finset κ) (A : κ→Q) : D (∏ i∈s,A i)=∑i∈s,D (A i)* (∏ j∈s.erase i, A j) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty,Finset.sum_empty]; exact D.map_one_eq_zero
  | insert i s h ih =>
    simp_rw [Finset.prod_insert h, Derivation.leibniz,Finset.sum_insert h,Finset.erase_insert h,ih,smul_eq_mul,Finset.mul_sum]
    rw [add_comm,mul_comm _ (D (A i))]; congr 1
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.erase_insert_of_ne (show i ≠ k from fun hk' => h (hk'.symm ▸ hk)), Finset.prod_insert (fun he=>h (Finset.mem_of_mem_erase he))];ring
lemma D_kill (A : Labels.Key G) {κ : Type*} [DecidableEq κ] (s : Finset κ) (q : κ→Labels.Key G) (x y : E4) (hy : x-y≠0) :
    ladder A x y (reduceEq (∏j∈s,(MvPolynomial.X (q j) : Labels.Pol G))) = ∑i∈s, (legKernel (kTape A) (kTape (q i)) (x-y) : ℂ) • reduceEq (∏ j∈s.erase i, MvPolynomial.X (q j)) := by
  simp_rw [_root_.map_prod,D_prod,ladder_X A _ hy,MvPolynomial.smul_eq_C_mul]
end YM.Pert.Warp
