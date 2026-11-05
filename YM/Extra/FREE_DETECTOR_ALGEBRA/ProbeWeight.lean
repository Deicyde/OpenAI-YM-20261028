import YM.Extra.FREE_DETECTOR_ALGEBRA.Average
import YM.Extra.FREE_DETECTOR_ALGEBRA.Quartz

set_option warningAsError false

/-! Fourth pole of `whole`, contributes Euler weights (not discarded as a
contact). Uses Wick factorial/combinatorial convention and normalization
in both tensor-dual legs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD.OPE
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels SphereTest Residue MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {G : Gauge} {j k n d : ℕ} {x y : E4}

local notation "W" => Sol G.Color

lemma twin_resolve (v : E4) (A B : W 0) :
    (∑ i : Fin (legDim G 0), gem (rCoeff (token 0 i)) (solAct (face v) A) * gem (solAct (face v) (frame G 0 i)) B) +
    (∑ i : Fin (legDim G 0), gem (solAct (face v) (frame G 0 i)) (solAct (face v) A) * gem (rCoeff (token 0 i)) B) =
    2*gem A B := by
  let P := solAct (face v) (F:=G.Color) (j:=0)
  have hu (A B : W 0) : gem (P A) (P B)=gem A B := carry_dot (face v) ..
  change (∑ i : Fin (legDim G 0), gem _ (P A) * gem _ B) + (∑ i : Fin (legDim G 0), gem (P _) (P A)*gem _ B)= _
  simp_rw [hu,fun i : Fin (legDim G 0) => reflected_gem v (frame G 0 i) B, mul_comm (gem (frame G 0 _) A)]
  rw [resolves,resolves]; rw [show gem (P A) (P B)=gem A B from hu A B, show gem B A=gem A B from dotF_symm B.val A.val]; ring

lemma cross_visits (S T : W j) : Average (fun v => gem (visit S v) (visit T v)) ((2^j*((j:ℝ)+1))⁻¹ * gem S T) := by
  unfold gem
  simp_rw [fun v => gem0 (visit S v) (visit T v),visit_eval,dotF_eval,Finset.mul_sum]
  exact Average.sum _ _ _ fun i _ => Average.sum _ _ _ fun b _ => avg_paths S T i b

def topTwin (P : W 0) (Q : W 0) (x y : E4) (a b : Slot G) (v : E4) : ℂ := residueSingle P Q v 4 x y a b + residueSingle Q P v 4 x y a b

def turnTwin (x y : E4) (a b : Slot G) (v : E4) : ℂ := ∑ i : Fin (legDim G 0), topTwin (rCoeff (token 0 i)) (solAct (face v) (frame G 0 i)) x y a b v

lemma twin_contract (a b : Slot G) (he : x≠y) (v : E4) (hv : v∈unitSet) : turnTwin x y a b v =
    (↑((flare a.1 * 2) * gem (visit (rCoeff a) v) (visit (aim (G:=G) (rCoeff b) a.1 (show y-x∈away from sub_ne_zero.mpr he.symm)) v)):ℂ) := by
  let A := visit (rCoeff a) v; let B := visit (aim (G:=G) (rCoeff b) a.1 (show y-x∈away from sub_ne_zero.mpr he.symm)) v
  have hs (P Q : W 0) : residueSingle P Q v 4 x y a b =
      (↑(flare a.1 * (gem P (solAct (face v) A) * gem Q B)):ℂ) := by
    rw [residueSingle,if_pos (show 4≤ rung 0 a by unfold rung; omega),show rung 0 a - 4=a.1 by unfold rung; omega, at_edge P a hv,gradePath Q b a.1 he v]; rw [← Complex.ofReal_mul,mul_assoc]
  unfold turnTwin topTwin; simp_rw [hs,← Complex.ofReal_add,← Complex.ofReal_sum]
  congr 1; simp_rw [← mul_add,← Finset.mul_sum,Finset.sum_add_distrib, twin_resolve v A B,← mul_assoc]; rfl

lemma turn_average (a b : Slot G) (he : x≠y) : Average (turnTwin x y a b) ((↑(8* normal):ℂ) * costKey a * ether (rCoeff a) b (x-y)) := by
  let A := rCoeff a; let B := aim (G:=G) (rCoeff b) a.1 (show y-x ∈ away from sub_ne_zero.mpr he.symm)
  have heq : ether (rCoeff a) b (x-y)=(↑(gem A B):ℂ) := ether_aim _ _ (sub_ne_zero.mpr he) (neg_sub ..).symm _
  rw [heq]
  let t := flare a.1 * 2
  have ht : Average (fun v => (↑(t*gem (visit A v) (visit B v)):ℂ)) ((↑(t*((2^a.1*((a.1:ℝ)+1))⁻¹ * gem A B)):ℂ)) :=
      ((cross_visits A B).vScale t).linear Complex.ofRealCLM
  suffices hs : t*(2^a.1*((a.1:ℝ)+1))⁻¹=8*normal*(costKey a:ℝ) by
    rw [← mul_assoc,hs] at ht
    push_cast at ht
    rw [Complex.ofReal_mul]; refine ht.test fun v hv => ?_
    rw [twin_contract a b he v hv]; unfold t; push_cast; rfl
  unfold t flare strength costKey; push_cast; set j := a.1
  rw [mul_right_comm _ normal, mul_assoc _ ((-2)^j), ← mul_pow,show (-2:ℝ) * -1=2 by norm_num]
  field_simp
  ring



def readPole (x : Points (n+1)) (Y : Fin (n+1) → WickPol G) (I : Fin (n+1) → Finset (Slot G)) (v : E4) :=
    ∑ a∈I 0, ∑ i : Fin n, ∑ b∈I i.succ, stageTwo x Y 0 a i.succ b * turnTwin (x 0) (x i.succ) a b v



-- Global weight derivation on local polynomials.
def weighing (G : Gauge) : Derivation ℂ (WickPol G) (WickPol G) := MvPolynomial.mkDerivation ℂ fun i => (costKey i:ℂ) • MvPolynomial.X i


lemma hinge (Y : WickPol G) (I : Finset (Slot G)) (hi : Y.vars ⊆ I) : weighing G Y= ∑ a ∈ I,(costKey a:ℂ) • (MvPolynomial.pderiv a Y * MvPolynomial.X a) := by
  classical
  let f (a : Slot G) : Derivation ℂ (WickPol G) (WickPol G) := (costKey a:ℂ) • (MvPolynomial.X a : WickPol G) • MvPolynomial.pderiv a
  have he : weighing G Y = (∑ a ∈ I, f a) Y := by
    apply sub_eq_zero.mp
    change (weighing G - ∑ a∈I, f a) Y = 0
    apply MvPolynomial.derivation_eq_zero_of_forall_mem_vars
    intro a h
    change weighing G (X a) - (∑ a∈I,f a) (X a) = _; rw [weighing,MvPolynomial.mkDerivation_X,deriv_apply_sum,Finset.sum_eq_single_of_mem a (hi h)]
    · change _ - (costKey a:ℂ) • ((X a : WickPol G)*MvPolynomial.pderiv a (X a))= _; simp
    intro b hb he; change (costKey b:ℂ) • ((X b : WickPol G) * pderiv b (X a))= _; simp [MvPolynomial.pderiv_X_of_ne he.symm]
  rw [he,deriv_apply_sum]; apply Finset.sum_congr rfl; intro a _; change (costKey a:ℂ) • ((MvPolynomial.X a : WickPol G) * (MvPolynomial.pderiv a Y)) = _; rw [mul_comm]

abbrev quantum : ℂ := (↑(8*normal):ℂ)
lemma stage_off (x : Points (n+1)) (Q : WickPol G) (Y : Fin n→ WickPol G) (a b : Slot G) (i : Fin n) :
    stageTwo x (Fin.cons Q Y) 0 a i.succ b = encounter x (update Y i (MvPolynomial.pderiv b (Y i))) (MvPolynomial.pderiv a Q) := by
  unfold stageTwo shorten; rw [encounter_vals,update_of_ne (Fin.succ_ne_zero i)]
  congr 1; ext1 j; refine Fin.cases ?_ (fun k => ?_) j
  · rw [update_of_ne (Fin.succ_ne_zero i).symm]; simp
  by_cases h:k=i <;> simp [h]

lemma avgC {f : E4→ℂ} {a : ℂ} (h : Average f a) (c : ℂ) : Average (fun x => c*f x) (c*a) := h.linear (ContinuousLinearMap.lsmul ℝ (E:=ℂ) ℂ c)

lemma read_average (Q : WickPol G) (x : Points (n+1)) (hx : x∈conf (n+1)) (Y : Fin n → WickPol G) (I : Fin (n+1) → Finset (Slot G))
    (hi : ∀ i,(Fin.cons (α:=fun _=> WickPol G) Q Y i).vars ⊆ I i) : Average (readPole x (Fin.cons Q Y) I) (quantum * encounter x Y (weighing G Q)) := by
  unfold readPole; rw [hinge Q (I 0) (hi 0),_root_.map_sum,Finset.mul_sum]
  apply Average.sum; intro a _; rw [← digit_coeff a,map_smul,slip (rCoeff a) x hx _ Y (Fin.tail I) (fun i => hi i.succ)]
  change Average _ (quantum *((costKey a:ℂ) * ∑ i : Fin n, ∑ k ∈ I i.succ, ether (rCoeff a) k _ * _))
  rw [Finset.mul_sum,Finset.mul_sum]; apply Average.sum; intro i _; rw [Finset.mul_sum, Finset.mul_sum]
  apply Average.sum; intro b _
  rw [← stage_off x Q Y a b i]
  let c := stageTwo x (Fin.cons Q Y) 0 a i.succ b; let k := ether (rCoeff a) b (x 0-x i.succ)
  change Average _ (quantum * ((costKey a:ℂ)*(k*c)))
  rw [show quantum*((costKey a:ℂ)*(k*c))= c*(quantum*(costKey a:ℂ)*k) by ring]
  exact avgC (turn_average a b ((show Injective x.ofLp from hx).ne (Fin.succ_ne_zero i).symm)) c

def listened (x : Points (n+1)) (Y : Fin (n+1) → WickPol G) := readPole x Y fun i => (Y i).vars



lemma pay (x : Points (n+1)) (hx : x∈conf (n+1)) (Y : Fin (n+1) → WickPol G) : Average (listened x Y) (quantum * moment G x (update Y 0 (weighing G (Y 0)))) := by
  suffices hh : ∀ (Q : WickPol G) (Y : Fin n→ WickPol G), Average (listened x (Fin.cons Q Y)) (quantum * moment G x (update (Fin.cons Q Y) 0 (weighing G Q))) by
    simpa using hh (Y 0) (Fin.tail Y)
  intro Q A
  rw [← replace_at, before_all,← encounter_vals]; exact read_average Q x hx A _ (fun _ => le_rfl)
end YM.Extra.FD.OPE
