import YM.RG08.Skiff.Spoke
import YM.RG08.Skiff.Pave

/-! # Exact scalar specialization

All ranks, no divisions by factorial except the ones in the algorithms.
At any T (`Fintype` not needed for these identities, at zero output rank
uses also both TSUM scopes, so never use for **bulk** extensive terms without a cover disclaimer.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Skiff
open Forms Jetty Steam Function Finset
open scoped Topology BigOperators ENNReal Classical ContDiff
variable {I:Type}{n p q l:ℕ}{Γ:Forms.Line I}
def during (f:Pearl)(P:Pack n I):Flake n I:=fun x=>P x f
lemma stageH (f:Pearl)(P:Pack n I): during f (breeze P)=bleach (during f P):=by
 unfold during bleach breeze
 ext x;rw [Pi.smul_apply,Pi.smul_apply,Pi.smul_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply];rfl
lemma clocked (f:Pearl)(P:Pack (n+2) I):during f (pocket Γ P)=lap Γ (during f P):=by
 unfold pocket lap;rw [stageH];apply congrArg bleach; ext x; unfold run during decker nut; simp only [Pi.smul_apply,smul_eq_mul]; simp_rw [lam,mul_comm (P _ f)]
lemma reel_stamp (f:Pearl)(P:Pack (p+1) I)(V:Flake (q+1) I):during f (cloak Γ P V)=bridge Γ (during f P) V:=by
 rw [cloak,stageH,bridge];apply congrArg bleach; unfold weld during decker sleeve seam;ext x; simp_rw [Pi.smul_apply,smul_eq_mul,mul_assoc (P _ f),mul_comm (P _ f)]
-- bill result through all positive heat coefficients (d_e,n strict feed, vacuum unchanged). Fixed time compile.
lemma registry (l e n:ℕ) :∃ P:ℝ→ℝ, Wage P ∧ ∀{I:Type}(A:Ground I)(L:Loom I){σ:ℝ}(h:0<σ)(d:ℕ)(δ W U:ℝ)
    (V V':Steam.Grain I)(Γ Γ':Forms.Line I)(F F':GrainS I), fits L A→Eligible V→Eligible V'→WireCot A σ δ W Γ Γ'→0≤δ→1≤W→0≤U→
 (∀ a r,taps 0 e 0 a r→Cot A σ δ W (V a r) (V' a r))→(∀ a r,across 1 e n a r→Dyad L d h U δ (F a r) (F' a r))→
 ∀{t:ℝ},|t|≤ W→Dyad L d h (P W*U) δ (shaker l Γ V F t e n) (shaker l Γ' V' F' t e n):=by
 choose P hP HP using fun j=>journey (j+1) e n
 let H(j:ℕ)(x:ℝ):=x^(j+1)*P j x
 have ht(j:ℕ):Wage fun (x:ℝ)=>x^(j+1):=⟨1,j+1,by linarith,fun x hx=>⟨by dsimp only;exact pow_nonneg (zero_le_one.trans hx) _,by simp⟩⟩
 refine ⟨fun x=>∑ i∈range (l+3*e),H i x,Wage.sum _ _ (fun j _=> (ht j).mul (hP j)),?_⟩
 intro I A L σ h d δ W U V V' Γ Γ' F F' hp he he' hg hδ hW hU hv hf t hw
 rw [Finset.sum_mul]; refine Dyad.sum _ (fun i _=>?_ ) hδ
 have hV:Dyad _ _ _ _ _ _ _:= HP i A L h d δ W U V V' Γ Γ' F F' hp he he' hg hδ hW hU hv (fun a r hs=> hf a r (by unfold across at *;omega))
 refine (hV.smul (t^(i+1))).mono ?_; rw [abs_pow]; unfold H; rw [mul_assoc];gcongr; exact mul_nonneg ((hP i).nn hW) hU
end YM.RG08.Skiff
