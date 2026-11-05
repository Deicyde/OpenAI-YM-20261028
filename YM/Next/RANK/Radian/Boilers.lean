import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import YM.Next.RANK.Bird
import YM.Next.RANK.Tuning

/-! Analytic flat symbol point hulls. IBP via scale without dyadic iteration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric  Lattice  Finset
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace
local notation "𝑒" => Real.exp
variable {n : ℕ} {F G : E4→ℂ} {U : Set E4} {C c r M : ℝ}

lemma stove (U : Set E4) (h : IsOpen U) (H : ContDiffOn ℝ (↑n) F U) (hf : ContDiffOn ℝ (↑n) G U) (x : E4) (ht : x ∈ U) :
    ‖iteratedFDeriv ℝ n (F*G) x‖ ≤ ∑ i∈Finset.range (n+1),(n.choose i:ℝ)* ‖iteratedFDeriv ℝ i F x‖* ‖iteratedFDeriv ℝ (n-i) G x‖:= by
  have hp {f : E4→ℂ} (Hf : ContDiffOn ℝ (↑n) f U) (k : ℕ) (hb : k≤n):iteratedFDeriv ℝ k f x=iteratedFDerivWithin ℝ k f U x:=
    (iteratedFDerivWithin_eq_iteratedFDeriv h.uniqueDiffOn (((Hf x ht).contDiffAt (h.mem_nhds ht)).of_le (by exact_mod_cast hb)) ht).symm
  refine le_trans (b:=‖iteratedFDerivWithin ℝ n (fun x=>F x*G x) U x‖) (congr_arg norm (hp (H.mul hf) _ (le_refl _))|>.le) ((norm_iteratedFDerivWithin_mul_le H hf h.uniqueDiffOn ht le_rfl).trans (le_of_eq ?_))
  exact sum_congr rfl fun i hi=> by rw [hp H i (Nat.le_of_lt_succ (mem_range.mp hi)),hp hf (n-i) (Nat.sub_le ..)]
-- positive chord on any scale

def crown : ContDiffBump (0:E4):= ⟨1/2,1,by norm_num,by norm_num⟩
def basin (r : ℝ) (x : E4) : ℂ:= crown (r⁻¹ • x)
def sail (r : ℝ): E4 → ℂ:= 1 - basin r
lemma stalls (h : 0 < r) {x} (hx : ‖x‖ ≤ r/2) : basin r x=1:= by
  unfold basin; rw [crown.one_of_mem_closedBall]; simp
  rw [mem_closedBall_iff_norm,sub_zero,norm_smul,norm_inv,Real.norm_of_nonneg h.le, ← div_eq_inv_mul,div_le_iff₀ h];change _ ≤ (1/2)*r; linarith only [hx]
lemma fades_out (h : 0 < r) {x} (hx : r ≤ ‖x‖): basin r x=0:= by
  unfold basin; rw [crown.zero_of_le_dist]; simp
  rw [dist_zero_right,norm_smul,norm_inv,Real.norm_of_nonneg h.le,← div_eq_inv_mul,le_div_iff₀ h];change 1*r≤_;rw [one_mul];exact hx
lemma hue r (x) : ‖basin r x‖≤1:= by unfold basin;rw [Complex.norm_real, Real.norm_of_nonneg crown.nonneg]; exact crown.le_one
lemma unbasin r : ContDiff ℝ ∞ (basin r) := (Complex.ofRealCLM.contDiff (n:=∞)).comp (crown.contDiff.comp ((contDiff_id (𝕜:=ℝ)).const_smul (r⁻¹:ℝ)))
lemma away_sail r : ContDiff ℝ ∞ (sail r) := contDiff_const.sub (unbasin r)

lemma crown_cost (D : ℕ) : ∃ L : ℝ, 1≤L ∧ ∀ i≤D,∀ r : ℝ,0<r→∀ x, ‖iteratedFDeriv ℝ i (sail r) x‖ ≤ L / r^i:= by
  let f:E4→ℂ:= fun x=> 1-(crown x:ℂ)
  choose b h₁ using fun i : Fin (D+1) => own i.val
  let p i:=max 1 (b i); refine ⟨(∑ i,p i),le_trans (le_max_left _ (b 0)) (single_le_sum (fun i _=>(show 0 ≤ p i from by unfold p; exact zero_le_one.trans (le_max_left ..))) (mem_univ 0)),fun i hi r ht x =>?_⟩
  let s:=r⁻¹ • ContinuousLinearMap.id ℝ E4; let v:Fin (D+1):=⟨i,by omega⟩
  have hf:sail r=f ∘ s:=funext fun i=>rfl
  have hs : ‖s‖=r⁻¹:= by rw [show s= _ from rfl]; unfold s; rw [norm_smul];simp [Real.norm_of_nonneg ht.le]
  have hp : ContDiff ℝ i f:= contDiff_const.sub ((Complex.ofRealCLM.contDiff).comp (show ContDiff ℝ i _ from crown.contDiff (n:=(↑i:ℕ∞))))
  rw [hf,ContinuousLinearMap.iteratedFDeriv_comp_right s hp _ le_rfl];refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ?_
  simp_rw [hs]; simp only [prod_const, card_univ, Fintype.card_fin]; rw [inv_pow, ← div_eq_mul_inv]; apply div_le_div_of_nonneg_right _ (pow_nonneg ht.le _)
  exact (h₁ v (s x)).trans ((le_max_right ..).trans (single_le_sum (f:=p) (fun i _=> zero_le_one.trans (le_max_left ..)) (mem_univ v)))
where
 own (i : ℕ) : ∃ C : ℝ, ∀ x : E4, ‖iteratedFDeriv ℝ i (fun x=> (1:ℂ)-(crown x:ℂ)) x‖ ≤ C:= by
  by_cases hx:i=0
  · subst i; refine ⟨2,fun x=>?_⟩; rw [norm_iteratedFDeriv_zero]; apply (norm_sub_le ..).trans; rw [norm_one,Complex.norm_real,Real.norm_of_nonneg crown.nonneg]; linarith only [crown.le_one (x:=x)]
  let f:E4→ℂ:=fun x=> (crown x:ℂ);have hf:HasCompactSupport f:= by
    apply crown.hasCompactSupport.mono; intro x h; apply Function.mem_support.mpr; intro hz; apply h; simp only [f,hz,Complex.ofReal_zero]
  have he : ContDiff ℝ (↑i) f:= Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ (↑i) _ from crown.contDiff (n:=(↑i:ℕ∞)))
  obtain ⟨C,hC⟩:= (hf.iteratedFDeriv (𝕜:=ℝ) i).exists_bound_of_continuous (he.continuous_iteratedFDeriv le_rfl); refine ⟨C,fun x=>?_⟩
  change ‖iteratedFDeriv ℝ i ((fun _=> (1:ℂ)) - f) x‖ ≤ _; rw [iteratedFDeriv_sub_apply (show ContDiffAt ℝ (↑i) _ _ from contDiffAt_const) (he.contDiffAt), iteratedFDeriv_const_of_ne hx, Pi.zero_apply,zero_sub,norm_neg]; apply hC x
end YM.Next.Rank.Radian
