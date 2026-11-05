import YM.PertExtension.Exponent
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
noncomputable section
namespace YM.PertExtension.Series.Radial
open Filter Set Metric MeasureTheory Asymptotics
open scoped BigOperators Topology Real ContDiff Classical
open Zone
variable {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]

lemma bounded_exp {c:ℝ}(hc : 0<c)(k : ℕ) : ∃ C,0≤C ∧ ∀ x : ℝ, 0≤ x → (1+x)^k * Real.exp (-c*x^2)≤ C := by
  have ht := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hc (↑k)).bound zero_lt_one
  obtain ⟨M,hM⟩:=eventually_atTop.1 ht
  let D:= max 1 M
  have h₁ : 1≤D := le_max_left ..
  have h₂ : M≤D:= le_max_right ..
  refine ⟨(1+D)^k+2^k,by have hL : 0≤D:=zero_le_one.trans h₁; positivity,fun x hx=>?_⟩
  by_cases h : x ≤ D
  · calc
      _ ≤ (1+D)^k * Real.exp 0 := by gcongr; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _)
      _ ≤ _ := by rw [Real.exp_zero,mul_one]; exact le_add_of_nonneg_right (by positivity)
  have hmx : M≤x:=h₂.trans (not_le.mp h).le; have hx1 := h₁.trans (not_le.mp h).le
  have he:= hM x hmx
  have hx' := pow_nonneg hx k
  simp only [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx' (Real.exp_pos _).le), abs_of_nonneg (Real.exp_pos _).le,one_mul] at he
  have hxt : 1+x ≤ 2*x:=by linarith
  calc
     _ ≤ 2^k*(x^k*Real.exp (-c*x^2)) := by rw [← mul_assoc,← mul_pow];gcongr
     _ ≤ 2^k*1 := by gcongr;exact he.trans <| Real.exp_le_one_iff.mpr (by nlinarith)
     _ ≤ _ := by have hL : 0≤D:=zero_le_one.trans h₁; simp;positivity

local notation "Z" => Radial.zone (E:=E)

def bill (k : ℕ)(c : ℝ) (u : E) := (Z).w u ^ k * Real.exp (-c*‖u‖^2)
lemma bill_nonneg (k : ℕ)(c : ℝ)(u : E) : 0≤bill k c u:= by have: 0≤(Z).w u:=zero_le_one.trans ((Z).high u); unfold bill; positivity
variable [MeasurableSpace E][BorelSpace E]
theorem bill_integrable (μ : Measure E)[μ.HasTemperateGrowth] (k : ℕ){c : ℝ}(hc : 0<c) : Integrable (bill (E:=E) k c) μ:= by
  obtain ⟨n,hn⟩:=Measure.HasTemperateGrowth.exists_integrable (μ:=μ)
  obtain ⟨C,hC,h⟩:=bounded_exp hc (k+n)
  refine (hn.const_mul C).mono' ?_ (Eventually.of_forall fun u=>?_)
  · apply Continuous.aestronglyMeasurable; unfold bill Radial.zone;dsimp only;fun_prop
  have hp: 0<(1+‖u‖):=by have:= norm_nonneg u;linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (bill_nonneg ..)]; change (1+‖u‖)^k * Real.exp (-c*‖u‖^2) ≤ _
  rw [Real.rpow_neg (by positivity),Real.rpow_natCast]; refine le_of_mul_le_mul_right (a:=(1+‖u‖)^n) ?_ (pow_pos hp _)
  have ht := h ‖u‖ (norm_nonneg _); calc
    _ = (1+‖u‖)^(k+n) * Real.exp (-c*‖u‖^2) := by rw [pow_add];ring
    _ ≤ C:=ht
    _ ≤ _ := by field_simp;exact le_rfl

def normTerm (K f : E→ℝ)(k : ℕ)(u : E) := integrandSeries f K k u*kernel f u

namespace Smooth
omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma continuousJet (K : E→ℝ)(j : ℕ) : Continuous (jet K j):= by
  unfold jet; apply continuous_const.mul
  exact Continuous.comp (iteratedFDeriv ℝ j K 0).cont (continuous_pi fun _=>continuous_id)

lemma continuousCoeff (K f : E→ℝ)(j : ℕ) : Continuous (integrandSeries f K j):= by
  unfold integrandSeries Zone.mul
  apply continuous_finsetSum; intro i hi; apply (continuousJet K _).mul; apply continuous_finsetSum;intro k hk
  have h (k : ℕ) : ∀ j, Continuous (TaylorPow (layers f) k j):=by
    induction k with
    | zero=> intro h;simp only [TaylorPow];split<;>exact continuous_const
    | succ k ih=>
      intro j; simp only [TaylorPow, Zone.mul]; apply continuous_finsetSum;intro i _
      refine (ih i.1).mul <| (continuousJet ..).neg.add ?_
      by_cases hi : i.2=0
      · simpa [hi] using! continuousJet f 2
      simpa [hi] using! (continuous_const (X:=E) (y:= (0:ℝ)))
  exact continuous_const.mul (h ..)

lemma continuousTerms (K f : E→ℝ)(j : ℕ) : Continuous (normTerm K f j):=(continuousCoeff ..).mul (Real.continuous_exp.comp (continuous_neg.comp (continuousJet ..)))
end Smooth

variable (μ : Measure E)[μ.HasTemperateGrowth]
variable {K : E→ℝ}{f : E→ℝ}
local notation "Term" => normTerm K f

def moment (K f : E→ℝ)(k : ℕ) := ∫ u, normTerm K f k u ∂μ
def poly (K f : E→ℝ) (n : ℕ)(t : ℝ)(u : E) := eval (integrandSeries f K) n t u * kernel f u

theorem kernel_pos {u} : 0<kernel f u:= by unfold kernel; exact Real.exp_pos _
theorem kernel_bound {u c r}(h : (c+r)*‖u‖^2 ≤ jet f 2 u) : shade r u*(kernel f u) ≤ Real.exp (-c*‖u‖^2) := by
  rw [shade,kernel,← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith

lemma boundedPrice {u : E→ℝ} (hu : (Z).Invoice u) {c : ℝ} (hf : ∀ u : E,c*‖u‖^2 ≤ jet f 2 u) : ∃ C k, 0≤C ∧ ∀ x,‖u x * kernel f x‖ ≤ C*bill k c x := by
  obtain ⟨C,k,hC,h⟩:=hu
  refine ⟨C,k,hC,fun x=>?_⟩
  unfold bill; rw [norm_mul,Real.norm_eq_abs (kernel ..),abs_of_nonneg kernel_pos.le,←mul_assoc]
  exact mul_le_mul (h _) (Real.exp_le_exp.mpr (by specialize hf x;linarith)) kernel_pos.le (by have h := (Z).high x; positivity)

namespace Stationary
variable (F : Stationary f)(hf : ContDiffAt ℝ ∞ K 0)
include μ
include F hf
local notation "poly'" => poly K f
local notation "moment'" => moment μ K f

protected theorem integrableTerm {k : ℕ} (H : ∃ c>0,∀ u : E,c*‖u‖^2≤jet f 2 u) : Integrable (Term k) μ := by
  obtain ⟨c,hc,h⟩:=H
  obtain ⟨C,j,hj,hb⟩:= boundedPrice ((integrand hf F hc).invoice k) (f:=f) h
  exact ((bill_integrable μ j hc).const_mul C).mono' (Smooth.continuousTerms .. |>.aestronglyMeasurable) (Eventually.of_forall hb)

protected lemma integral_eval (H : ∃ c>0,∀ u : E,c*‖u‖^2≤jet f 2 u)(n : ℕ)(t : ℝ) : ∫ u,poly' n t u ∂μ = ∑ i∈Finset.range (n+1), t^i*moment' i := by
  let S:= Finset.range (n+1)
  have he : poly' n t=∑ i∈S, (fun u=>t^i*Term i u) := by funext u; unfold poly Zone.eval normTerm;rw [Finset.sum_mul];simp [Finset.sum_apply, mul_assoc,S]
  rw [he]; unfold moment
  simp_rw [Finset.sum_apply,integral_finsetSum _ (fun i _=>(F.integrableTerm μ hf H).const_mul (t^i)),integral_const_mul]
  rfl

omit μ in
protected lemma coeffBound (n : ℕ) : ∃ C e,0≤C ∧ ∀ u (t:ℝ),0≤t → t≤1 →
    ‖eval (integrandSeries f K) n t u‖≤ C*(Z).w u^e := by
  let a:= fun i u=>‖integrandSeries f K i u‖
  obtain ⟨C,e,hC,h⟩:=Invoice.fin_sum (Finset.range (n+1)) a (fun i _=> (integrand hf F (show (0:ℝ)<1 from by positivity)).invoice i |>.norm)
  refine ⟨C,e,hC,fun u t ht hh=>le_trans (b:=∑ i∈Finset.range (n+1), a i u) ?_ (by simpa only [Finset.sum_apply,Real.norm_eq_abs,abs_of_nonneg (show 0≤∑ i∈Finset.range (n+1), a i u from by apply Finset.sum_nonneg;intro i hi; apply norm_nonneg)] using h u)⟩
  refine le_trans (norm_sum_le ..) <| Finset.sum_le_sum fun i _=>?_
  rw [norm_smul,Real.norm_eq_abs (t^i),abs_of_nonneg (pow_nonneg ht _)]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht hh)

end Stationary
end YM.PertExtension.Series.Radial
