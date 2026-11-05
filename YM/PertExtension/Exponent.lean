import YM.PertExtension.Uniform
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! All estimates here are on finite-dimensional cutoffs; no uniform-in-cutoff assertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.PertExtension.Series.Radial
open Filter Set Metric
open scoped BigOperators Topology ContDiff Classical
open Zone
variable {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
protected abbrev invoice : Zone E:=Radial.zone


def kernel (f : E→ℝ) := fun u=>Real.exp (-jet f 2 u)
def higher (f : E→ℝ) (t :ℝ)(u) := -f (t • u) / t^2 + jet f 2 u
def layers (f : E→ℝ)(k : ℕ)(u:E) : ℝ:= -jet f (k+2) u+(if k=0 then jet f 2 u else 0)
def shade (c:ℝ) : E→ℝ:=fun u=>Real.exp (c*‖u‖^2)

structure Stationary (f : E→ℝ) : Prop where
  smooth : ContDiffAt ℝ ∞ f 0
  base0 : f 0=0
  base1 (u : E) : jet f 1 u=0

namespace Stationary
variable {f : E→ℝ} (F : Stationary f)
include F
protected theorem cancellation (u : E)(n)(t:ℝ)(ht : 0<t) :
  (higher f t u - eval (layers f) n t u)*t^2 = -(f (t • u) - eval (jet f) (n+2) t u) := by
   have hne:t≠0:=ht.ne'
   suffices h : eval (jet f) (n+2) t u=t^2*jet f 2 u - (eval (layers f) n t u)*t^2 by rw [h];unfold higher;field_simp;ring
   unfold Zone.eval layers; simp only [smul_eq_mul]
   rw [Finset.sum_range_succ' _ (n+2)]
   rw [Finset.sum_range_succ' _ (n+1)]
   have hh : (∑ i∈Finset.range (n+1), t^i * (-jet f (i+2) u + if i=0 then jet f 2 u else 0)) = -(∑ i∈Finset.range (n+1),t^i * jet f (i+2) u) + jet f 2 u := by
    simp [mul_add, Finset.sum_add_distrib, Finset.sum_neg_distrib]
   have he : (∑ i∈Finset.range (n+1),t^(i+1+1)*jet f (i+1+1) u)=(∑ i∈Finset.range (n+1),t^i * jet f (i+2) u)*t^2:=by
     rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _=>?_
     rw [show i+1+1=i+2 from rfl, pow_add];ring
   rw [hh,he]; rw [jet_zero,F.base1,F.base0];ring

protected theorem expansion : (Radial.zone (E:=E)).Built 1 (higher f) (layers f) := by
  have H : ∀ i, (Radial.zone (E:=E)).Invoice (layers f i) := fun i => (jetInvoice f (i+2) |>.weaken (b:=fun x=>-jet f (i+2) x) (by simp)).add <|
     ⟨by by_cases h:i=0
         · simpa [h] using! (jetInvoice f 2).exists_bound
         simpa [h] using! (Invoice.const (Z:=Radial.zone) (0:ℝ)).exists_bound⟩
  refine ⟨H,fun k=>⟨fun _=>le_rfl,?_⟩⟩
  obtain ⟨δ,C,hδ,hC,hd⟩:= deposition f (k+2) F.smooth
  refine ⟨δ,C,k+3,hδ,hC,fun u t ht hm=>?_⟩
  have he : ‖u‖ ≤ (Radial.zone (E:=E)).w u:= by simp [Radial.zone]
  have h := hd u t ht <| (mul_le_mul_of_nonneg_left he ht.le).trans hm
  calc
     _ ≤ C*‖u‖^(k+2+1)*t^(k+1) := (le_of_mul_le_mul_right ?_ (pow_pos ht 2))
     _ ≤ _ := by simp only [Pi.one_apply,mul_one];gcongr
  rw [← show ‖t^2‖=t^2 from by rw [Real.norm_eq_abs,abs_of_pos (pow_pos ht _)], ← norm_mul, Pi.sub_apply,Pi.sub_apply,F.cancellation u k t ht,norm_neg]; rw [Real.norm_eq_abs (t^2),abs_of_pos (pow_pos ht _)]; exact h.trans_eq (by rw [show k+2+1=k+1+2 from by omega, pow_add t];ring)

omit F in
@[simp] lemma layers_zero (u : E) : layers f 0 u=0:=by unfold layers; exact neg_add_cancel _

protected theorem dominated {c : ℝ} (hc : 0 < c) : ∃ δ C : ℝ,0<δ ∧ 0≤C ∧ ∀ u (t:ℝ),
  0<t → t*‖u‖ ≤ δ → ‖higher f t u‖ ≤ C*‖u‖^3*t ∧ ‖higher f t u‖ ≤ c*‖u‖^2 := by
  obtain ⟨δ,C,hδ,hC,h⟩:= deposition f 2 F.smooth
  refine ⟨min δ (c/(C+1)),C,lt_min hδ (by positivity),hC,fun u t ht hm=>?_⟩
  have hd:=h u t ht (hm.trans (min_le_left ..))
  have he:=F.cancellation u 0 t ht; simp only [Zone.eval, zero_add,layers_zero,Finset.sum_range_one,smul_zero,sub_zero] at he
  have h' : ‖higher f t u‖≤C*‖u‖^3*t := (le_of_mul_le_mul_right ?_ (pow_pos ht 2))
  · constructor;exact h'
    calc
     _ ≤ ‖u‖^2 * (C+1)*(t*‖u‖) := h'.trans (by nlinarith only [show 0≤t*‖u‖^3 by positivity])
     _ ≤ c*‖u‖^2 := by have hr := hm.trans (min_le_right ..); grw [hr];field_simp; exact le_rfl
  calc
    _ = ‖higher f t u*t^2‖ := by rw [norm_mul,Real.norm_eq_abs (t^2),abs_of_pos (pow_pos ht _)]
    _ ≤ _ := by rw [he,norm_neg]; exact hd.trans_eq (by norm_num;ring)

end Stationary

private lemma exp_series_error (x : ℝ)(j : ℕ) : ‖Real.exp x - ∑ i∈Finset.range (j+1),(i.factorial:ℝ)⁻¹*x^i‖ ≤ ‖x‖^(j+1) * Real.exp ‖x‖ := by
  let g : ℝ → ℝ := fun t=> Real.exp (x*t)
  have hsm : ContDiff ℝ ∞ g := (Real.contDiff_exp).comp (contDiff_const.mul contDiff_id)
  have hy (i : ℕ)(t)(ht : t∈Icc (0:ℝ) 1) : iteratedDerivWithin i g (Icc 0 1) t=x^i*Real.exp (x*t):=by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) ((hsm.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt) ht]; unfold g; rw [iteratedDeriv_exp_const_mul]
  have hh : ContDiffOn ℝ ((j:WithTop ℕ∞)+1) g (Icc 0 1):=by rw [← Nat.cast_one (R:=WithTop ℕ∞),←Nat.cast_add];exact hsm.of_le (by exact WithTop.coe_le_coe.mpr le_top)|>.contDiffOn
  have h := taylor_mean_remainder_bound (n:=j) (x:=1) (C:=‖x‖^(j+1) * Real.exp ‖x‖) (a:=0) (b:=1) zero_le_one hh (right_mem_Icc.mpr zero_le_one) ?_; swap
  · intro y hy'; obtain ⟨hd,hu⟩:=hy'
    rw [hy _ _ ⟨hd,hu⟩,norm_mul,norm_pow,Real.norm_eq_abs (Real.exp ..), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (show x*y≤‖x‖ by rw [Real.norm_eq_abs];rcases abs_cases x with ⟨eq,_⟩|⟨eq,_⟩ <;> rw [eq] <;> nlinarith)) (by positivity)
  have e : taylorWithinEval g j (Icc 0 1) 0 1 = ∑ i∈Finset.range (j+1),(i.factorial:ℝ)⁻¹*x^i := by
    rw [taylor_within_apply]; apply Finset.sum_congr rfl fun i _ => ?_
    rw [hy _ _ (left_mem_Icc.mpr zero_le_one)];simp
  rw [e] at h; dsimp [g] at h; rw [mul_one,sub_zero,one_pow,mul_one] at h
  exact h.trans <| div_le_self (by positivity) (by exact_mod_cast j.factorial_pos)

def expsum (a : ℕ → E → ℝ)(k j : ℕ)(u : E) := ∑ i∈ Finset.range (k+1),(i.factorial:ℝ)⁻¹ * TaylorPow a i j u
lemma expsum_limit {a : ℕ → E → ℝ}(hf : a 0 = 0) {j k : ℕ} (hj : j≤k) : expsum a j j = expsum a k j := by
  have h (i)(u : E) : ∀ j < i, TaylorPow a i j u=0:=by
    induction i with
    | zero=> simp
    | succ i ih=>
      intro j hj
      simp only [TaylorPow, Zone.mul];apply Finset.sum_eq_zero
      intro v hv; have hv:=Finset.mem_antidiagonal.mp hv
      obtain hj|hj:=eq_zero_or_pos v.2
      · rw [hj,hf];simp
      rw [ih _ (by omega),zero_mul]
  funext u; unfold expsum
  exact Finset.sum_subset (((by simp [Finset.range_subset];omega) : Finset.range (j+1) ⊆ Finset.range (k+1))) fun i hi ha=> by simp only [Finset.mem_range,not_lt] at ha; simp [h i u j ha]

def scaled {V X : Type*}[NormedAddCommGroup V][NormedSpace ℝ V](c : ℝ) (a : X → V) := c • a

lemma scaled_build {X : Type*}{Z : Zone X}{a : ℕ→X→ℝ}{f : ℝ→X→ℝ}{V : X→ℝ}(h : Built Z V f a)(c : ℝ) : Built Z V (fun t x=>c*f t x) (fun k x=>c*a k x) := by
  let g : X→ℝ:=fun _=>c
  have hb := (Invoice.const (Z:=Z) c)
  refine ⟨fun j=> hb.mul (h.invoice j),fun j=>?_⟩
  refine (h.fits j).shift_a (h.fits j).envelope ⟨1,‖c‖,0,zero_lt_one,norm_nonneg _,fun x t _ _=>⟨?_,le_rfl⟩⟩
  dsimp only [Pi.sub_apply]; unfold Zone.eval
  simp only [smul_eq_mul];rw [show ∑ i∈Finset.range (j+1), t^i*(c*a i x) = c*∑ i∈Finset.range (j+1),t^i*a i x by simp only [Finset.mul_sum];apply Finset.sum_congr rfl; intro; intro;ring,←mul_sub,norm_mul]; simp

private lemma step_bound {f : E→ℝ}(F : Stationary f){c}{j : ℕ}(hc : 0<c) : (Radial.zone (E:=E)).Fits (shade c) (j+1)
      (fun t u => Real.exp (higher f t u) - ∑ i∈Finset.range (j+1),(i.factorial:ℝ)⁻¹ * (higher f t u)^i):= by
  have hn (u : E) : (1:ℝ)≤shade c u:= by unfold shade; apply Real.one_le_exp;positivity
  obtain ⟨δ,C,hδ,hC,h⟩:=F.dominated hc
  refine ⟨hn,δ,C^(j+1),3*(j+1),hδ,pow_nonneg hC _,fun u t ht hm=>?_⟩
  have hw : ‖u‖ ≤ (Radial.zone (E:=E)).w u := by simp [Radial.zone]
  obtain ⟨h₁,h₂⟩:=h u t ht ((mul_le_mul_of_nonneg_left hw ht.le).trans hm)
  have e:=exp_series_error (higher f t u) j
  calc
    _ ≤ (C*‖u‖^3*t)^(j+1) * shade c u := e.trans (mul_le_mul (by gcongr) (Real.exp_le_exp.mpr h₂) (Real.exp_pos _).le (by positivity))
    _ ≤ (C*((Radial.zone (E:=E)).w u)^3*t)^(j+1) * shade c u := by unfold shade;gcongr
    _ = _ := by simp only [mul_pow,pow_mul];ring

namespace Stationary
variable {f : E→ℝ}(F : Stationary f)
include F
protected lemma finiteExp (n : ℕ) :
    (Radial.zone (E:=E)).Built 1
      (fun t u=>∑ i∈Finset.range (n+1), (i.factorial:ℝ)⁻¹ * (higher f t u)^i)
      (expsum (layers f) n) := by
  let g (i : ℕ) (t:ℝ)(u:E) := (i.factorial:ℝ)⁻¹ * (higher f t u)^i
  let a (i j : ℕ)(u : E) := (i.factorial:ℝ)⁻¹*TaylorPow (layers f) i j u
  have hp (i : ℕ) : (Radial.zone (E:=E)).Built 1 (g i) (a i) := by simpa only [one_pow, Pi.pow_apply] using! scaled_build (F.expansion.powers i) ((i.factorial:ℝ)⁻¹)
  convert Built.fin_sum (Finset.range (n+1)) (fun i _=>hp i) (fun _=>le_rfl) using 1
  · funext t x;simp [Finset.sum_apply,g]
  funext j x;simp [Finset.sum_apply,a,expsum]

protected theorem exponential {c}(hc : 0<c) :
    (Radial.zone (E:=E)).Built (shade c) (fun t u=>Real.exp (higher f t u)) (fun j=>expsum (layers f) j j) := by
  refine ⟨fun j=> (F.finiteExp j).invoice j,fun j=>?_⟩
  have hv:=step_bound F (j:=j) hc
  have h₁:=((F.finiteExp j).fits j).widen (V':=shade c) (fun _=>hv.envelope ..)
  have he: eval (fun j=>expsum (layers f) j j) j= eval (expsum (layers f) j) j:=by
    funext t u; apply Finset.sum_congr rfl (fun i hi=> by exact congrArg (fun q : E→ℝ => t^i • q u) (expsum_limit (a:=layers f) (funext fun x=>layers_zero (f:=f) x) (Nat.le_of_lt_succ (Finset.mem_range.mp hi))))
  rw [he]; convert hv.add h₁ using 1
  funext t u;exact (sub_add_sub_cancel ..).symm
end Stationary

def insertion (f K : E→ℝ)(t:ℝ)(u) := K (t • u)*Real.exp (higher f t u)
def integrandSeries (f K : E→ℝ) := Zone.mul (jet K) (fun j=>expsum (layers f) j j)

theorem integrand {K f : E→ℝ}(h : ContDiffAt ℝ ∞ K 0) (hf : Stationary f){c}(hc : 0<c) :
   (Radial.zone (E:=E)).Built (shade c) (insertion f K) (integrandSeries f K) := by
  simpa only [one_mul] using! (ordinary K h).prod (hf.exponential hc)

end YM.PertExtension.Series.Radial
