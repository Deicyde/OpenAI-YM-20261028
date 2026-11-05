import YM.PertExtension.Series
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Pointwise testing asymptotics, no exchange with a regulator limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.PertExtension.Series.Tested
open Function Filter Set
open scoped BigOperators Topology Classical
protected abbrev germ := 𝓝[>] (0:ℝ)
local notation "smallScale" => Tested.germ
section General
variable {R : Type*}[NormedAddCommGroup R][NormedSpace ℝ R]

abbrev peval (a : ℕ→R)(n)(t : ℝ) := Zone.eval (fun i (_:Unit)=>a i) n t ()

-- Nonnegative constant form.
def Bill (n : ℕ) (f : ℝ→R) : Prop := ∃ C : ℝ,0≤C ∧ ∀ᶠ t in smallScale, ‖f t‖ ≤ C*t^n

def Aspiration (f : ℝ→R)(a : ℕ→R) : Prop := ∀ n, Bill (n+1) (f - peval a n)

private def z : Zone Unit := ⟨fun _=>1,fun _=>le_rfl⟩

lemma eventually_top {t : ℝ} (ht : 0 < t) : ∀ᶠ r in smallScale,r<t := eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht)
lemma eventually_pos : ∀ᶠ r in smallScale,0<r := self_mem_nhdsWithin
lemma eventually_small {t : ℝ}(ht : 0<t) : ∀ᶠ r in smallScale, 0<r ∧ r<t:=eventually_pos.and (eventually_top ht)

lemma of_bill {f : ℝ→R} {n} (h : Bill n f) : z.Fits (1:Unit→ℝ) n (fun t _ => f t) := by
  obtain ⟨C,hC,h⟩:=h; rw [eventually_nhdsWithin_iff] at h
  obtain ⟨δ,hδ,hd⟩:=Metric.mem_nhds_iff.mp h
  refine ⟨fun _=>le_rfl,δ/2,C,0,half_pos hδ,hC,fun _ t ht he=>?_⟩
  have hh:t∈Metric.ball 0 δ:=by
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg ht.le]; have : t≤δ/2:=by simpa [z] using he
    linarith
  have hd:=@hd t hh ht
  simpa [z] using hd

lemma bill_of {f : ℝ→R} {n} (h : z.Fits (1:Unit→ℝ) n (fun t _ => f t)) : Bill n f := by
  obtain ⟨δ,C,k,hδ,hC,h⟩:=h.cost
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_small hδ] with t ht; exact (h () t ht.1 (by simpa [z] using ht.2.le)).trans_eq (by simp [z])

lemma bill_ge {f : ℝ→R} {n k} (h : Bill n f)(hk : k≤n) : Bill k f := bill_of ((of_bill h).degrade hk)
lemma bill_neg {f : ℝ→R}{n}(h : Bill n f) : Bill n (-f) := bill_of (by convert (of_bill h).neg using 1 <;> rfl)
lemma bill_add {f g : ℝ→R}{n}(hf : Bill n f)(hg : Bill n g) : Bill n (f+g) := bill_of (by convert (of_bill hf).add (of_bill hg) using 1 <;> rfl)
lemma bill_mon {k} (c:R)(ℓ : ℕ)(h : k≤ℓ) : Bill k fun t => t^ℓ • c :=
  bill_of <| (Zone.Fits.power (fun _=>show (1:ℝ)≤1 from le_rfl) (Zone.Invoice.const c) ℓ).degrade h

variable {f g : ℝ→R}{a b : ℕ→R}

namespace Aspiration
lemma of_test (h : Aspiration f a) : z.Built 1 (fun t _=>f t) (fun i _=>a i) := ⟨fun i=>Zone.Invoice.const _,fun i=>by convert of_bill (h i) using 1 <;> rfl⟩
lemma bill_self (h : z.Built 1 (fun t _=>f t) (fun i _=>a i)) : Aspiration f a := fun n=> bill_of (by convert h.fits n using 1 <;> rfl)

lemma add (hf : Aspiration f a)(hg : Aspiration g b):Aspiration (f+g) (a+b) := bill_self (by convert (of_test hf).add (of_test hg) <;> rfl)
lemma sum {I : Type*}(s : Finset I)(f : I→ℝ→R)(A : I→ℕ→R)(hf : ∀ i∈s,Aspiration (f i) (A i)) : Aspiration (∑ i∈s,f i) (∑ i∈s,A i) := by
  refine bill_self ?_
  convert Zone.Built.fin_sum s (fun i hi=>of_test (hf i hi)) (fun _=>le_rfl) using 1
  · funext t u; simp [Finset.sum_apply]
  funext i u; simp [Finset.sum_apply]

lemma single (c : R)(k : ℕ) : Aspiration (fun t=>(t^k • c)) (fun i=>if i=k then c else 0):= by
  intro n; by_cases hn:k≤n
  · obtain ⟨C,hC,H⟩:=(bill_of (f:=0) (n:=n+1) (Zone.Fits.zero (E:=R) (fun _=>le_rfl) z _))
    refine ⟨C,hC,H.mono fun x hx=>?_⟩
    simpa [peval,Zone.eval,smul_ite, Finset.sum_ite_eq', Nat.lt_succ_iff, hn] using hx
  obtain ⟨C,hC,H⟩:=bill_mon c k (Nat.lt_of_not_ge hn)
  refine ⟨C,hC,H.mono fun x hx=>?_⟩
  simpa [peval,Zone.eval,smul_ite, Finset.sum_ite_eq', Nat.lt_succ_iff, hn] using hx

-- Substitute finite truncation as an actual polynomial, at every order.
lemma polynomial (a : ℕ→R)(m : ℕ) : Aspiration (peval a m) (fun i=>if i≤m then a i else 0) := by
  let s:=Finset.range (m+1)
  convert sum s _ _ (fun k hk=>single (a k) k) using 1
  · funext t; simp [s,peval,Zone.eval,Finset.sum_apply]
  funext i; simp [s,Finset.sum_apply,Nat.lt_succ_iff]

lemma tendsto_first (hf : Aspiration f a):Tendsto f smallScale (𝓝 (a 0)):= Metric.tendsto_nhds.mpr fun ε he=>by
  obtain ⟨C,hC,h⟩:= hf 0
  filter_upwards [h,eventually_small (show 0<ε/(C+1) by positivity)] with t ht hz
  simp [peval,Zone.eval] at ht; rw [dist_eq_norm_sub]; nlinarith [(lt_div_iff₀ (by positivity:0<C+1)).mp hz.2]

lemma single_part (hf : Aspiration f a)(hg : Aspiration f b) (k) (h : ∀ i < k,a i=b i) : a k=b k := by
  obtain ⟨C,hC,hf⟩:= hf k
  obtain ⟨D,hD,hg⟩:= hg k
  let ε:=‖a k-b k‖
  by_contra H
  have hp : 0<ε:= norm_pos_iff.mpr (sub_ne_zero.mpr H)
  have hsmall := hf.and (hg.and (eventually_small (show 0<ε/(C+D+1) by positivity)))
  obtain ⟨t,HF,HG,ht,hlt⟩:=hsmall.exists
  have heq: ((f-peval b k) -(f-peval a k)) t=t^k • (a k-b k):=by
       change (f t - peval b k t) - (f t - peval a k t) = t^k • (a k-b k)
       unfold peval Zone.eval
       rw [Finset.sum_range_succ,Finset.sum_range_succ,show (∑ i∈Finset.range k,t^i • a i) =∑ i∈Finset.range k,t^i • b i by apply Finset.sum_congr rfl;intro i hi;rw [h _ (Finset.mem_range.mp hi)], smul_sub]; abel
  have hh : ε≤(C+D)*t:=by
    apply le_of_mul_le_mul_left (a:=t^k) ?_ (pow_pos ht k)
    change t^k*‖a k-b k‖≤ _
    rw [←abs_of_pos (a:=t^k) (pow_pos ht _),← Real.norm_eq_abs,← norm_smul, ← heq]
    change ‖(f-peval b k) t - (f-peval a k) t‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_pos (pow_pos ht _)]
    exact ((norm_sub_le ..).trans (add_le_add HG HF)).trans_eq (by rw [pow_succ]; ring)
  have := (lt_div_iff₀ (show (0:ℝ)<C+D+1 by positivity)).mp hlt
  linarith

lemma unique (ha : Aspiration f a)(hb : Aspiration f b) : a=b:= by
  funext i; induction i using Nat.strong_induction_on with
  | _ k ih=>exact ha.single_part hb k ih

end Aspiration
end General

section Field
variable {𝕜 : Type*}[NormedField 𝕜][NormedAlgebra ℝ 𝕜]
variable {f g : ℝ→𝕜}{a b : ℕ→𝕜}

open PowerSeries
def term (a : 𝕜⟦X⟧) (i : ℕ) := coeff i a
def conv (a b : ℕ→𝕜):= term (PowerSeries.mk a * PowerSeries.mk b)
def reciprocal (b : ℕ→𝕜):= term ((PowerSeries.mk b)⁻¹)
def divide (a b : ℕ→𝕜):= term (PowerSeries.mk a * (PowerSeries.mk b)⁻¹)

namespace Aspiration
lemma prod (hf : Aspiration f a)(hg : Aspiration g b) : Aspiration (f*g) (conv a b) := by
  apply bill_self; have h := hf.of_test.prod hg.of_test
  have heq : Zone.mul (fun i (_:Unit)=>a i) (fun i _=>b i)=fun k u=>conv a b k:=by
    funext k u
    simp [Zone.mul,conv,term,coeff_mul]
  rw [heq,one_mul] at h;exact h

private lemma eval_via {a b : ℕ→𝕜}(H : b 0 ≠ 0)(n : ℕ)(t : ℝ) :
    peval (conv b (fun i => if i≤n then reciprocal b i else 0)) n t = (1:𝕜) := by
  let A := PowerSeries.mk b
  have hA : PowerSeries.constantCoeff A ≠ 0 := by simpa [A,← PowerSeries.coeff_zero_eq_constantCoeff_apply] using! H
  have hd := PowerSeries.mul_inv_cancel A hA
  let a := (fun i : ℕ=>if i≤n then reciprocal b i else 0)
  have hb {k}(hk:k≤n) : conv b a k=coeff k (1:𝕜⟦X⟧) := by
    unfold conv term; rw [coeff_mul,← hd,coeff_mul]
    apply Finset.sum_congr rfl fun j hj=> ?_;have hj := Finset.mem_antidiagonal.mp hj
    have h' : j.2≤n:=by omega
    simp [A,a,h',reciprocal,term]
  calc
    peval _ n t = peval (fun k=>if k=0 then (1:𝕜) else 0) n t := by unfold peval Zone.eval; exact Finset.sum_congr rfl (fun k hk=> congr_arg (fun c:𝕜=>t^k • c) ((hb (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).trans (coeff_one k)))
    _ = (1:𝕜) := by simp [peval,Zone.eval,smul_ite, Finset.sum_ite_eq']

lemma inverse (hf : Aspiration f a) (h : a 0 ≠ 0) : Aspiration f⁻¹ (reciprocal a) := by
  intro n
  obtain ⟨C,hC,H⟩:= (hf.prod (polynomial (reciprocal a) n)) n
  have hh := hf.tendsto_first.inv₀ h |>.norm
  have hc := hh.eventually (isOpen_Iio.mem_nhds (show ‖(a 0)⁻¹‖ < ‖(a 0)⁻¹‖+1 by linarith))
  refine ⟨(‖(a 0)⁻¹‖+1)*C,by positivity,?_⟩
  filter_upwards [H,hc,hf.tendsto_first.eventually (isOpen_compl_singleton.mem_nhds (show (a 0) ∈ ({0}:Set 𝕜)ᶜ from h))] with t ht hC hne
  have hint : ‖(f⁻¹-peval (reciprocal a) n) t‖= ‖(f t)⁻¹‖*‖1 - f t*peval (reciprocal a) n t‖:=by
    rw [←norm_mul]; congr 1; dsimp only [Pi.sub_apply,Pi.inv_apply];
    have hne:f t≠0:=hne
    rw [mul_sub,mul_one,← mul_assoc,inv_mul_cancel₀ hne,one_mul]
  rw [hint,mul_assoc]; gcongr
  rw [norm_sub_rev]; simpa only [Pi.sub_apply,Pi.mul_apply,eval_via (𝕜:=𝕜) (a:=a) h] using ht

lemma quotient (hf : Aspiration f a)(hg : Aspiration g b) (h : b 0 ≠ 0):Aspiration (f/g) (divide a b) := by
  rw [div_eq_mul_inv]
  convert hf.prod (hg.inverse h) using 1
  have h : PowerSeries.mk (reciprocal b)= (PowerSeries.mk b)⁻¹:= by ext n;simp [reciprocal,term];
  rw [divide,conv,h]

end Aspiration
end Field

end YM.PertExtension.Series.Tested
