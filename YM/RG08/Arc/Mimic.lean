import YM.RG08.Arc.Fit
import Mathlib.RingTheory.PowerSeries.Exp
/-! # Evaluating the formal exponential after a test path substitution
Pointwise fit, no coupling domains at physical fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter PowerSeries Finset Function YM.PertExtension.Series YM.PertExtension.Series.Tested
open YM.PertExtension.Series.Radial
open scoped BigOperators Topology Real ContDiff Classical
variable {u : ℕ} {F H : Reel ℝ}
private def formal (F : Reel ℝ) := PowerSeries.subst (mk F) (PowerSeries.exp ℝ)
private lemma compatible_s (h : F 0=0) : HasSubst (mk F) := .of_constantCoeff_zero (by rwa [show MvPowerSeries.constantCoeff (mk F)=constantCoeff (mk F) from rfl,← coeff_zero_eq_constantCoeff_apply,coeff_mk])
private lemma aura_x (h : Aura H F) (j k : ℕ) (he : j≤k) : H j=∑ i∈range (k+1), ((i.factorial:ℝ))⁻¹ * coeff j (mk F ^ i) := by
  let X':=PowerSeries.X (R:=ℝ); let P:=PowerSeries.derivative ℝ
  have hs i (p : PowerSeries ℝ) : coeff i (X'*(P p))=i • coeff i p := by
    cases i with
    | zero=> rw [coeff_zero_X_mul,zero_smul]
    | succ i=> rw [coeff_succ_X_mul, coeff_derivative,nsmul_eq_mul, Nat.cast_succ,mul_comm]
  have hd : X'*(P (formal F))= X'*(P (mk F))* (formal F) := by rw [formal,PowerSeries.derivative_subst ℝ (compatible_s h.1),derivative_exp]; ring
  have ht k' (i : ℕ) (hp : k' ≤ i) : coeff k' (formal F)=∑ b∈range (i+1), ((b.factorial:ℝ))⁻¹*coeff k' (mk F ^ b) := by
    unfold formal; rw [coeff_subst' (compatible_s h.1),finsum_eq_sum_of_support_subset (s:=range (i+1)) _]
    · simp [coeff_exp]
    intro b hb; by_contra hV
    have hR : k'<b := by simp only [mem_coe,mem_range,not_lt] at hV; omega
    have hx n : ∀ u<n,coeff u (mk F ^ n)=0 := by
      induction n with
      | zero=> simp
      | succ n ih=>
        intro i hi; rw [pow_succ,coeff_mul]; apply Finset.sum_eq_zero; intro a ha
        by_cases hh:a.1<n; · rw [ih a.1 hh,zero_mul]
        rw [show a.2=0 by have hy:=mem_antidiagonal.mp ha; omega,coeff_mk,h.1,mul_zero]
    exact hb (by dsimp only; rw [hx b k' hR,smul_zero])
  rw [← ht _ k he]; clear he
  induction j using Nat.caseStrongRecOn with
  | zero=>rw [ht _ 0 le_rfl]; simp [h.2.1]
  | ind j ih=>
    apply (smul_right_inj (show j+1≠0 by omega)).1
    rw [← hs, hd, coeff_mul, h.2.2]; apply sum_congr rfl; intro p hp
    rw [hs,coeff_mk]; by_cases ht:p.2≤j; · rw [ih p.2 ht]
    have he:=mem_antidiagonal.mp hp
    rw [show p.1=0 by omega,zero_smul,zero_mul,zero_mul]

-- Bill composition along SAME t. No analytic part assumed for coefficients.
variable {p f g : ℕ→ℝ→ℝ}

def year (f : ℕ→ℝ→ℝ) (k : ℕ) := fun t:ℝ=>∑ j∈range (k+1), t^j • f j t
lemma ruler (a k : ℕ)(h : a ≤ k) : Bill a (fun t : ℝ=> t^k) := by simpa only [smul_eq_mul,mul_one] using bill_mon (1:ℝ) k h
lemma year_bills (h : ∀ i,Bill 0 (p i)) (k : ℕ) : Bill 0 (year p k) := by
  rw [show year p k=∑ i∈range (k+1), (fun t:ℝ=> t^i*p i t) from funext fun t=>Eq.symm (Finset.sum_apply t ..)]
  exact bill_sum _ _ (fun i _=> bill_mul (ruler 0 i (Nat.zero_le _)) (h i))

lemma year_earns (h : ∀ i,Bill 0 (p i)) (k : ℕ) (hp : p 0=0) : Bill 1 (year p k) := by
  let P (i : ℕ) := fun t : ℝ=> t^i • p i t
  rw [show year p k=∑ i∈range (k+1), P i from funext fun t=> Eq.symm (Finset.sum_apply t _ P)]
  refine bill_sum _ _ fun i _=>?_
  cases i with
  | zero=> exact ⟨0,le_rfl,Eventually.of_forall (by simp [P,hp])⟩
  | succ i=> exact bill_mul (ruler 1 _ (by omega)) (h _)
lemma year_mult (h : ∀ i, Bill 0 (f i)) (hp : ∀ i, Bill 0 (g i)) (n) :
    Fit (n+1) (year f n*year g n) (year (Zone.mul f g) n) := by
  let R:=range (n+1); let S:=R×ˢR; let L:=S.filter fun i=>i.1+i.2≤n
  let e (i : ℕ×ℕ) := fun t : ℝ => t^(i.1+i.2)* (f i.1 t*g i.2 t)
  rw [show year f n*year g n=∑ i∈S,e i from funext fun t=> by
    unfold year; simp only [Pi.mul_apply, smul_eq_mul,S, sum_product,sum_mul]; simp_rw [Finset.mul_sum]; rw [Finset.sum_apply]; apply sum_congr rfl; intro i _; rw [Finset.sum_apply]; apply sum_congr rfl; intro j _; dsimp only [e]; rw [pow_add]; ring]
  rw [show year (Zone.mul f g) n=∑ i∈ L,e i from funext fun t=> by
    unfold year; rw [Finset.sum_apply,← Finset.sum_fiberwise_of_maps_to (show ∀ i∈L,i.1+i.2 ∈ R from fun i hi=> mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hi).2)) (fun i=>e i t)]; apply sum_congr rfl; intro i hi
    have hx : wheel i=L.filter fun j=>j.1+j.2=i := by ext j; have hi:=mem_range.mp hi; simp only [L,S,R,wheel, mem_filter,mem_antidiagonal, mem_product, mem_range]; omega
    rw [Zone.mul,smul_sum]; apply sum_congr hx; intro b hb; unfold e; rw [(mem_filter.mp hb).2]; rfl]
  unfold Fit
  rw [← Finset.sum_sdiff (f:=e) (show L ⊆ S from filter_subset (fun i=> i.1+i.2≤n) S),add_sub_cancel_right]
  exact bill_sum _ _ (fun i hi=> bill_mul (j:=0) (k:=n+1) (ruler (n+1) (i.1+i.2) (show _ by have he:=mem_sdiff.mp hi; have hh : ¬ i.1+i.2 ≤ n := fun h => he.2 (mem_filter.mpr ⟨he.1,h⟩); omega)) (bill_mul (h i.1) (hp i.2)))
lemma year_crown (h : ∀ i, Bill 0 (f i)) (u n : ℕ) : Fit (n+1) ((year f n)^u) (year (Zone.TaylorPow f u) n) ∧ ∀ i,Bill 0 (Zone.TaylorPow f u i) := by
  induction u with
  | zero=> refine ⟨?_,fun i=>?_⟩
           · rw [pow_zero,show year (Zone.TaylorPow f 0) n=1 from funext fun t=> by simp only [year,Zone.TaylorPow]; simp [mul_ite]]; exact Fit.same ..
           by_cases he : i=0 <;> simpa only [Zone.TaylorPow, he,if_pos,if_neg] using! bill_const (R:=ℝ) (if i=0 then 1 else 0)
  | succ u ih=>
    rw [pow_succ]; refine ⟨(ih.1.left (year_bills h n)).join (year_mult ih.2 h n), fun i=>?_⟩
    rw [Zone.TaylorPow]; let Y (a : ℕ×ℕ) := Zone.TaylorPow f u a.1*f a.2
    rw [show Zone.mul (Zone.TaylorPow f u) f i=∑ j∈wheel i,Y j from funext fun j=> Eq.symm (by simp [Finset.sum_apply,Y,Zone.mul,wheel])]; exact bill_sum _ _ (fun i _=> bill_mul (ih.2 i.1) (h i.2))
private lemma aura_wag (f : ℕ→ℝ→ℝ) (t : ℝ) (u i) : coeff i (mk (fun i=> f i t) ^ u)= Zone.TaylorPow f u i t := by
  induction u generalizing i with
  | zero=> simp [Zone.TaylorPow,PowerSeries.coeff_one]
  | succ u ih=> rw [pow_succ, coeff_mul, Zone.TaylorPow,Zone.mul];simp_rw [coeff_mk,ih]
lemma bill_goes {p : ℝ→ℝ} (h : Bill 1 p) : Tendsto p (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,hC,H⟩:=h; apply Metric.tendsto_nhds.mpr; intro ε he
  filter_upwards [H,eventually_small (show 0<ε/(C+1) by positivity)] with v hv hz
  rw [dist_zero_right]; rw [pow_one] at hv
  have ht := (lt_div_iff₀ (show 0<C+1 by positivity)).mp hz.2; exact lt_of_le_of_lt hv (by linarith [hz.1])
lemma exp_fits {p : ℝ→ℝ} (h : Bill 1 p)(k) : Fit (k+1) (Real.exp∘p) (fun t=> ∑ i∈range (k+1), ((i.factorial:ℝ))⁻¹ * (p t)^i) := by
  have he:=bill_goes h
  obtain ⟨D,hD,hb⟩:=h
  obtain ⟨C,hC,Hc⟩:= (Real.exp_sub_sum_range_isBigO_pow (k+1)).exists_nonneg; refine ⟨C*D^(k+1),by positivity,?_⟩
  filter_upwards [he.eventually Hc.bound,hb,eventually_pos] with t ht hv hp
  have hx : (∑ i∈range (k+1), ((i.factorial:ℝ))⁻¹ * (p t)^i)=(∑ i∈range (k+1), (p t)^i / (i.factorial:ℝ)) := sum_congr rfl (fun i _=> by rw [mul_comm,div_eq_mul_inv]);
  change ‖Real.exp _ - _‖ ≤ _; dsimp only; rw [hx]; rw [pow_one] at hv
  exact ht.trans ((show C * ‖p t ^ (k+1)‖ ≤ _ from mul_le_mul_of_nonneg_left (show ‖p t ^ (k+1)‖ ≤ (D*t)^(k+1) from by rw [norm_pow]; gcongr) hC).trans_eq (by rw [mul_pow,mul_assoc]))
lemma year_aura (h : ∀ t, Aura (fun i=>p i t) (fun i=>f i t)) (hp : ∀ i,Bill 0 (f i)) (n) :
    Fit (n+1) (Real.exp ∘ year f n) (year p n) := by
  let R:=range (n+1)
  have he : f 0=0 := funext fun t=> (h t).1
  have hu := exp_fits (year_earns hp n he) n
  apply hu.join
  have hx : year p n=(∑ i∈R, ((i.factorial:ℝ))⁻¹ • year (Zone.TaylorPow f i) n) := by
    funext t; unfold year; rw [Finset.sum_apply]; simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i hi; rw [aura_x (h t) _ n (by have hv:=mem_range.mp hi; omega),Finset.mul_sum]; exact sum_congr rfl fun j _=>by rw [aura_wag]; ring
  rw [hx, show (fun t=>∑ i∈range (n+1), ((i.factorial:ℝ))⁻¹*year f n t ^i)=∑ i∈R, ((i.factorial:ℝ))⁻¹ • ((year f n)^i) from funext fun t=> by simp [Finset.sum_apply,R]]
  exact Fit.list (fun i _=> (year_crown hp i n).1.scale _)
end YM.RG08.Reflect
