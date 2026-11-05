import YM.TraceExtension.Perfect.Tensor

/-! # Jet gain normalized -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Stationary Filter Function Matrix Lattice Precision Finset OrderedFinpartition
open scoped Topology BigOperators ContDiff
variable {I J W:Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
    {m : ℕ} {X : Type*}[NormedAddCommGroup X][NormedSpace ℝ X]

def sail (f:Rays I → Rays J) (x:Rays I)(A:I→ℕ)(m : ℕ)(j:J)(α : ℝ)(t:ℕ)(r:ℝ) := cost A α t r fun v=> leaf f x m v j
lemma sail_nn (f:Rays I → Rays J)(x A m j α t r): 0 ≤ sail f x A m j α t r:= cost_nn ..
lemma sail_anti (f:Rays I → Rays J)(x A m j α t r s) (h:0 ≤ α)(hp:r ≤ s): sail f x A m j α t s ≤ sail f x A m j α t r:=cost_anti _ _ _ _ _ _ h hp

def rush (L : ℝ)(r : ℕ):= L⁻¹ * min 1 ((1+r)/L)
lemma rush_nn {L:ℝ}(h:0<L)(r): 0 ≤ rush L r:=mul_nonneg (inv_nonneg.mpr h.le) (le_min (by norm_num) (by positivity))
lemma rush_incr {L:ℝ}(h:0<L): Monotone (rush L):= by
 intro i j he; unfold rush; gcongr
lemma moment_collect {α β L:ℝ}(t r)(ha:0 ≤ α)(hL:1 ≤ L)(he:α/L ≤ β) : shelter α t ((r:ℕ)/L) ≤ spot β t 0 r:=by
 unfold shelter spot
 have hp : 0<L:= lt_of_lt_of_le zero_lt_one hL; have ht : 0 ≤ (r:ℝ)/L:=by positivity
 simp only [sub_zero, max_eq_right (show (0:ℝ) ≤ r from Nat.cast_nonneg _)]
 refine mul_le_mul ?_ ?_ (Real.exp_pos _).le (by positivity)
 · exact pow_le_pow_left₀ (by positivity) (by linarith only [div_le_self (show 0≤ (r:ℝ) from Nat.cast_nonneg _) hL]) t
 apply Real.exp_monotone (le_trans (le_of_eq (show α*((r:ℝ)/L)=α/L*r by ring)) (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)))
lemma golden {α β L:ℝ}(n t r)(hL:1 ≤ L)(he:α/L ≤ β)(hk:n ≤ t) :
    shelter α t ((r:ℕ)/L) * rush L r^n ≤ (2:ℝ)^n/L^(2*n) * spot β t 0 r:=by
 have h : 0<L:=lt_of_lt_of_le zero_lt_one hL
 have hx:0≤(r:ℝ):=Nat.cast_nonneg _
 let u:= min 1 ((1+r)/L); let v:ℝ:= 1+r/L
 have hu:0 ≤ u:= le_min zero_le_one (by positivity)
 have hv0:0 ≤ v:= by unfold v; positivity
 have hv:v ≤ 1+r := add_le_add_right (div_le_self hx hL) _
 have hf: v * (L⁻¹ * u) ≤ (2/L^2)*(1+r) := by
    by_cases hh:(r:ℝ) ≤ L
    · have hs : v ≤ 2:= by unfold v; linarith only [div_le_one h|>.mpr hh]
      apply le_trans (mul_le_mul hs (mul_le_mul_of_nonneg_left (min_le_right ..) (inv_nonneg.mpr h.le)) (by positivity : 0 ≤ L⁻¹*u) (by norm_num : (0:ℝ)≤2)) (le_of_eq ?_); field_simp
    have he: 1 ≤ (r:ℝ)/L:= (one_le_div h).mpr (le_of_not_ge hh)
    calc
     _ ≤ (2*((r:ℝ)/L))*(L⁻¹*1) := mul_le_mul (show v ≤ _ by unfold v; linarith) (mul_le_mul_of_nonneg_left (min_le_left ..) (by positivity)) (by positivity) (by positivity)
     _ = (2/L^2)*r := by field_simp
     _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
 have hr : rush L r = L⁻¹*u := rfl
 have hm : Real.exp (α * ((r:ℝ)/L)) ≤ Real.exp (β*r) := Real.exp_monotone (le_trans (le_of_eq (show α*((r:ℝ)/L)=α/L*r by ring)) (mul_le_mul_of_nonneg_right he hx))
 have hh : v^t*(rush L r)^n ≤ ((2:ℝ)/L^2)^n * (1+(r:ℝ))^t := calc
     _ = v^(t-n) * (v*rush L r)^n:= by rw [mul_pow, ← mul_assoc,← pow_add]; congr 2; omega
     _ ≤ (1+(r:ℝ))^(t-n) * ((2/L^2)*(1+r))^n := mul_le_mul (pow_le_pow_left₀ hv0 hv _) (pow_le_pow_left₀ (mul_nonneg hv0 (rush_nn h _)) hf n) (by apply pow_nonneg (mul_nonneg hv0 (rush_nn h _))) (by positivity)
     _ = _:= by rw [mul_pow,mul_left_comm,← pow_add]; congr 2; omega
 have ht := mul_le_mul hh hm (Real.exp_pos _).le (by positivity); unfold spot; unfold shelter; unfold v at ht; rw [div_pow,← pow_mul] at ht; simp only [sub_zero,max_eq_right hx]; exact le_trans (le_of_eq (mul_right_comm ..)) (ht.trans_eq (mul_assoc ..))

open Planned.PrimaryIntegral295.Cases
variable {α β L:ℝ} {A:I→ℕ} {B:J→ℕ}{t:ℕ}
def ferries (A:I→ℕ)(α t) (g:Rays J→ X) (f:Rays I→ Rays J) (x:Rays I)(c:OrderedFinpartition m):=cost A α t 0 fun b=> caseRead c g f x (desk ∘ b)
lemma fares (g:Rays J→ X) (f:Rays I → Rays J)(x:Rays I) (c:OrderedFinpartition m) (hL : 1≤L) (ha:0≤α) :
    ferries A α t g f x c ≤ ∑ z, (shelter α t ((limitN B z)/L) * ∏ i, sail f x A (c.partSize i) (z i) α t ((limitN B z)/L))* ‖leaf g (f x) _ z‖ := by
 exact volume_join A _ _ c (iteratedFDeriv ℝ c.length g (f x)) (fun i=>leaf f x (c.partSize i)) (fun z=>(limitN B z)/L) ha (fun z=>by have he:= lt_of_lt_of_le zero_lt_one hL; positivity)
lemma fee_coarse {g:Rays J→ X}{f:Rays I → Rays J}{x:Rays I}(c:OrderedFinpartition m) (hL : 1≤L) (ha:0≤α) (hx : α/L ≤ β) (F: Fin c.length→ℝ) (hr : ∀ i j, sail f x A (c.partSize i) j α t (B j/L) ≤ F i) :
    ferries A α t g f x c ≤ (∏ i,F i) * cost B β t 0 (leaf g (f x) c.length) := by
 have hp := lt_of_lt_of_le zero_lt_one hL; refine (fares g f x c (A:=A) (B:=B) hL ha).trans ?_
 unfold cost; rw [Finset.mul_sum]; apply sum_le_sum; intro i _; rw [← mul_assoc, mul_comm (∏ j,F j)]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
 have hz : ∀ j,sail f x A (c.partSize j) (i j) α t ((limitN B i)/L)≤F j:=fun j=>(sail_anti _ _ _ _ _ _ _ (B (i j)/L) _ ha (div_le_div_of_nonneg_right (Nat.cast_le.mpr (limitN_ge B i j)) hp.le)).trans (hr j (i j))
 exact le_trans (mul_le_mul_of_nonneg_left (prod_le_prod (fun j _=> sail_nn ..) (fun j _=> hz j)) (shelter_pos _ _ (by positivity)).le) (mul_le_mul_of_nonneg_right (moment_collect t _ ha hL hx) (prod_nonneg fun j _=> (sail_nn ..).trans (hz j)))
lemma fee_atomic {g:Rays J→ X}{f:Rays I → Rays J}{x:Rays I}(hL : 1≤L) (ha:0≤α) (hx : α/L ≤ β)(hm:m≤t) {S:ℝ}(hs:0 ≤ S) (hr: ∀ j,sail f x A 1 j α t (B j/L)≤ S * rush L (B j)) :
    ferries A α t g f x (.atomic m) ≤ (S*2/L^2)^m * cost B β t 0 (leaf g (f x) m):=by
 let c:=atomic m; refine (fares g f x (B:=B) c hL ha).trans ?_; unfold cost; rw [Finset.mul_sum]; apply sum_le_sum; intro i _; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
 let R:= limitN B i; have hp:= lt_of_lt_of_le zero_lt_one hL; have hh:= rush_nn hp R
 let Z:=∏ j,sail f x A (c.partSize j) (i j) α t (R/L)
 have hz: Z ≤ (S*rush L R)^c.length:=by
     unfold Z
     refine (prod_le_prod (fun j _=> sail_nn ..) (g:=fun _=> S*rush L R) (fun j _ => ?_)).trans_eq (by simp)
     have he:=limitN_ge B i j
     exact ((sail_anti _ _ _ 1 _ _ _ (B (i j)/L) _ ha (div_le_div_of_nonneg_right (Nat.cast_le.mpr he) hp.le)).trans (hr _)).trans (mul_le_mul_of_nonneg_left (rush_incr hp he) hs)
 change shelter α t (R/L)*Z ≤ _
 calc
  _ ≤ shelter α t (R/L)*(S*rush L R)^m:= mul_le_mul_of_nonneg_left hz (shelter_pos _ _ (by positivity)).le
  _ = S^m*(shelter α t (R/L)*rush L R^m) := by ring
  _ ≤ S^m*(2^m/L^(2*m)*spot β t 0 R):= mul_le_mul_of_nonneg_left (golden m _ _ hL hx hm) (pow_nonneg hs _)
  _ = _:= by rw [div_pow,mul_pow,pow_mul]; unfold R; ring_nf; rfl

lemma split_fees (g:Rays J→X)(f:Rays I → Rays J) (x:Rays I) (he : ContDiffAt ℝ ω g (f x))(hx : ContDiffAt ℝ ω f x)(n : ℕ): cost A α t 0 (leaf (g ∘ f) x n) ≤ ∑ c: OrderedFinpartition n, ferries A α t g f x c:= by
 let P c b := caseRead (n:=n) c g f x (desk ∘ b)
 have hz : leaf (g ∘ f) x n=(fun b=>∑ c,P c b):= funext fun b=> compReads he hx (by simp) _
 rw [hz]; exact cost_sum ..

end YM.Trace.Perfect
