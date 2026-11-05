import YM.Euclid.Test
import YM.Analysis.Homogeneous
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Full relative-coordinate test-function convention

Complex-linear slot, no conjugating tests on contact prescriptions. Use
arbitrary joint normal tests with support booked separately. `Charge` allows
any supplied Cʲ test budget, saying it enforces the usual finite set of
sup inequalities. Include scale. This avoids having to fix a seminorm object
on each different compact under consideration. Bound works for every admissible
value of the budget, *and* one exists on each such test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Normal
open Function Set TopologicalSpace Filter MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {X Y:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]

abbrev Full (X:Type*) [NormedAddCommGroup X][NormedSpace ℝ X]:= TestFunction (⊤:Opens X) ℂ ⊤

def join (u v: Full X) : Full X:=⟨fun x=> u x * v x,u.contDiff.mul v.contDiff, u.hasCompactSupport.mul_right,subset_univ _⟩
@[simp] lemma join_apply (u v:Full X)(x:X): join u v x=u x*v x:=rfl
lemma join_left (u v:Full X): tsupport (join u v) ⊆ tsupport u:=tsupport_mul_subset_left
lemma join_right (u v:Full X): tsupport (join u v)⊆tsupport v:=tsupport_mul_subset_right

abbrev Smooth (g:X→Y) := ContDiff ℝ ∞ g

def Estimate (j:ℕ)(s:ℝ)(f:X→ Y)(L:Set X)(P:ℝ):Prop:=∀ i≤j,∀ x∈L,s^i*‖iteratedFDeriv ℝ i f x‖≤P
def Charge (j:ℕ)(s:ℝ)(f:X→Y)(P:ℝ):Prop:= Estimate j s f univ P
variable {j n:ℕ}{B s t P Q :ℝ}{L N:Set X}{f g:X→Y}
theorem Estimate.zero (u:X→ Y) (he:Estimate j s u L P){x:X}(hx:x∈ L):‖u x‖ ≤ P:=by simpa using he 0 (Nat.zero_le _) x hx
theorem Charge.nonneg (he:Charge j s f P): 0 ≤ P:= (norm_nonneg _).trans (Estimate.zero f he (mem_univ (0:X)))
theorem Estimate.down_cost (he:Estimate j s f L P)(h:P≤Q): Estimate j s f L Q:=fun i hi x hx=>(he i hi x hx).trans h
theorem Estimate.lower (he:Estimate j s f L P)(h:n≤j):Estimate n s f L P:=fun i hi=> he i (hi.trans h)
theorem Estimate.subset (he:Estimate j s f L P)(h:N⊆L): Estimate j s f N P:=fun i hi x hx=>he i hi x (h hx)
theorem Estimate.due (he:Estimate j s f L P)(hv:tsupport f⊆ L)(hP:0 ≤ P): Charge j s f P:=by
  intro i hi x _; by_cases h:x∈ L; · exact he i hi x h
  rw [image_eq_zero_of_notMem_tsupport (fun hy=> h (hv (tsupport_iteratedFDeriv_subset i hy))), norm_zero,mul_zero]; exact hP

theorem exists_charge (j:ℕ)(φ:Full X)(s:ℝ)(hs:0≤ s):∃ P:ℝ,Charge j s (φ : X→ℂ) P:=by
  obtain ⟨P,hP⟩:∃ P:ℝ,∀ i:Fin (j+1), s^i.val*SchwartzMap.seminorm ℂ 0 i (HasCompactSupport.toSchwartzMap φ.hasCompactSupport φ.contDiff) ≤ P:= (eventually_all.mpr (fun i : Fin (j+1)=> eventually_ge_atTop _)).exists
  refine ⟨P,fun i hi x hx=> le_trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hs _)) (hP (⟨i,by omega⟩:Fin (j+1)))⟩
  simpa only [show (HasCompactSupport.toSchwartzMap φ.hasCompactSupport φ.contDiff:X→ℂ)=(φ:X→ℂ) from rfl,pow_zero,one_mul] using (SchwartzMap.le_seminorm ℂ 0 i (HasCompactSupport.toSchwartzMap φ.hasCompactSupport φ.contDiff) x)
theorem natural_le (i:ℕ): (i:WithTop ℕ∞) ≤ ∞:= by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top)
theorem charge_smooth (h:Smooth f)(i:ℕ):ContDiff ℝ ↑i f:= h.of_le (natural_le i)
theorem Estimate.add (hf:Estimate j s f L P)(hg:Estimate j s g L Q)(hf':Smooth f)(hg':Smooth g)(hs:0 ≤ s) : Estimate j s (f+g) L (P+Q):=by
  intro i hi x hx
  rw [iteratedFDeriv_add_apply (charge_smooth hf' i).contDiffAt (charge_smooth hg' i).contDiffAt];
  exact (mul_le_mul_of_nonneg_left (norm_add_le ..) (pow_nonneg hs i)).trans (by rw [mul_add]; exact add_le_add (hf i hi x hx) (hg i hi x hx))
theorem Estimate.neg (hf:Estimate j s f L P):Estimate j s (-f) L P:=by
  intro i hi x hx; rw [iteratedFDeriv_neg_apply,norm_neg]; exact hf i hi x hx
theorem Estimate.sub (hf:Estimate j s f L P)(hg:Estimate j s g L Q)(hf':Smooth f)(hg':Smooth g)(hs:0 ≤ s) : Estimate j s (f-g) L (P+Q):=by rw [sub_eq_add_neg]; exact hf.add hg.neg hf' hg'.neg hs

theorem Estimate.scale_le (hv:Estimate j s f L P)(ht:0 ≤ t)(he:t≤s): Estimate j t f L P:=fun i hi x hx=> (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht he _) (norm_nonneg _)).trans (hv i hi x hx)
theorem Estimate.scale_up (hv:Estimate j s f L P)(hs:0 ≤ s)(ht:0 ≤ t)(hP:0 ≤ P)(hB:1 ≤ B)(he:t≤ B*s): Estimate j t f L (B^j * P):=by
  intro i hi x hx
  calc
    _ ≤ (B*s)^i * _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht he _) (norm_nonneg _)
    _ = B^i * (s^i * ‖iteratedFDeriv ℝ i f x‖) := by rw [mul_pow,mul_assoc]
    _ ≤ _ := mul_le_mul (pow_le_pow_right₀ hB hi) (hv i hi x hx) (mul_nonneg (pow_nonneg hs _) (norm_nonneg _)) (pow_nonneg (by linarith only [hB]) _)

variable {φ ψ:X→ℂ}
theorem Estimate.smulR (z:ℝ)(h:Estimate j s f L P)(hc:Smooth f) : Estimate j s (z • f) L (‖z‖ * P):=by
  intro i hi x hx; rw [iteratedFDeriv_const_smul_apply (hf:=(charge_smooth hc i).contDiffAt),norm_smul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (h i hi x hx) (norm_nonneg z)
theorem Estimate.smul (z:ℂ)(h:Estimate j s φ L P)(hc:Smooth φ) : Estimate j s (z • φ) L (‖z‖ * P):=by
  intro i hi x hx; rw [iteratedFDeriv_const_smul_apply (hf:=(charge_smooth hc i).contDiffAt),norm_smul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (h i hi x hx) (norm_nonneg z)

theorem Estimate.mul (hf:Estimate j s φ L P)(hg:Estimate j s ψ L Q)(hP:0 ≤ P)(hQ:0 ≤ Q)(hs:0 ≤ s)(h:Smooth φ)(h':Smooth ψ) : Estimate j s (φ*ψ) L ((2:ℝ)^j*P*Q):=by
  intro i hi x hx
  apply (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le h h' x (natural_le i)) (pow_nonneg hs i)).trans
  let A := Finset.range (i+1)
  let Y(a:ℕ):=(i.choose a:ℝ)
  have he : ∑ a∈A, Y a= (2:ℝ)^i:=by unfold A Y; exact_mod_cast Nat.sum_range_choose i
  rw [Finset.mul_sum]; refine le_trans (Finset.sum_le_sum (g:=fun a=> Y a*P*Q) fun a ha=>?_) ?_
  · let X':=‖iteratedFDeriv ℝ a φ x‖; let X'':=‖iteratedFDeriv ℝ (i-a) ψ x‖; have hv:a≤ i:=by simpa only [Finset.mem_range,Nat.lt_succ_iff] using ha
    have hu: s^i=s^a * s^(i-a):=by rw [← pow_add, Nat.add_sub_of_le hv]
    change s^i*(Y a * X' * X'') ≤ Y a*P*Q
    rw [hu, show s^a * s^(i-a)*(Y a* X' * X'')= Y a * (s^a * X' * (s^(i-a)*X'')) by ring,mul_assoc (Y a) P Q]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hf a (by omega) x hx) (hg (i-a) (by omega) x hx) (mul_nonneg (pow_nonneg hs _) (norm_nonneg _)) hP) (Nat.cast_nonneg _)
  rw [← Finset.sum_mul, ← Finset.sum_mul, he]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) hP) hQ
end YM.Frontier6.Normal
#print axioms YM.Frontier6.Normal.Estimate.mul
