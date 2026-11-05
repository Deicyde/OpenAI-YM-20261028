import YM.RG08.Arc.Chamber
import YM.PertExtension.PTBills

/-! # Fitting auxiliary jets (no control between periods). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter Set Metric MeasureTheory YM.PertExtension.Series.Tested
open YM.PertExtension.Series.Radial
open scoped BigOperators Topology Real ContDiff Classical
variable {f g p q r : ℝ→ℝ} {n k m : ℕ} {ι : Type*}
abbrev Fit (n : ℕ) (f g : ℝ → ℝ) : Prop := Bill n (f-g)
@[refl] lemma Fit.same (p n) : Fit n p p := ⟨0,by simp,Eventually.of_forall (by simp)⟩
lemma Fit.turn (h : Fit n f g) : Fit n g f := by rw [Fit, ← neg_sub f]; exact bill_neg h
lemma Fit.join (h : Fit n f g) (hp : Fit n g r) : Fit n f r := by rw [Fit,← sub_add_sub_cancel f g]; exact bill_add h hp
lemma Fit.pair (h : Fit n f g) (hp : Fit n p q) : Fit n (f+p) (g+q) := by rw [Fit,show f+p-(g+q)=f-g+(p-q) by abel]; exact bill_add h hp
lemma Fit.negate (h : Fit n f g) : Fit n (-f) (-g) := by rw [Fit,show -f- -g= -(f-g) by abel]; exact bill_neg h
lemma Fit.less (h : Fit n f g) (hp : Fit n p q) : Fit n (f-p) (g-q) := by simpa only [sub_eq_add_neg] using! h.pair hp.negate
lemma Fit.list {f g : ι→ ℝ→ℝ} {s : Finset ι} (h : ∀ i∈s,Fit n (f i) (g i)) : Fit n (∑ i∈s,f i) (∑ i∈s,g i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty,Finset.sum_empty]; exact Fit.same ..
  | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self _ _)).pair (ih (fun j hj=> h _ (Finset.mem_insert_of_mem hj)))
lemma Fit.emp {f g : ι→ ℝ→ℝ} {s : Finset ι} (h : ∀ i∈s,Fit n (f i) (g i)) : Fit n (fun t=>∑ i∈s, f i t) (fun t=>∑ i∈s, g i t) := by
  have hv (f : ι→ℝ→ℝ) : (∑ i∈s,f i)=(fun t=> ∑ i∈s,f i t) := funext (fun i => Finset.sum_apply i ..)
  rw [← hv, ← hv]; exact Fit.list h
lemma Fit.supply (h : f=ᶠ[𝓝[>]0]g) (n : ℕ) : Fit n f g := ⟨0,le_rfl,h.mono fun x hx=> by simp [hx]⟩
lemma Fit.havePay (hp : Fit n f g) (h : Bill k g) (hz : k≤n) : Bill k f := by simpa only [sub_add_cancel] using! bill_add (f:=f-g) (bill_ge hp hz) h
lemma Fit.scale (h : Fit n f g) (c : ℝ) : Fit n (c • f) (c • g) := by unfold Fit; rw [← smul_sub]; exact bill_flip (n:=n) (by convert bill_mul (bill_const c) h <;> first|rfl|simp) EventuallyEq.rfl
lemma Fit.left (h : Fit n f g) (hx : Bill k p) : Fit (n+k) (f*p) (g*p) := by unfold Fit; rw [← sub_mul]; exact bill_mul h hx
lemma Fit.right (h : Fit n f g) (hx : Bill k p) : Fit (k+n) (p*f) (p*g) := by unfold Fit; rw [← mul_sub]; exact bill_mul hx h
lemma Fit.lower (h : Fit n f g) (he : k≤n) : Fit k f g := bill_ge h he
lemma Fit.groups (h : Fit n f g) (hp : Fit n p q) (hh : Bill 0 g) (he : Bill 0 q) : Fit n (f*p) (g*q) := (h.left (hp.havePay he (Nat.zero_le _))).join (by rw [← show 0+n=n from zero_add n]; exact hp.right hh)
lemma Fit.toSave (hp : Bill n f) : Fit n f 0 := by unfold Fit; rw [sub_zero]; exact hp
lemma Fit.shorten (h : Fit (n+k) f g) : Fit n (fun t=> f t/t^k) (fun t=> g t/t^k) := by
  obtain ⟨C,hC,H⟩:=h; refine ⟨C,hC,?_⟩
  filter_upwards [H,eventually_pos] with t h ht
  rw [Pi.sub_apply, ← sub_div,norm_div, Real.norm_eq_abs (t^k), abs_of_pos (pow_pos ht _)]; exact (div_le_iff₀ (pow_pos ht _)).2 (h.trans_eq (by rw [pow_add,mul_assoc])) -- norm_pi sub at h defeq

lemma life_price {α : Type*} [NormedAddCommGroup α] {f : ℝ→α} {b : α} (h : Tendsto f (𝓝[>]0) (𝓝 b)) : Bill 0 f :=
  ⟨‖b‖+1,by positivity, (h.norm.eventually (isOpen_Iio.mem_nhds (show ‖b‖<‖b‖+1 by linarith))).mono fun t ht=> by rw [pow_zero,mul_one]; exact le_of_lt ht⟩
lemma exponentiated {c x y : ℝ} (hx : ‖x‖≤c)(hy : ‖y‖≤c) :
    Real.exp (-c)*‖x-y‖ ≤ ‖Real.exp x-Real.exp y‖ ∧ ‖Real.exp x-Real.exp y‖ ≤ Real.exp c*‖x-y‖ := by
  have hp (x y : ℝ) (h : y≤x) (hx : ‖x‖≤c)(hy : ‖y‖≤c) : Real.exp (-c)*‖x-y‖ ≤ ‖Real.exp x-Real.exp y‖ ∧ ‖Real.exp x-Real.exp y‖ ≤ Real.exp c*‖x-y‖ := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr h),Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h))]; refine ⟨?_,?_⟩
    · calc
        _ ≤ Real.exp y*(x-y) := by gcongr; exact (abs_le.mp hy).1
        _ ≤ _ := by have H := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x-y)) (Real.exp_pos y).le; rw [← Real.exp_add,add_sub_cancel ..] at H; linarith -- maybe add_sub_cancel_left
    calc
      _ ≤ Real.exp x*(x-y) := by have H:= mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y-x)) (Real.exp_pos x).le; rw [← Real.exp_add,add_sub_cancel ..] at H; linarith
      _ ≤ _ := by gcongr; exact (abs_le.mp hx).2
  rcases le_total y x with h | h; · exact hp x y h hx hy
  rw [norm_sub_rev x,norm_sub_rev (Real.exp x)]; exact hp y x h hy hx
lemma Fit.elevate (h : Fit n f g) (hx : Bill 0 g) : Fit n (Real.exp∘f) (Real.exp∘g) := by
  obtain ⟨C,hC,hP⟩:=h.havePay hx (Nat.zero_le _)
  obtain ⟨D,hD,hZ⟩:=hx; obtain ⟨B,hB,hS⟩:=h; refine ⟨Real.exp (max C D)*B,by positivity,?_⟩
  filter_upwards [hP,hZ,hS] with t ht hD hM
  change ‖Real.exp _ - Real.exp _‖ ≤ _; rw [mul_assoc]; exact (exponentiated ((show ‖f t‖ ≤ C by simpa using ht).trans (le_max_left C D)) ((show ‖g t‖ ≤ D by simpa using hD).trans (le_max_right ..))).2.trans (mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le)
lemma Fit.unelevate (h : Fit n (Real.exp∘f) (Real.exp∘g)) (hp : Bill 0 f) (hx : Bill 0 g) : Fit n f g := by
  obtain ⟨C,hC,hP⟩:=hp
  obtain ⟨D,hD,hZ⟩:=hx; obtain ⟨B,hB,hS⟩:=h; refine ⟨B/Real.exp (-max C D),by positivity,?_⟩
  filter_upwards [hP,hZ,hS] with t ht hD hM
  change ‖f t-g t‖ ≤ B/_* t^n; rw [div_mul_eq_mul_div]; apply (le_div_iff₀ (Real.exp_pos _)).2; rw [mul_comm]; exact (exponentiated ((show ‖f t‖ ≤ C by simpa using ht).trans (le_max_left C D)) ((show ‖g t‖ ≤ D by simpa using hD).trans (le_max_right ..))).1.trans hM
end YM.RG08.Reflect
