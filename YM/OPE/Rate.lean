import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential rates for fixed families of collapsing scales

Cost calculus with *eventual* bounds. Allows more than one collapsing scale; a close pair
might be at `log(1/separation) = b*T + o(T)`, `b` larger than the outer scale's rate `a`.
This accounting doesn't cost a whole extra power at transitions in a fixed (positive)
log-rate layer. `Envelope` and `Dominated` mean something else in the Wilson library.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter
open scoped Topology BigOperators
variable {ι ι' X Y : Type*}

/-- Upper exponential rate `a`. The time variable will tend to +∞.
Using ‖·‖ instead of log‖·‖ also admits arbitrarily small or vanishing amplitudes. -/
def RateLE [Norm X] (l : Filter ι) (T : ι → ℝ) (f : ι → X) (a : ℝ) : Prop :=
  ∀ r : ℝ, a < r → ∀ᶠ i in l, ‖f i‖ ≤ Real.exp (r*T i)

/-- Exact exponential rate of an eventually positive real function. -/
structure RateIs (l : Filter ι) (T : ι → ℝ) (f : ι → ℝ) (a : ℝ) : Prop where
  pos : ∀ᶠ i in l, 0 < f i
  rate : Tendsto (fun i => Real.log (f i) / T i) l (𝓝 a)

variable {l l₂ : Filter ι} {l' : Filter ι'} {T f g : ι → ℝ} {a b c : ℝ}

namespace RateLE
variable {F F' : ι → X} {G : ι → Y}

section
variable [Norm X] (h : RateLE l T F a)
include h
lemma mono (hx : a ≤ b) : RateLE l T F b := fun r hr => h r (lt_of_le_of_lt hx hr)
lemma shrink (hx : l₂ ≤ l) : RateLE l₂ T F a := fun r hr => (h r hr).filter_mono hx
lemma comp {φ : ι' → ι} (hφ : Tendsto φ l' l) : RateLE l' (T ∘ φ) (F ∘ φ) a :=
  fun r hr => hφ.eventually (h r hr)
lemma congr (hx : F =ᶠ[l] F') : RateLE l T F' a := by
  intro r hr; filter_upwards [h r hr,hx] with i hi he; rwa [← he]
lemma transfer [Norm Y] (hx : ∀ᶠ i in l, ‖G i‖ ≤ ‖F i‖) : RateLE l T G a :=
  fun r hr => (hx.and (h r hr)).mono fun _ hi => hi.1.trans hi.2
end

lemma norm [SeminormedAddGroup X] (h : RateLE l T F a) : RateLE l T (fun i => ‖F i‖) a :=
  h.transfer (Eventually.of_forall fun i => by simp)

lemma zero [SeminormedAddGroup X] (l : Filter ι) (T : ι → ℝ) (a : ℝ) :
    RateLE l T (fun _ => (0:X)) a := by intro r _; simp [Real.exp_nonneg]

lemma add [SeminormedAddGroup X] (h : RateLE l T F a) (hh : RateLE l T F' a)
    (hT : Tendsto T l atTop) : RateLE l T (fun i => F i+F' i) a := by
  intro r hr; obtain ⟨s,hs,hs'⟩ := exists_between hr
  filter_upwards [h s hs,hh s hs, (Real.tendsto_exp_atTop.comp (hT.const_mul_atTop (sub_pos.mpr hs'))).eventually_ge_atTop 2] with i hx hy he
  apply (norm_add_le _ _).trans
  calc _ ≤ 2*Real.exp (s*T i) := (add_le_add hx hy).trans_eq (two_mul _).symm
       _ ≤ Real.exp ((r-s)*T i)*Real.exp (s*T i) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
       _ = _ := by rw [← Real.exp_add,sub_mul, sub_add_cancel]

lemma addMax [SeminormedAddGroup X] (h : RateLE l T F a) (hh : RateLE l T F' b)
    (hT : Tendsto T l atTop) : RateLE l T (fun i => F i+F' i) (max a b) :=
  (h.mono (le_max_left _ _)).add (hh.mono (le_max_right _ _)) hT

lemma neg [SeminormedAddGroup X] (h : RateLE l T F a) : RateLE l T (fun i => - F i) a :=
  h.transfer (Eventually.of_forall fun _ => by simp)

lemma sub [SeminormedAddGroup X] (h : RateLE l T F a) (hh : RateLE l T F' a)
    (hT : Tendsto T l atTop) : RateLE l T (fun i => F i-F' i) a := by
  simpa only [sub_eq_add_neg] using h.add hh.neg hT

lemma sum [SeminormedAddCommGroup X] {S : Finset Y} {f : Y → ι → X}
    (hT : Tendsto T l atTop) (h : ∀ x ∈ S, RateLE l T (f x) a) :
    RateLE l T (fun i => ∑ x ∈ S, f x i) a := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using RateLE.zero (X:=X) l T a
  | insert x s hx ih => simpa only [Finset.sum_insert hx] using
      (h x (Finset.mem_insert_self ..)).add (ih (fun y hy => h _ (Finset.mem_insert_of_mem hy))) hT

variable {Z : Type*}
lemma bil [SeminormedAddGroup X] [SeminormedAddGroup Y] [Norm Z] (h : RateLE l T F a)
    (hh : RateLE l T G b) {u : ι → Z} (hu : ∀ᶠ i in l, ‖u i‖ ≤ ‖F i‖*‖G i‖) :
    RateLE l T u (a+b) := by
  intro r hr; obtain ⟨s,hs,hs'⟩ := exists_between (lt_sub_iff_add_lt.mpr hr)
  filter_upwards [h s hs,hh (r-s) (by linarith),hu] with i hx hy ht
  exact ht.trans ((mul_le_mul hx hy (norm_nonneg _) (Real.exp_nonneg _)).trans_eq (by
    rw [← Real.exp_add, sub_mul]; ring_nf))

lemma mul [SeminormedRing X] (h : RateLE l T F a) (hh : RateLE l T F' b) :
    RateLE l T (fun i => F i*F' i) (a+b) := h.bil hh (Eventually.of_forall fun _ => norm_mul_le _ _)

lemma smul [NormedField X] [SeminormedAddCommGroup Y] [NormedSpace X Y]
    (h : RateLE l T F a) (hh : RateLE l T G b) : RateLE l T (fun i => F i • G i) (a+b) :=
  h.bil hh (Eventually.of_forall fun _ => norm_smul_le _ _)

lemma absBound [Norm X] (A : ℝ) (hT : Tendsto T l atTop) (h : ∀ᶠ i in l, ‖F i‖ ≤ A) :
    RateLE l T F 0 := by
  intro r hr
  filter_upwards [h, (Real.tendsto_exp_atTop.comp (hT.const_mul_atTop hr)).eventually_ge_atTop A]
    with i hi hx using hi.trans hx

lemma const [Norm X] (x : X) (hT : Tendsto T l atTop) : RateLE l T (fun _ => x) 0 :=
  absBound ‖x‖ hT (Eventually.of_forall fun _ => le_rfl)

lemma pow [SeminormedRing X] (n : ℕ) (h : RateLE l T F a) (hT : Tendsto T l atTop) :
    RateLE l T (fun i => (F i)^n) (n*a) := by
  induction n with
  | zero => simpa using RateLE.const (1:X) hT
  | succ n ih => simpa only [pow_succ,Nat.cast_add_one,add_mul,one_mul] using ih.mul h

lemma prod [SeminormedCommRing X] {S : Finset Y} {r : Y → ℝ} {f : Y → ι → X}
    (hT : Tendsto T l atTop) (h : ∀ x ∈ S, RateLE l T (f x) (r x)) :
    RateLE l T (fun i => ∏ x ∈ S, f x i) (∑ x ∈ S,r x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using RateLE.const (1:X) hT
  | insert x s hx ih => simpa only [Finset.prod_insert hx,Finset.sum_insert hx] using
      (h x (Finset.mem_insert_self ..)).mul (ih fun y hy => h y (Finset.mem_insert_of_mem hy))

lemma tends [SeminormedAddGroup X] (h : RateLE l T F a) (ha : a < 0) (hT : Tendsto T l atTop) :
    Tendsto F l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨b,hb,hb'⟩ := exists_between ha
  exact squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) (h b hb)
    (Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg hb' hT))

lemma of_norm_le [Norm X] (h : RateLE l T f a) (he : ∀ᶠ i in l, ‖F i‖ ≤ f i) : RateLE l T F a :=
  h.transfer (he.mono fun _ hx => hx.trans (Real.le_norm_self _))

lemma exp (a : ℝ) (hT : Tendsto T l atTop) : RateLE l T (fun i => Real.exp (a*T i)) a := by
  intro r hr; filter_upwards [hT.eventually_ge_atTop 0] with i hi
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_monotone (mul_le_mul_of_nonneg_right hr.le hi)
end RateLE

namespace RateIs
lemma comp {φ : ι' → ι} (h : RateIs l T f a) (hφ : Tendsto φ l' l) :
    RateIs l' (T ∘ φ) (f ∘ φ) a := ⟨hφ.eventually h.pos,h.rate.comp hφ⟩
lemma shrink (h : RateIs l T f a) (hx : l₂ ≤ l) : RateIs l₂ T f a :=
  ⟨h.pos.filter_mono hx,h.rate.mono_left hx⟩
lemma congr (h : RateIs l T f a) (hx : f =ᶠ[l] g) : RateIs l T g a := by
  refine ⟨?_,h.rate.congr' ?_⟩
  · filter_upwards [h.pos,hx] with i hi he; rwa [← he]
  filter_upwards [hx] with i hi; rw [hi]
lemma mul (h : RateIs l T f a) (hh : RateIs l T g b) : RateIs l T (fun i => f i*g i) (a+b) := by
  refine ⟨(h.pos.and hh.pos).mono fun _ hi => mul_pos hi.1 hi.2,(h.rate.add hh.rate).congr' ?_⟩
  filter_upwards [h.pos,hh.pos] with i hf hg; rw [Real.log_mul hf.ne' hg.ne',add_div]
lemma inv (h : RateIs l T f a) : RateIs l T (fun i => (f i)⁻¹) (-a) := by
  refine ⟨h.pos.mono fun _ hx => inv_pos.mpr hx,h.rate.neg.congr ?_⟩
  intro i; rw [Real.log_inv,neg_div]
lemma div (h : RateIs l T f a) (hh : RateIs l T g b) : RateIs l T (fun i => f i/g i) (a-b) := by
  simpa only [div_eq_mul_inv,sub_eq_add_neg] using h.mul hh.inv
lemma rpow (h : RateIs l T f a) (x : ℝ) : RateIs l T (fun i => f i ^ x) (x*a) := by
  refine ⟨h.pos.mono fun _ hx => Real.rpow_pos_of_pos hx _,(h.rate.const_mul x).congr' ?_⟩
  filter_upwards [h.pos] with i hi; rw [Real.log_rpow hi, mul_div_assoc]
lemma power (h : RateIs l T f a) (n : ℕ) : RateIs l T (fun i => f i ^ n) (n*a) := by
  simpa only [Real.rpow_natCast] using h.rpow n
lemma const (hT : Tendsto T l atTop) (hp : 0<c) : RateIs l T (fun _ => c) 0 :=
  ⟨Eventually.of_forall fun _ => hp,tendsto_const_nhds.div_atTop hT⟩
lemma exp' (h : Tendsto (fun i => f i/T i) l (𝓝 a)) : RateIs l T (fun i => Real.exp (f i)) a := by
  refine ⟨Eventually.of_forall fun _ => Real.exp_pos _,h.congr ?_⟩
  intro i; rw [Real.log_exp]
lemma exp (a : ℝ) (hT : Tendsto T l atTop) : RateIs l T (fun i => Real.exp (a*T i)) a := by
  apply exp'; apply tendsto_const_nhds.congr'
  filter_upwards [hT.eventually_gt_atTop 0] with i hi
  rw [mul_div_cancel_right₀ _ hi.ne']
lemma pays (h : RateIs l T f a) (hT : Tendsto T l atTop) : RateLE l T f a := by
  intro r hr
  filter_upwards [h.rate.eventually (gt_mem_nhds hr),hT.eventually_gt_atTop 0,h.pos] with i hi ht hf
  rw [Real.norm_of_nonneg hf.le]
  exact Real.le_exp_of_log_le ((div_le_iff₀ ht).mp hi.le)
lemma outweigh [Norm X] {F : ι → X} (h : RateIs l T f a) (hh : RateLE l T F b)
    (hab : b < a) (hT : Tendsto T l atTop) : ∀ᶠ i in l, ‖F i‖ ≤ f i := by
  obtain ⟨s,hs,hs'⟩ := exists_between hab
  filter_upwards [h.pos,hh s hs,h.rate.eventually (lt_mem_nhds hs'),hT.eventually_gt_atTop 0] with i hf hi hg ht using
    hi.trans ((Real.le_log_iff_exp_le hf).mp ((le_div_iff₀ ht).mp hg.le))
lemma of_sandwich {f' : ι → ℝ} (h : RateIs l T f a) (hh : RateLE l T f' a) (hg : ∀ᶠ i in l, f i ≤ g i)
    (hj : ∀ᶠ i in l, g i ≤ f' i) (hT : Tendsto T l atTop) : RateIs l T g a := by
  have hp := (hg.and h.pos).mono fun i he => he.2.trans_le he.1
  refine ⟨hp,tendsto_order.mpr ⟨fun r hr => ?_,fun r hr => ?_⟩⟩
  · filter_upwards [h.rate.eventually (lt_mem_nhds hr),hg,hT.eventually_gt_atTop 0,h.pos] with i hi hg ht hf
    exact hi.trans_le (div_le_div_of_nonneg_right (Real.log_le_log hf hg) ht.le)
  obtain ⟨s,hs,hs'⟩ := exists_between hr
  filter_upwards [hh s hs,hj,hT.eventually_gt_atTop 0,hp] with i hi hg ht hf
  rw [div_lt_iff₀ ht]
  exact ((Real.log_le_iff_le_exp hf).mpr (hg.trans ((Real.le_norm_self _).trans hi))).trans_lt (mul_lt_mul_of_pos_right hs' ht)
lemma add (h : RateIs l T f a) (hh : RateIs l T g b) (hT : Tendsto T l atTop) :
    RateIs l T (fun i => f i+g i) (max a b) := by
  have hp := (h.pays hT).addMax (hh.pays hT) hT
  rcases le_total b a with he|he
  · refine of_sandwich (max_eq_left he |>.symm ▸ h) hp ?_ (Eventually.of_forall fun i => le_rfl) hT
    filter_upwards [hh.pos] with i hi using le_add_of_nonneg_right hi.le
  refine of_sandwich (max_eq_right he |>.symm ▸ hh) hp ?_ (Eventually.of_forall fun i => le_rfl) hT
  filter_upwards [h.pos] with i hi using le_add_of_nonneg_left hi.le
lemma tends (h : RateIs l T f a) (ha : a < 0) (hT : Tendsto T l atTop) : Tendsto f l (𝓝 0) :=
  (h.pays hT).tends ha hT
end RateIs
end YM.OPE
