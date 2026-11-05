import YM.Further.DENSE_MIXED_KERNELS.Round

/-!
# Symmetric splitting of companions, one large-event witness

Jtrid. Need full *positive-address* incidence even on a winding support.
Proof of pitch for profiles in this variant doesn't differentiate the
integral: coefficients are nonnegative with unit mass and at most one visit
per argument before the fixed product rules. Can use for both variants of
same original address. Use of rarity weights on trigger nodes separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Module Pads
open Port Gaussian Surface Tree Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {Ω ι κ : Type} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] {G : Gauge}
    {n : Side} {k : ℕ} {g w d r T : ℝ} {A : ChartRatio G} {H : Port A}
    {W : Config G n → Surface H ι κ Ω} {S : Surface H ι κ Ω}
    {U : Config G n} {P : Directions G n → Prop}

section calculus
variable {f : Config G n → ℝ}

lemma Pitch.sumReal {α : Type*} (s : Finset α) {f : α→Config G n → ℝ} {b : α → ℝ} (ht : 0 ≤ T)
    (h : ∀ i∈s,Pitch (f i) U P k (b i) T) : Pitch (fun v => ∑ i∈s, f i v) U P k (∑ i∈s,b i) T := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,norm_zero] using! Pitch.fixed (P:=P) (U:=U) (k:=k) (0:ℝ) ht
  | insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (h i (by simp)).plus (ih (fun _ hx => h _ (Finset.mem_insert_of_mem hx)))

-- Pitch for complements (with no larger price, will save for allocations).
lemma Pitch.complement (ht : 0 ≤ T) (he : 0 ≤ f U) (hp : Pitch f U P k 1 T) : Pitch (fun v => 1-f v) U P k 1 T := by
  let F (v : Config G n) := (1:ℝ)
  let L := fun v => -f v
  have hF (l : List (Directions G n)) (w : Config G n) : leftDerivs F l w = if l=[] then 1 else 0 := by
    induction l generalizing w with | nil => rfl | cons A l ih => simp only [leftDerivs,ih,List.cons_ne_nil,↓reduceIte,deriv_const]
  have hf : Ripple F U P k 0 T := ⟨contDiffAt_const,fun l hl _ _ => by rw [hF,if_neg hl,norm_zero,zero_mul]⟩
  have hL : Ripple L U P k 1 T := ⟨hp.negate.smooth,fun l _ hl hh => hp.negate.bounds l hl hh⟩
  simp_rw [sub_eq_add_neg]
  refine (hf.plus hL).parcel ht (by linarith) ?_
  have hx := (le_abs_self (f U)).trans hp.cost
  rw [Real.norm_eq_abs]; change |1+ -f U| ≤ 1; rw [abs_le]; constructor <;> linarith
end calculus
namespace Companions
open Finset
variable {α : Type*} (s t : Finset α)

def score (s t : Finset α) (x : ℝ) := (1-x)^t.card * x^(s \ t).card
def quote (s t : Finset α) := ∫ x in (0:ℝ)..1, score s t x

lemma true_share : 0 ≤ quote s t := intervalIntegral.integral_nonneg zero_le_one fun _ hx =>
    mul_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) _) (pow_nonneg hx.1 _)

variable (f : α → ℝ)
def lot (s : Finset α) (f : α → ℝ) := ∫ x in (0:ℝ)..1, ∏ j∈s, (f j+x*(1-f j))

theorem lots : lot s f = ∑ t∈s.powerset, quote s t* ∏ j∈t,f j := by
  unfold lot; let L (t:Finset α) x := score s t x * ∏ j∈t,f j
  have h x : ∏ j∈s,(f j+x*(1-f j))=∑ t∈s.powerset,L t x := by
    simp_rw [show ∀ j,f j+x*(1-f j)=(1-x)*f j+x from fun j => by ring]
    rw [prod_add (fun j => (1-x)*f j) (fun _=>x)]
    exact sum_congr rfl (fun y _ => by unfold L score; rw [prod_mul_distrib,prod_const,prod_const]; ring)
  simp_rw [h]; rw [intervalIntegral.integral_finsetSum];
  · simp only [L,quote, ← intervalIntegral.integral_mul_const]
  exact fun i _ => (show Continuous (L i) by unfold L score; fun_prop).intervalIntegrable ..

def bear (s : Finset α) (f : α → ℝ) (i : α) := (1-f i)*lot (s.erase i) f

theorem jtrid : (1- ∏ i∈s,f i)= ∑ i∈s, bear s f i := by
  let L (i : α) (x : ℝ) := f i+x*(1-f i)
  let H (x : ℝ) := ∏ i∈s,L i x
  let F i x := (1-f i)*∏ j∈s.erase i, L j x
  have hf (i : α) : Continuous (F i) := by unfold F L; fun_prop
  have hu i x : HasDerivAt (L i) (1-f i) x := by
    simpa only [one_mul,zero_add] using! ((hasDerivAt_const _ _).add ((hasDerivAt_id' x).mul_const (1-f i)))
  have hh x : HasDerivAt H (∑ i∈s,F i x) x := by
    have ht := HasDerivAt.fun_finsetProd (fun i (_:i∈s) => hu i x)
    refine (show ∑ j∈s,_=∑ j∈s,F j x from sum_congr rfl (fun i _ => mul_comm _ (1-f i))) ▸ ht
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=1) (fun v _ => hh v)
    ((continuous_finsetSum _ fun i _ => hf i).intervalIntegrable ..)
  have h₀ : H 1=1 := by unfold H; exact prod_eq_one fun i _ => by unfold L; ring
  unfold bear lot; simp_rw [← intervalIntegral.integral_const_mul]
  change _=∑ i∈s,(∫ x in (0:ℝ)..1,F i x); rw [← intervalIntegral.integral_finsetSum (fun i (_:i∈s) => (hf i).intervalIntegrable ..),h,h₀]
  simp [H,L]

lemma common : ∑ t∈s.powerset,quote s t=1 := by
  simpa [lot,sub_self] using (lots s (fun _ : α=>1)).symm
lemma lot_pitch {F : α → Config G n → ℝ} (hT : 0≤T) (hf : ∀ i∈s,Pitch (F i) U P k 1 T) : Pitch (fun v => lot s (fun i => F i v)) U P k
    1 (s.card*T) := by
  have h t (ht : t∈s.powerset) : Pitch (fun v => quote s t * ∏ i∈t,F i v) U P k (quote s t) (s.card*T) := by
    have hh := mem_powerset.mp ht
    have H : Pitch (fun v => ∏ i∈t,F i v) U P k 1 (t.card*T) := by
      simpa only [prod_const,one_pow,sum_const,nsmul_eq_mul] using product_real t (f:=F) (fun i hi => hf i (hh hi))
    have hv := Pitch.real_mul (Pitch.fixed (quote s t) (le_refl 0)) (H.mono le_rfl (show 0 ≤ t.card*T by positivity)
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hh)) hT))
    rwa [Real.norm_of_nonneg (true_share ..),mul_one,zero_add] at hv
  simp_rw [lots]; rw [← common s]; exact Pitch.sumReal _ (by positivity) h

end Companions
namespace Pads
open Companions
local notation "X" => H.front ι (H.Room κ)
variable (H) (c : Chi)

def middle (d : ℝ) (s : Finset (ι⊕κ)) (z : H.front ι (H.Room κ)) := ∏ i∈s,light H c d i z


/-- use variant only at i∈s; doesn't fabricate more data from an
empty witness set. Smooth profile (not analyticity). -/
def endCap (d : ℝ) (s : Finset (ι⊕κ)) (i : ι⊕κ) (z : H.front ι (H.Room κ)) := bear s (fun j => light H c d j z) i


omit [Fintype ι] [Fintype κ] in
theorem restores (d : ℝ) (s : Finset (ι⊕κ)) (z : H.front ι (H.Room κ)) :
    middle H c d s z + ∑ i∈s, endCap H c d s i z=1 := by
  rw [show ∑ i∈s,endCap H c d s i z = 1-middle H c d s z from (jtrid s _).symm]; ring

omit [Fintype ι] [Fintype κ] in
lemma before (s : Finset (ι⊕κ)) (hd : 0<d) {z} (h : middle H c d s z ≠ 0) :
    ∀ i∈s, ‖take H i z‖ < 2*d := fun _ hv => lt_of_not_ge fun he => h <| Finset.prod_eq_zero hv (escape c hd he)
omit [Fintype ι] [Fintype κ] in
lemma witnesses {s : Finset (ι⊕κ)} (hd : 0<d) {i z} (hv : endCap H c d s i z≠0) : d < ‖take H i z‖ := by
  by_contra! hx; unfold endCap bear at hv; dsimp only at hv; rw [show light H c d i z=1 from remains c hd hx,sub_self,zero_mul] at hv; exact hv rfl

omit [Fintype ι] [Fintype κ] in
lemma warmth (d : ℝ) (s : Finset (ι⊕κ)) (z : X) : 0≤middle H c d s z ∧ middle H c d s z≤1 := by
  have hv (i) : 0≤light H c d i z ∧ light H c d i z≤1 := scope c _
  exact ⟨Finset.prod_nonneg fun i _ => (hv i).1, Finset.prod_le_one (fun i _ => (hv i).1) (fun i _ => (hv i).2)⟩
omit [Fintype ι] [Fintype κ] in
lemma shade_bounds (d : ℝ) (s : Finset (ι⊕κ)) (z : X) (i : ι⊕κ) (_hi : i∈s) : 0 ≤ endCap H c d s i z ∧ endCap H c d s i z ≤ 1 := by
  -- use restoration even to bound any of the profiles
  have h (j) : 0 ≤ endCap H c d s j z := by
    unfold endCap bear; simp_rw [lots]
    exact mul_nonneg (sub_nonneg.mpr (scope (x:=take H j z) c _).2)
      (Finset.sum_nonneg fun t _ => mul_nonneg (true_share ..) (Finset.prod_nonneg fun i _ => (scope (x:=take H i z) c _).1))
  exact ⟨h i, (Finset.single_le_sum (fun i _ => h i) _hi).trans (by linarith only [(warmth H c d s z).1, restores H c d s z])⟩
-- Consumption at arc. keep symmetric identity costs small (1)
variable {H}
omit [MeasurableSpace Ω] in
lemma middle_pitch (s : Finset (ι⊕κ)) (hs : Shifts W U P k g T) (ht : 0≤T) (hg : 0<g) (he : g≤1)
    (hd : 1≤d) {y : Ω × H.back ι (H.Room κ)} (hp : y ∈ (W U).Perch) :
    Pitch (fun v => middle H c d s ((W v).mapUp g y).2) U P k 1 (s.card*speed H c k T) := by
  simpa only [Finset.prod_const,one_pow, Finset.sum_const, nsmul_eq_mul] using! product_real s (f:=fun i v => light H c d i
    ((W v).mapUp g y).2) fun i _ => shade c hs ht hg he hd hp i
omit [MeasurableSpace Ω] in
lemma end_pitch (s : Finset (ι⊕κ)) (hs : Shifts W U P k g T) (ht : 0≤T) (hg : 0<g) (he : g≤1)
    (hd : 1≤d) {y : Ω × H.back ι (H.Room κ)} (hp : y ∈ (W U).Perch) (i : ι⊕κ) (hi : i ∈ s) :
    Pitch (fun v => endCap H c d s i ((W v).mapUp g y).2) U P k 1 (s.card*speed H c k T) := by
  have hF := shade c hs ht hg he hd hp
  let f (i) v := light H c d i ((W v).mapUp g y).2
  have h : 0≤ f i U := (scope c d).1
  have hr := Pitch.real_mul (Pitch.complement (sunnier c k ht (H:=H)) h (hF i))
    (lot_pitch (F:=f) (s.erase i) (sunnier c k ht) fun i _ => hF i)
  rw [show s.card=(s.erase i).card+1 from (Finset.card_erase_add_one hi).symm,Nat.cast_add,Nat.cast_one,add_mul,one_mul,
    add_comm]; unfold endCap bear; rw [mul_one] at hr
  convert! hr using 1; congr!
end Pads
end YM.Further.DenseMixedKernels
