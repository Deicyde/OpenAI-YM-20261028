import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Arias

/-!
# Slot budgets through upward radius changes

Geometry at every old-scale step between launch and redemption. No h-bands
here. Ergodic layout cannot change based on calibration at basis prices.
Does not assume boot on the resulting mounted stencils.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Weaver
open Lattice Wilson Pressure RG MeasureTheory Function Matrix Finset Next.SectorChange
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid Precision Display Edition Thirst  Alarm
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side} {t r e p q z : ℝ} {V ι κ ω : Type} [Fintype V] [DecidableEq V] {c : V→Site n}
section inflation
variable (Q : BudgetPoint)
local notation "F" => -(Q.B:ℝ)/128
lemma pays_curve (X : Support n) (s : modes V) (h : Edition.Spaced Q.B c) (hf : 2 ≤ s.val.card) (hv : ∀ i, i∈s.val→ c i∈ X) (hb : 8≤ Q.B) (hr : 0≤r)
    (ht : t ≤ Real.exp ((Q.B:ℝ)/256)*r) (ht' : 0≤t) : Value.charge Q Q.supportExponent X*Poly.toll (fun _=>t) s ≤ Real.exp F*(Value.charge Q (Q.supportExponent+1) X*Poly.toll (fun _=>r) s) :=by
  have hx := count_cost Q X s h hf hv hb; let m:=s.val.card; let C:= coverNumber Q.B X
  have hz :(Q.B:ℝ)*(m:ℝ) ≤64*C:=by exact_mod_cast hx
  unfold Value.charge
  let q:= Q.supportExponent; let b:ℝ := (Q.B:ℝ)/256
  change Real.exp (q*↑C)* _≤ Real.exp F*(Real.exp ((q+1)*↑C) * _)
  have ha : Poly.toll (fun _=>t) s ≤ Real.exp ((m:ℝ)*b)*r^m:= by
    simp only [Poly.toll,prod_const]; apply le_trans (pow_le_pow_left₀ ht' ht m); rw [mul_pow,←Real.exp_nat_mul]
  have he : q*(C:ℝ)+(m:ℝ)*b≤ F+(q+1)*↑C:= by
    have hp:(1:ℝ)≤m:= Nat.one_le_cast.mpr (by unfold m;omega)
    unfold b; linarith only [hz,mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α:=ℝ) Q.B)]
  simp only [Poly.toll,prod_const] at *
  apply (mul_le_mul_of_nonneg_left ha (Real.exp_pos _).le).trans
  rw [← mul_assoc _ _ (r^m),←Real.exp_add,←mul_assoc _ _ (r^s.val.card), ←Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone he) (pow_nonneg hr _)
variable {H : ι→SourceAt G c}
    [Fintype ι] [Fintype κ]
private lemma purse {ι : Type} [Fintype ι] {ζ : ι→Prop} [DecidablePred ζ] (Q : ι→Prop) [DecidablePred Q]
    {y p : ℝ} {f:ι→ℝ} (hp : 0≤p) (h : ∀ i,0≤f i) (hf : (∑ i,if Q i then f i else 0)≤y) : (∑ i:{i// ζ i},if Q i then p*f i else 0) ≤ p*y:=by
  apply (le_trans _ (mul_le_mul_of_nonneg_left hf hp)); rw [Finset.mul_sum];let K i:= if Q i then p*f i else 0
  change (∑ i:{i//ζ i},K i)≤_; rw [← Finset.sum_subtype (univ.filter ζ) (show ∀ i,i∈univ.filter _↔ζ i from fun i=>by simp) K]; apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (f:=K) (subset_univ _) (fun i _ _=>by unfold K;split; exact mul_nonneg hp (h _); exact le_rfl)); apply Finset.sum_le_sum; intro i _; unfold K; split <;> first|rfl|skip
  simp
lemma ferveur {T : Rep G n} {K : κ→Lifted G c T.p.threshold} (hb : 8≤ T.p.B) (h : Spaced T.p.B c) (hr : 0≤r) (ht : 0≤t) (he : t ≤ Real.exp ((T.p.B:ℝ)/256)*r)
    (hp : Light T H K (fun _=> r) (T.p.supportExponent+1) p q) -- adjust
    : Light T (fun i : Priced H=>H i.val) (fun i:Piqued K=>K i.val) (fun _=>t) T.p.supportExponent (Real.exp (-(T.p.B:ℝ)/128)*p) (Real.exp (-(T.p.B:ℝ)/128)*q):=by
  let Q := T.p
  obtain ⟨⟨v,hv,h⟩,⟨a,ha,hV⟩⟩:= hp
  have hz:0≤Real.exp (-(T.p.B:ℝ)/128):= (Real.exp_pos _).le
  constructor
  · refine ⟨fun i=>Real.exp (-(T.p.B:ℝ)/128)*v i.val,fun i=>⟨mul_nonneg hz (hv i.val).1,fun U hU=>?_⟩,fun i=>?_⟩
    · apply le_trans _ (mul_le_mul_of_nonneg_left ((hv i.val).2 _ hU) hz); rw [← mul_assoc (Real.exp (-(T.p.B:ℝ)/128))]
      apply mul_le_mul_of_nonneg_right (pays_curve Q (H i.val).extent (H i.val).fires (by assumption) i.property (H i.val).remembers hb hr he ht) (norm_nonneg _)
    exact purse (fun j=> i∈(H j).fires.val) hz (fun j=>(hv _).1) (h _)
  refine ⟨fun i=>Real.exp (-(T.p.B:ℝ)/128)*a i.val,fun i=> ⟨mul_nonneg hz (ha i.val).1,fun U=>?_⟩,fun i=>?_⟩
  · apply le_trans _ (mul_le_mul_of_nonneg_left ((ha i.val).2 U) hz); rw [← mul_assoc (Real.exp (-(T.p.B:ℝ)/128))]; exact mul_le_mul_of_nonneg_right (pays_curve Q (K i.val).extent (K i.val).fires (by assumption) i.property (K i.val).remembers hb hr he ht) (norm_nonneg _)
  exact purse (fun j=>i∈(K j).extent) hz (fun i=>(ha _).1) (hV _)
end inflation
end YM.PhysicalNext.InteractingRank.Weaver
