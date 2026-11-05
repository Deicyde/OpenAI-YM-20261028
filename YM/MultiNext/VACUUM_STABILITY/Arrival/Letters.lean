import YM.MultiNext.VACUUM_STABILITY.Arrival.Pay

set_option warningAsError false

/-!
# Analytic exponent arrivals on the actual step

Mayer complement at each regular source input, with arbitrary powers PRESENT, fixed polynomial
letters. Charge at same threshold and integer stage powers/order independent of volume, incl all
derivatives and overlap currency before spanning estimates. No order charges from unbounded
number of sources beyond this constant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Arrival
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Hits Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {V : Type} {n : Side} {F : Flock V G n} {P : BudgetPoint} {D : V→ Pulse G n}

namespace Sugar

def powerFee (k : ℕ) := k.factorial * Real.exp (Real.exp 1)
lemma power_pos (k : ℕ) : 0 < powerFee k := by unfold powerFee; positivity

lemma margined (k : ℕ) {x : ℝ} (hx : 0≤x) (he : x ≤ 1) :
    SumBudget (fun j => honey x j * ((↑(j+1:ℕ):ℝ))^k) (powerFee k*x) := by
  let E := Real.exp 1
  let f (i : ℕ) := (i.factorial:ℝ)⁻¹*E^i
  have ht := Absolute.rexp E (Real.exp_pos _).le
  have hf : SumBudget (fun i => f (i+1)) (Real.exp E) := by
    have hk := summable_nat_add_iff 1 |>.2 (show Summable f from ht.2.1)
    refine ⟨fun i => ht.1 _,hk,?_⟩
    have hg := (hasSum_nat_add_iff' 1).mpr (show Summable f from ht.2.1).hasSum
    rw [hg.tsum_eq]; exact (sub_le_self _ (sum_nonneg fun i _ => ht.1 _)).trans ht.2.2
  have hw := permit_mul hf (mul_nonneg hx (show 0 ≤ (k.factorial:ℝ) by positivity))
  have hp : x*k.factorial*Real.exp E=powerFee k*x := by unfold powerFee E; ring
  apply Absolute.loosen _ hp.le
  refine Absolute.compare hw (fun i => by unfold honey; positivity) fun i => ?_
  have hb : (↑(i+1:ℕ):ℝ)^k ≤ (k.factorial:ℝ)*Real.exp (↑(i+1:ℕ):ℝ) :=
    (inv_mul_le_iff₀ (show (0:ℝ) < k.factorial by positivity)).1
        (Absolute.little (Absolute.rexp _ (show (0:ℝ) ≤ (i+1:ℕ) by positivity)) k)
  have hI : x^(i+1) ≤ x := by rw [pow_succ]; exact mul_le_of_le_one_left hx (pow_le_one₀ hx he)
  unfold honey; calc
    _ ≤ ((↑(i+1).factorial:ℝ)⁻¹*x)*((k.factorial:ℝ)*Real.exp (i+1:ℕ)) := by gcongr
    _ = _ := by rw [show Real.exp (i+1:ℕ) = E ^(i+1) by rw [←Real.exp_nat_mul]; simp]; unfold f; ring

variable {s : Support n} {u : Config G n → ℂ}

private lemma regPow (h : P.Regular s u) (k : ℕ) : P.Regular s (u^k) := by
  induction k with
  | zero => rw [pow_zero]; exact regular_unit ..
  | succ k hk => rw [pow_succ]; exact regular_mul hk h

private lemma powerBand (h : P.Regular s u) {o : Site n} {x : ℝ} (hs : P.supBounds o s u x) {U} (ht : Healthy P.threshold s U)
    (k : ℕ) : Band P.order (P.dirBound o) U k (x^k) (u^k) := by
  have hu := into P.order u (h.smooth U ht)
  have he : Band P.order (P.dirBound o) U 1 x u :=
    ⟨hu,zero_le_one,hs.1,fun l hl hb => by simpa only [one_pow,mul_one] using hs.2 U ht l hl hb⟩
  induction k with
  | zero => simpa only [pow_zero,Nat.cast_zero] using constant_unit U (P.dirBound o) P.order
  | succ k hk => rw [Nat.cast_add,Nat.cast_one,pow_succ,pow_succ]; exact hk.multiply he

lemma reg_spice (h : P.Regular s u) (i : ℕ) : P.Regular s (fun U => spice (u U) i) := by
  convert path_scaled ((↑(i+1).factorial:ℂ)⁻¹) (regPow h (i+1)) using 1; ext U : 1; simp [spice]

lemma spicy (h : P.Regular s u) {o : Site n} {x : ℝ} (hs : P.supBounds o s u x) (k : ℕ) :
    P.supBounds o s (fun U => spice (u U) k) (honey x k * (k+1:ℕ)^P.order) := by
  have he := hs.1
  rw [show (fun U => spice (u U) k) = ((↑(k+1).factorial:ℂ)⁻¹) • u^(k+1) by ext1 U; simp [spice]]
  refine ⟨mul_nonneg (show 0≤honey x k by unfold honey; positivity) (by positivity),fun U hu l hl hb => ?_⟩
  rw [scaled_left,norm_mul,norm_inv,Complex.norm_natCast,honey,mul_assoc]
  have ht := powerBand h hs hu (k+1)
  exact mul_le_mul_of_nonneg_left ((ht.caps l hl hb).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_cast; omega) hl) ht.nonneg)) (by positivity)
end Sugar

namespace Flock
variable (F)

abbrev Power (V : Type) := Choices (Bulk V)

def penny (i : Power V) : Stamp V (Config G n) :=
    ⟨(i.2+1) • (stimulant F i.1).name, fun U => spice ((stimulant F i.1).ink U) i.2⟩

def pennyZone (i : Power V) := bulkZone F i.1

variable [Fintype V]

def raiseE (P : BudgetPoint) (z : V→ℂ) (i : Power V) :=
    honey (stipendE F z i.1) i.2 * ((↑(i.2+1:ℕ):ℝ))^P.order

lemma cast_penny (z : V→ℂ) (i : Power V) : (penny F i).tell z = fun U => spice ((stimulant F i.1).tell z U) i.2 := by
  funext U; simp only [penny,Stamp.tells,Stamp.beat_many,spice,mul_pow]; ring

lemma heated (P : BudgetPoint) (z : V→ℂ) (U : Config G n) :
    heat (fun i => masked P.threshold (bulkZone F i) ((stimulant F i).tell z) U)=
      (fun i => masked P.threshold (pennyZone F i) ((penny F i).tell z) U) := by
  funext i
  dsimp only [heat,pennyZone]
  by_cases h : Healthy P.threshold (F.bulkZone i.1) U
  · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h, cast_penny]
  rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h]; simp [spice]

namespace Attended
variable {F} {o : V → Site n} {k : V → ℝ} {κ η : ℝ} (h : Attended F P D o k κ) (z : V → ℂ) (hz : z∈allot o k η)
include h hz in
lemma pepper (he : η ≤ 1) : Locations P (pennyZone F) (fun i => o i.1.1) (raiseE F P z) (Sugar.powerFee P.order * η) ∧
    ∀ i : Power V, o i.1.1∈pennyZone F i ∧ P.Regular (pennyZone F i) (penny F i).ink ∧
        P.supBounds (o i.1.1) (pennyZone F i) ((penny F i).tell z) (raiseE F P z i) := by
  obtain ⟨hh,hA⟩:=h.issued_bulk z hz
  have hn i := (hA i).2.2.1
  constructor
  · intro x
    let f (i : Power V) := if o i.1.1=x then P.mass (pennyZone F i) (raiseE F P z i) else 0
    let a := Sugar.powerFee P.order
    let b i := stipendE F z i
    have hg := permit_mul (hh x) (Sugar.power_pos P.order).le
    let c (i : Bulk V) := a*(if o i.1=x then P.mass (bulkZone F i) (b i) else 0)
    have hp i : SumBudget (fun j => f (i,j)) (c i) := by
      unfold f c; split
      · let t : ℝ := Real.exp (P.supportExponent*coverNumber P.B (bulkZone F i))
        change SumBudget _ (a*(t*b i))
        rw [mul_left_comm a]; exact permit_mul (Sugar.margined P.order (hn i) ((hh.just hn i).trans he)) (show 0 ≤ t from (Real.exp_pos _).le)
      simp [SumBudget]
    have hm i : 0≤f i := (hp i.1).1 _
    have hv := Absolute.compare (show SumBudget c (a*η) from hg) (fun i => tsum_nonneg (hp i).1) fun i => (hp i).2.2
    have hw := (summable_prod_of_nonneg (show 0≤f from hm)).2 ⟨fun i => (hp i).2.1,hv.2.1⟩
    exact ⟨hm,hw,hw.tsum_prod.trans_le hv.2.2⟩
  intro i; obtain ⟨hv,hF,H⟩:=hA i.1
  exact ⟨hv,Sugar.reg_spice hF _, (cast_penny F z i).symm ▸ Sugar.spicy (path_scaled _ hF) H _⟩
end Attended
end Flock
end YM.Multi.Vacuum.Arrival
