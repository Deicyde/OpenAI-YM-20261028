import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Pool

/-!
True healthy directions *at the result anchor*, paid from any designated
individual output anchor on each constituent footprint. Speeds apply once
per differentiated order, not once per factor of an unbounded connected
cluster. Catalogue costs of projection/true path length/halos & variants
of each factor go into the INDIVIDUAL hit or multiplicity budget in
addition to these tariffs, see Request.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction
open Function Filter Finset Lattice RG Wilson Precision Multi Multi.Vacuum Next.SectorChange
open MeasureTheory Gaussian Gauss
open Component Arrival Desk Stamp Jets
open scoped Topology BigOperators Classical ContDiff

namespace Toll
variable {V I J : Type} {G : Gauge} {n : Side}

def pace (R d : ℝ) [Fintype J] (l : ℕ) (z : Vec J) := R*(1+d)^l * (1+Gauss.squares z)^l

def velocity (P : BudgetPoint) (R : ℝ) := R * (1+(Hits.stride P.B:ℝ))^P.power

def order (P : BudgetPoint) (l : ℕ) := (l+P.power+1)*P.order

def degree (P : BudgetPoint) (l : ℕ) := l*P.order

def level (P : BudgetPoint) (l : ℕ) := degree P l + order P l

def transferPrice (P : BudgetPoint) (R K H : ℝ) (l : ℕ) := Gauss.coat K H (degree P l)*(velocity P R)^P.order

lemma velocity_one (P : BudgetPoint) {R : ℝ} (hr : 1≤R) : 1 ≤ velocity P R :=
    one_le_mul_of_one_le_of_one_le hr (one_le_pow₀ (by simp))
lemma pace_one {R d : ℝ} (hr : 1≤R) (hd : 0≤d) (l : ℕ) [Fintype J] (z : Vec J) : 1≤pace R d l z := by
  have hh : (0:ℝ) ≤ squares z := Schur.sumSq_nn _
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr (one_le_pow₀ (by linarith))) (one_le_pow₀ (by linarith))
lemma transfer_pos (P : BudgetPoint) (R K H : ℝ) (l : ℕ) (hr : 1≤R) (hk : 0≤K) (hh : 1≤H) : 0≤transferPrice P R K H l := by
  have ht := velocity_one P hr |>.trans' zero_le_one
  have hi := (coin_ok hk).1; have hu := hh.trans' zero_le_one; unfold transferPrice Gauss.coat; positivity

private lemma widen {P : BudgetPoint} {f : Config G n→ℂ} {o o' : Site n} {d r c : ℝ} (hd : separation o o' ≤ d*Hits.stride P.B)
    (he : 0≤d) (U : Config G n) (h : Band P.order (P.dirBound o) U r c f) :
    Band P.order (P.dirBound o') U (r*(1+(Hits.stride P.B:ℝ))^P.power * (1+d)^P.power) c f := by
  have ht : 1 ≤ (1+d*Hits.stride P.B)^P.power := one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  let t := (1+d*(Hits.stride P.B:ℝ))^P.power
  have ht' : t ≤ (1+(Hits.stride P.B:ℝ))^P.power * (1+d)^P.power := by
    rw [←mul_pow]; exact pow_le_pow_left₀ (by positivity) (by nlinarith [Nat.cast_nonneg (α:=ℝ) (Hits.stride P.B)]) _
  have ht : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hr := h.sane; have hc := h.nonneg
  refine ⟨h.readable,by positivity,hc,?_⟩
  intro v hv hV
  let k := v.map (fun u=>t⁻¹ • u)
  have hh := h.caps k (by simpa only [k,List.length_map] using hv) (by
    intro A h; obtain ⟨j,hj,rfl⟩:=List.mem_map.mp h; exact Jets.translate hd (hV _ hj))
  rw [← show k.map (fun u => t • u)=v by simp [k,ht.ne',Function.comp_def],Push.RelayDifference.left_dilate]
  rw [norm_smul_of_nonneg (pow_nonneg ht.le _),(List.length_map (as:=k))]
  change t^k.length * _ ≤ c*(r*_ * _)^k.length
  calc
    _ ≤ t^k.length*(c*r^k.length) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = c*(r*t)^k.length := by ring
    _ ≤ _ := by rw [mul_assoc]; gcongr



lemma prod_band {f : I → Config G n→ℂ} {g : I→ℝ} {r : ℝ} {k D U} {s : Finset I}
    (h : ∀ i∈s, Band k D U r (g i) (f i)) : Band k D U (∑ _ ∈ s, r) (∏ i∈s,g i) (∏ i∈s, f i) := by
  induction s using Finset.induction with
  | empty => simp only [sum_empty,prod_empty]; exact constant_unit U _ k
  | insert i s hi ih =>
    simp only [sum_insert hi,prod_insert hi]
    exact (h _ (by simp)).multiply (ih fun j hj => h j (mem_insert_of_mem hj))

variable {B : Brush V G n} (A : Pasture I B)

def volume (P : BudgetPoint) (s : Fruit) : ℝ := (∑ j∈A.bud s,Lattice.coverNumber P.B (A.sites j):ℕ)

lemma volume_pos (P : BudgetPoint) (s : Fruit) : 0 ≤ volume A P s := Nat.cast_nonneg _
lemma covers (P : BudgetPoint) (s : Fruit) : (coverNumber P.B (ends B s):ℝ) ≤ volume A P s := by
  rw [A.lives]; unfold volume; exact_mod_cast Ac.cover A.sites P.B (A.connected s)
lemma counts (P : BudgetPoint) (s : Fruit) : ((A.bud s).card:ℝ) ≤ volume A P s := by
  unfold volume; gcongr
  rw [Finset.card_eq_sum_ones]; exact sum_le_sum fun j _ => Hits.cover_pos _ _ (A.origin j)
lemma distance (P : BudgetPoint) (s : Fruit) {x y : Site n} (hx : x∈ends B s) (hy : y∈ends B s) :
    (separation x y : ℝ) ≤ volume A P s * Hits.stride P.B := by
  refine le_trans (b:=(↑(coverNumber P.B (ends B s) * Hits.stride P.B) : ℝ)) (by exact_mod_cast Hits.distance _ P.B hx hy) ?_
  rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_right (covers A P s) (Nat.cast_nonneg _)

/- Post-L polynomial losses, including kernel itself as a differentiated factor. -/
theorem stretched (P : BudgetPoint) [Fintype J] (z : Vec J) (s : Fruit) (a : Site n) (U : Config G n) (R : ℝ) (l : ℕ) (hr : 1≤R)
    (ha : a ∈ ends B s) (f : Config G n→ℂ) (g : I → Config G n→ℂ) (c : ℝ) (w : I→ℝ)
    (hf : Band P.order (P.dirBound a) U (pace R (volume A P s) l z) c f)
    (hg : ∀ i∈A.bud s, ∃ x∈ ends B s,Band P.order (P.dirBound x) U (pace R (volume A P s) l z) (w i) (g i)) :
    ∀ v:List (Directions G n), v.length≤P.order → (∀ D∈v,P.dirBound a D) →
    ‖leftDerivs (f * ∏ i∈A.bud s, g i) v U‖ ≤ c*((velocity P R)^P.order * (1+volume A P s)^order P l *
      (1+squares z)^degree P l * ∏ i∈A.bud s,w i) := by
  let d := volume A P s
  have hd := volume_pos A P s
  let r := pace R d l z
  let w' := r*(1+ (Hits.stride P.B:ℝ))^P.power*(1+d)^P.power
  let t := velocity P R*(1+d)^(l+P.power+1)*(1+squares z)^l
  have hG (i) (hi : i∈A.bud s) : Band P.order (P.dirBound a) U w' (w i) (g i) := by
    obtain ⟨x,hx,hb⟩ := hg i hi; exact widen (distance A P s hx ha) hd U hb
  have hD : 0≤d:=hd
  have hR : 0≤R := zero_le_one.trans hr
  have hz : 0≤squares z := Schur.sumSq_nn _
  have hh : 1≤r := pace_one hr hD l _
  have hu : 1 ≤ (1+ (Hits.stride P.B:ℝ))^P.power*(1+d)^P.power := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by simp)) (one_le_pow₀ (by linarith))
  have hw : r ≤ w' := by unfold w'; rw [mul_assoc]; exact le_mul_of_one_le_right (hf.sane) hu
  have ht : 0≤w' := (hf.sane.trans hw)
  have heq : w' + d*w' = t := by unfold t w' r pace velocity; ring
  have ht' : 1≤t := by linarith [add_nonneg (sub_nonneg.mpr (hh.trans hw)) (mul_nonneg hD ht)]
  intro v hv hV
  have hb := hf.multiply (prod_band hG)
  have hs : r + ∑ _ ∈ A.bud s, w' ≤ t := by
    rw [← heq, sum_const, nsmul_eq_mul]; exact add_le_add hw (mul_le_mul_of_nonneg_right (counts A P s) ht)
  refine ((hb.caps v hv hV).trans (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hb.sane hs _).trans
    (pow_le_pow_right₀ ht' hv)) hb.nonneg)).trans_eq ?_
  unfold t order degree d; rw [mul_pow,mul_pow,← pow_mul,← pow_mul]; ring
end Toll
end YM.ProofPorts.CommonComplexProduction
