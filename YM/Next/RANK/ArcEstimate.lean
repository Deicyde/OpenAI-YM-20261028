import YM.Next.RANK.BoundParticle
import YM.Next.RANK.Scars
import YM.Next.RANK.Sky

/-!
# Vertex and two-point sampling bounds on lifted stencil

Need only high-high/low comparisons before decomposing simultaneously. Budgets
use one λ per endpoint, compare kernel to projected continuum as real. Includes
low 0≤ order. No claim of symbolic C-pure beyond these differences. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Beamer
open Lattice CellsInt Function Configuration Labels Rise Particle Common Finset Normal
open scoped Classical Topology BigOperators

variable {G : Gauge} {d n k T : ℕ} {S : Type*}

variable (d) (f : S → Address G) (r : ℝ)

-- weight of remainder at d+1 when d≥2; d=1 also compatible, d=0 weaker.

def fee (i : KeyIn G d) := ∑ a, ‖glimpse i a‖
def sensed (d : ℕ) (B : ℝ) := ∀ i : KeyIn G d, fee d i ≤ B

lemma sense (G : Gauge) (d : ℕ) : ∃ B : ℝ, 1 ≤ B ∧ sensed (G:=G) d B := by
  have ht (i : KeyIn G d) : 0 ≤ fee d i := sum_nonneg fun i _ => norm_nonneg _
  refine ⟨(∑ i : KeyIn G d, fee d i)+1,by linarith only [show 0 ≤ ∑ i : KeyIn G d, fee d i from sum_nonneg fun i _ => ht i], fun i => ?_⟩
  exact (single_le_sum (f:=fee d) (fun i _ => ht i) (mem_univ i)).trans (le_add_of_nonneg_right zero_le_one)

def attends (d : ℕ) (M : ℕ) (L : Degree G) :=
    (L.point=0 ∧ L.degree+2≤d) ∨ (L.degree=d-1 ∧ street L.point ≤ M)

def amount (r : ℝ) (L : Degree G) := r^(L.degree+2)
def Gather (B : ℝ) (M : ℕ) (F : Horizon G) := shutter F ∧ ∀ L : Degree G,attends d M L → amount r L * ‖gesture L F‖≤B

def Drift (E : ℝ) (F : Horizon G) := ∀ L : Hub G d 0, amount r L.val* ‖gesture L.val F‖ ≤ E

variable {d r}
lemma fares (hr : 1≤r) (B : ℝ) (he : 0≤B) (v : Horizon G) (x : KeyIn G d) (E : ℝ) (hE : sensed (G:=G) d E)
    (h : Drift d r B v) : ‖passcode f r d (.inl x) v‖ ≤ B*E := by
  let s := x.val.1
  rw [item,concentrates,Finset.mul_sum]; apply (norm_sum_le _ _).trans
  refine le_trans (Finset.sum_le_sum (g:=fun i => B*‖glimpse x i‖) (fun i _ => ?_)) ((le_of_eq ?_).trans (mul_le_mul_of_nonneg_left (hE x) he))
  · rw [norm_mul, norm_mul, ← mul_assoc, Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans hr) _)]
    exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr
      (show generation x.val ≤ i.val.degree+2 from Nat.add_le_add_right i.property.2.1 _))
      (norm_nonneg _)).trans (h (⟨i.val,i.property.1,Nat.zero_le _,i.property.2.2⟩ : Hub G d 0))) (norm_nonneg (glimpse x i))
  unfold fee; rw [Finset.mul_sum]

lemma buys {T : ℝ} (hr : 1≤r) {B : ℝ} (hb : 0 ≤ B) (z : S) {M : ℕ} (hf : street (f z).1 ≤ M) (he : ((M:ℝ))^(d-1)≤T)
    {F : Horizon G} (h : Gather d r B M F) : ‖passcode f r d (.inr z) F‖ ≤ B*T := by
  let k := d-1
  let K := r^(k+2)
  have hp : 0<K := pow_pos (zero_lt_one.trans_le hr) _
  have ht : ∀ L : Degree G,L.degree=k → street L.point ≤ M → ‖gesture L F‖ ≤ B/K := by
    intro L h₁ h₂; apply (le_div_iff₀ hp).mpr; rw [mul_comm]
    exact (show K=amount r L by rw [amount,h₁]) ▸ h.2 L (Or.inr ⟨h₁,h₂⟩)
  rw [stub,norm_mul,Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans hr) _)]
  apply (mul_le_mul (pow_le_pow_right₀ hr (show d+1≤k+2 by omega)) (remains F h.1 (B/K) (div_nonneg hb hp.le) M ht _ hf) (norm_nonneg _) hp.le).trans
  change K*((M:ℝ)^k*(B/K)) ≤ _; field_simp; nlinarith only [hp, mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hb) hp.le]

lemma flight {T r B : ℝ} (hr : 1≤r) (hb : 0 ≤ B) {M : ℕ} (hf : ∀ z,street (f z).1 ≤ M) (he : ((M:ℝ))^(d-1) ≤ T) (hx : sensed (G:=G) d T)
    {F : Horizon G} (h : Gather d r B M F) (i : KeyIn G d ⊕ S) : ‖passcode f r d i F‖ ≤ B*T := by
  cases i with
  | inl i => exact fares f hr B hb _ i T hx fun L => h.2 _ (Or.inl ⟨L.property.1,L.property.2.2⟩)
  | inr i => exact buys f hr hb _ (hf _) he h

-- test errors for tensor kernel differences. low precision tighter than global cover.

def Vane (G : Gauge) := fun d r B E M (F : Bridge G) =>
    (∀ i, shutter (F i)) ∧ (∀ j, shutter (fun i => F i j)) ∧
    (∀ x y : Degree G, attends d M x → attends d M y → amount r x * amount r y * ‖mourn (gesture x) (gesture y) F‖ ≤ B) ∧
    ∀ (x y : Hub G d 0), amount r x.val*amount r y.val*‖mourn (gesture x.val) (gesture y.val) F‖ ≤ E

lemma breezy {F : Bridge G} {r B E : ℝ} (h : Vane G d r B E n F) (hr : 1 ≤ r) (L : Degree G) (hx : attends d n L) :
    Gather d r (B / amount r L) n (fun i => gesture L (fun j => F j i)) := by
  refine ⟨shut_reader (bright_gesture L) (fun i j => F j i) h.1, fun R he => ?_⟩
  have hP : 0 < amount r L := pow_pos (zero_lt_one.trans_le hr) _
  rw [le_div_iff₀ hP]; change amount r R*‖mourn (gesture R) (gesture L) (fun i j => F j i)‖ * _ ≤ _
  rw [moves _ _ _ (bright_gesture L)]; exact (mul_comm ..).le.trans (by rw [← mul_assoc]; exact h.2.2.1 L R hx he)

lemma eastward {F : Bridge G} {T B E r : ℝ} (h : Vane G d r B E n F) (hr : 1 ≤ r) (hb : 0 ≤ B) (hf : ∀ z, street (f z).1 ≤ n)
    (ht : ((n:ℝ))^(d-1) ≤ T) (hx : sensed (G:=G) d T) (i j) : ‖mourn (passcode f r d i) (passcode f r d j) F‖ ≤ B*T*T := by
  let u := fun x => passcode f r d j (F x)
  have hT := ht.trans' (pow_nonneg (Nat.cast_nonneg _) _)
  have hu : Gather d r (B*T) n u := by
    refine ⟨shut_reader (bright_pass f r ..) F h.2.1,fun L HL => ?_⟩
    change amount r L * ‖mourn (gesture L) (passcode f r d j) F‖ ≤ _
    rw [moves _ _ _ (bright_pass f r d j)]; have hp : 0 < amount r L := pow_pos (zero_lt_one.trans_le hr) _
    have he := flight f hr (div_nonneg hb hp.le) hf ht hx (breezy h hr L HL) j
    apply (mul_le_mul_of_nonneg_left he hp.le).trans_eq; field_simp
  exact flight f hr (mul_nonneg hb hT) hf ht hx hu i

lemma starbound {F : Bridge G} {T B E r : ℝ} (h : Vane G d r B E n F) (hr : 1 ≤ r) (hb : 0 ≤ E) (hp : 0 ≤ T)
    (hx : sensed (G:=G) d T) (i j) : ‖mourn (passcode f r d (.inl i)) (passcode f r d (.inl j)) F‖ ≤ E*T*T := by
  refine fares f hr (E*T) (mul_nonneg hb hp) (fun k => passcode f r d (.inl j) (F k)) i T hx fun L => ?_
  let v k := gesture L.val (fun x => F x k); have hv : 0<amount r L.val := pow_pos (zero_lt_one.trans_le hr) _
  have he : Drift d r (E/amount r L.val) v := by
    intro p; rw [le_div_iff₀ hv]
    change amount r p.val * ‖mourn (gesture p.val) (gesture L.val) (fun i j => F j i)‖ * _ ≤ _
    rw [moves _ _ _ (bright_gesture _)]; exact (mul_comm ..).le.trans (by rw [←mul_assoc]; exact h.2.2.2 L p)
  rw [show gesture L.val _= _ from moves (gesture L.val) (passcode f r d (.inl j)) F (bright_pass ..)]
  apply (mul_le_mul_of_nonneg_left (fares f hr _ (div_nonneg hb hv.le) v j T hx he) hv.le).trans_eq; field_simp
end YM.Next.Rank.Beamer
