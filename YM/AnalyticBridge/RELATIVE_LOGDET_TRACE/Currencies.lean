import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Pockets
import YM.Push.FREE_RESOLVENT.Torus

/-!
# The local summable bills

Costs hold **uniformly per ordered address**, on common Tube, step, and output
height, regardless of which allowed sector V/flags/tags is read on it (no
promise of simultaneous smoothness across sectors). Don't extend that to summing
over all ignored large-volume tag arrays!
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Filter Function Set Matrix MeasureTheory FreeResolvent Lattice
open Next.SectorChange
open scoped Topology BigOperators Classical

variable {ι : Type} {c : Side} {B n l : ℕ}

def inventory (p : ι → Site c) (l B : ℕ) (z : Letter ι n) := pocket p l B z.2.1 z.2.1 z.2.2
def ticket (p : ι → Site c) (B : ℕ) (v C q : ℝ) (z : Letter ι n) : ℝ :=
  let i := z.2.1
  let x:= z.2.2
  let J:=fares (native c) p v
  if jumps (nearby p B) i i x then C*q^(z.1+1)*road J J i i x else 0

variable {p : ι → Site c} {v C q : ℝ}

lemma ticket_nn (p : ι → Site c) (v) (hC : 0 ≤ C) (hq : 0 ≤ q) (z : Letter ι n) : 0 ≤ ticket p B v C q z := by
  unfold ticket; dsimp only; split
  · exact mul_nonneg (by positivity) (road_pos _ _ (fun _ _ => fares_nn ..) (fun _ _ => fares_nn ..) ..)
  exact le_rfl

variable [Fintype ι] [DecidableEq ι]

section sized
variable {A : Square ι} {W : ι → Set ι}

lemma Priced.scrolls (H : Priced (native c) p W A v C q) (h : Aperture p B W A) (z : Letter ι 1) :
    IntegrableOn (scroll W A z.2.1 z.2.2) (Ioi 0) ∧ (∫ u in Ioi 0, |scroll W A z.2.1 z.2.2 u|) ≤ ticket p B v C q z ∧
      |page W A z| ≤ ticket p B v C q z := by
  unfold ticket; dsimp only; split
  · exact H.scroll_paid z
  next hx =>
    simp [Aperture.away h _ hx,page,show scroll W A z.2.1 z.2.2 = 0 from funext (h.away z hx)]
    exact integrable_zero _ _ _

lemma Priced.erratas (H : Priced (native c) p W A v C q) (h : Aperture p B W A) (z : Letter ι 0) :
    |errata W A z| ≤ ticket p B v C q z := by
  unfold ticket; dsimp only; split
  · apply (H.errata_paid z).trans
    apply mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (pow_nonneg H.coupon _) H.paid)
      (road_pos _ _ (fun _ _ => fares_nn ..) (fun _ _ => fares_nn ..) ..)
  next hx => rw [h.quiet z hx,abs_zero]
end sized

def pass (L q a θ : ℝ) (l B : ℕ) : ℝ := q*L*Real.exp (a*tilePrice l)*Real.exp (θ*(B:ℝ))
def permitCost (n : ℕ) (L V C q a θ : ℝ) (l B : ℕ) : ℝ :=
  V*C*q*L^n * Real.exp (a*tilePrice l)^(n+2)*Real.exp (θ*(B:ℝ))^(n+1+l)
def totalCost (n : ℕ) (L V C q a θ : ℝ) (l B : ℕ) : ℝ :=
  permitCost n L V C q a θ l B * (1-pass L q a θ l B)⁻¹

namespace Counting
variable {a L V θ : ℝ} (s : Site c)

def hit (s : Site c) (p : ι → Site c) (l B : ℕ) (v C q a : ℝ) (z : Letter ι n) :=
  if s ∈ inventory p l B z then ticket p B v C q z * Real.exp (a*coverNumber B (inventory p l B z)) else 0

omit [DecidableEq ι] in
lemma tagged_length (hv : 0 ≤ v) (hC : 0 ≤ C) (hq : 0 ≤ q) (hB : 0 < B) (hl : 1 ≤ l)
    (ha : 0 ≤ a) (ht : 0 ≤ θ) (hL : 0≤L)
    (hK : (native c).Volume p v L) (h : (native c).Volume p θ V) (n m : ℕ) :
    (∑ z : ι × (Fin (m+n) → ι),hit s p l B v C q a (⟨m,z⟩:Letter ι n)) ≤
      permitCost n L V C q a θ l B * pass L q a θ l B ^ m := by
  let T := Real.exp (a*tilePrice l)
  let J := Real.exp (θ*B)
  let w (i : ι) := (native c).weight (-θ) s (p i)
  let A := fares (native c) p v
  let N := C*q^(m+1)
  let H := T^(m+n+2)
  let P := J^(m+n+1+l)
  have hN : 0 ≤ N := by unfold N; positivity
  have hH : 0 ≤ H := by unfold H T; positivity
  have hP : 0 ≤ P := by unfold P J; positivity
  have hw (i : ι) : 0 ≤ w i := (native c).weight_nn ..
  have h1 (i : ι) (x : Fin (m+n) → ι) : hit s p l B v C q a (⟨m,i,x⟩:Letter ι n) ≤
      (P*H*N) * (w i * road A A i i x) := by
    have hR : 0 ≤ road A A i i x := road_pos _ _ (fun _ _ => fares_nn ..) (fun _ _ => fares_nn ..) ..
    unfold hit
    split
    next hu =>
      unfold ticket; dsimp only; split
      next he =>
        let Z := pocket p l B i i x
        have he1 := pocket_span p x he (show s∈Z from hu)
        have he2 := pocket_cost p hB hl i i x he
        have hs : Real.exp (a*coverNumber B Z) ≤ H := by
          unfold H T; rw [← Real.exp_nat_mul]
          have he' : (coverNumber B Z:ℝ) ≤ ((m+n+2:ℕ):ℝ)*tilePrice l := by exact_mod_cast he2
          exact Real.exp_monotone ((mul_le_mul_of_nonneg_left he' ha).trans_eq (by ring))
        have hr : 1 ≤ w i*P := by
          unfold w P J Cost.weight; rw [← Real.exp_nat_mul,← Real.exp_add]
          apply Real.one_le_exp
          change 0 ≤ -θ * separation s (p i) + ((m+n+1+l:ℕ):ℝ)*(θ* (B:ℝ))
          rw [separation_comm]; have hi : (separation (p i) s:ℝ) ≤ ((m+n+1+l:ℕ):ℝ)*(B:ℝ) := by exact_mod_cast he1
          nlinarith only [mul_le_mul_of_nonneg_left hi ht]
        change N*_*Real.exp _ ≤ _
        refine (mul_le_mul_of_nonneg_left hs (mul_nonneg hN hR)).trans ?_
        exact (le_mul_of_one_le_left (mul_nonneg (mul_nonneg hN hR) hH) hr).trans_eq (by ring)
      next he => simp only [zero_mul]; exact mul_nonneg (by positivity) (mul_nonneg (hw _) hR)
    next hu => exact mul_nonneg (by positivity) (mul_nonneg (hw _) hR)
  have h2 (i : ι) : (∑ x : Fin (m+n) → ι, hit s p l B v C q a (⟨m,i,x⟩:Letter ι n)) ≤
      P*H*N*L^(m+n)*w i := by
    refine (Finset.sum_le_sum (fun x _ => h1 i x)).trans ?_
    rw [← Finset.mul_sum,← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_fares hv hL hK (m+n) i i) (hw i))
      (mul_nonneg (mul_nonneg hP hH) hN)).trans_eq (by ring)
  rw [Fintype.sum_prod_type]; refine (Finset.sum_le_sum (fun i _ => h2 i)).trans ?_
  rw [← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left (h.bound s) (by positivity)).trans_eq ?_
  change _ * V = V*C*q*L^n * T^(n+2)*J^(n+1+l)*(q*L*T*J)^m
  unfold P H N
  rw [show m+n+2=m+(n+2) by omega,show m+n+1+l=m+(n+1+l) by omega]
  simp only [pow_add,pow_one,mul_pow]; ring

omit [DecidableEq ι] in
/-- Local differentiations can use larger l. This prices just values of
all ordered chains hitting at **any** of those lenses (not multiplied by
fuel for *each* such hit). -/
theorem passports (hv : 0 ≤ v) (hC : 0 ≤ C) (hq : 0 ≤ q) (hB : 0<B) (hl : 1 ≤ l)
    (ha : 0 ≤ a) (ht : 0 ≤ θ) (hL : 0≤L) (hK : (native c).Volume p v L)
    (h : (native c).Volume p θ V) (he : pass L q a θ l B < 1) (n : ℕ) :
    Ac.Hit (inventory p l B (n:=n)) B (ticket p B v C q) a (totalCost n L V C q a θ l B) := by
  intro s
  let f := hit s p l B v C q a (n:=n)
  have he' : 0 ≤ pass L q a θ l B := by unfold pass; positivity
  have hp := (hasSum_geometric_of_lt_one he' he).mul_left (permitCost n L V C q a θ l B)
  have h0 z : 0 ≤ f z := by
    unfold f hit; split
    · exact mul_nonneg (ticket_nn _ _ hC hq _) (Real.exp_pos _).le
    exact le_rfl
  let g (m : ℕ) := ∑' x,f ⟨m,x⟩
  have hh (m : ℕ) : g m ≤ permitCost n L V C q a θ l B * pass L q a θ l B ^ m := by unfold g; rw [tsum_fintype]; exact tagged_length s hv hC hq hB hl ha ht hL hK h n m
  have hg := hp.summable.of_nonneg_of_le (fun m => (by apply tsum_nonneg; intro; apply h0 : 0 ≤ g m)) hh
  have hu : Summable f := (summable_sigma_of_nonneg h0).2 ⟨fun m=>.of_finite,hg⟩
  refine ⟨h0,hu,?_⟩
  change ∑' z,f z ≤ _
  rw [Summable.tsum_sigma' (fun m=>.of_finite) hu]
  exact (hg.tsum_le_tsum hh hp.summable).trans_eq hp.tsum_eq
end Counting
end YM.AnalyticBridge.RelativeLogdet
