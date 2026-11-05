import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.StampCost
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Walt

/-!
# Envelope independent of V, Y, F and every tag

Retain TRUE chain ratio lengths, count terminal A for order (unscaled)
from calibrated script. Unlike E Laplace-tail argument do not need
L4 since hard replacements in this dictionary mask with ψ. This alone
doesn't give variation with fixed z or with covariance under V derivative.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {η r Q Y : ℝ} {L : Side}
variable (X : Coat T F)

private lemma stack_bound (θ : Rotator P L η r Q Y X) (n : ℕ) (i : Bond f) (p : Itinerary f (n+2)) :
    let M := Q*distPay η r Q (tubularPrice G L) X.B
    let R := (Fintype.card G.ColorIndex:ℝ)
    ∀ x y, |combo i p (X.finale n) x y| ≤ R^(n+2)*(Q*M^(n+1)) := by
  intro M R x y
  have hB := θ.scale
  have hg := hB.disc
  have hh := hB.heap X.B
  have hQ : 0≤Q := hB.fuel.le
  have hn : 0≤M := mul_nonneg hQ (mul_nonneg hg hh)
  let l (n i : ℕ) := if i ≤ n then M else Q
  have hu k (hk : k<n+2) : 0≤l n k := by unfold l; split <;> assumption
  have hs k j i : |X.finale n k j i| ≤ l n k := by
    unfold finale l; split
    next he => exact only_price ((spent_neg (hB.flank _)).1) θ.full.prices.le j i
    next he => exact only_price hB.price hB.eta.le j i
  have hZ (n : ℕ) : tally (n:=n+2) (l n) = Q*M^(n+1) := by
    induction n with
    | zero =>
      rw [count_mul 1,count_mul 0]
      change l 0 0*(l 0 1*1)=_; simp [l,mul_comm]
    | succ i hi =>
      rw [count_mul (i+2),show (fun t => l (i+1) (t+1))=l i from funext fun t => by simp [l], hi]
      unfold l; rw [if_pos (Nat.zero_le _),pow_succ]; ring
  rw [← hZ n]; exact pricingEntries S (X.finale n) (l n) i p (fun k _ => hs k) hu x y

private lemma enforce_arc (θ : Room P S T X.x) (n : ℕ) (z : Air f G) (i : Bond f) (p : Itinerary f (n+2))
    (h : X.qunique z ⟨n,i,p⟩ ≠ 0) : Armed S (3*X.B) i p := by
  by_contra hn; apply h
  have hh : combo i p (X.finale n)=0 := by
    refine filtered S (3*X.B) _ _ hn (X.finale n) ?_; intro k _; unfold finale; split
    next he => exact opposite _ (effects _ _ (X.span θ) (le_trans (by norm_num) θ.sight.1))
    next he => exact fun i j h => X.span θ i j (by omega)
  simp [qunique,circle,hh]

def centreQ (η r Q : ℝ) (m B : ℕ) (G : Gauge) (K : ℝ) := (1/2:ℝ) * K^2 * flagP (G:=G)^4 * (Q*(Q*distPay η r Q m B))
def capQ (S : StepData c f) (η r Q : ℝ) (m B : ℕ) (G : Gauge) (K : ℝ) (p : Ledger f 2) :=
    cap S B 2 p (centreQ η r Q m B G K) (etaS η r Q m B G)
lemma borne (θ : Rotator P L η r Q Y X) (z : Air f G) (p : Ledger f 2) {β a U K : ℝ}
    (hβ : 0<β) (ha : 0 < a*X.t) (hU : 0≤U) (hk : heat a K X.t β ≤ U) (he : ∀ i, ‖X.μ i‖ ≤ K*X.t) :
    |X.chain β z a p| ≤ capQ S η r Q (tubularPrice G L) X.B G U p := by
  let E := X.aperture β z a
  let m := tubularPrice G L
  have hg : 0≤ capQ S η r Q m X.B G U p := by
    have ht := θ.scale; have hh : 0≤distPay η r Q m X.B := mul_nonneg ht.disc (ht.heap _)
    unfold capQ cap; split
    next hi => unfold centreQ etaS flagP; have := ht.fuel; positivity
    exact le_rfl
  unfold chain
  by_cases hu : E p.2.1 * E (arrive p.2.1 p.2.2)=0
  · change |_ * X.qunique z p| ≤ _; unfold E at hu; rw [hu,zero_mul,abs_zero]; exact hg
  by_cases hz : X.qunique z p=0
  · rw [hz,mul_zero,abs_zero]; exact hg
  obtain ⟨i,j⟩ := X.emitting θ z p hz
  rcases p with ⟨n,x,t⟩; dsimp only at *
  let y := arrive x t
  have h (a') (hg : X.Hot a') (he' : E a'≠0) (u : G.ColorIndex) :
      |z (a',u)| ≤ U := (stand_cap u (X.atmos z a')).trans ((X.held z hβ ha a' hg he' (he a')).trans hk)
  have hi := h x i (left_ne_zero_of_mul hu); have hj := h y j (right_ne_zero_of_mul hu)
  rw [abs_mul (X.aperture β z a x * _)]
  apply (mul_le_of_le_one_left (abs_nonneg _) ?_).trans
  rotate_left
  · simp only [aperture,if_pos i, if_pos j,abs_mul]; rw [abs_of_nonneg (X.booked ..).1, abs_of_nonneg (X.booked ..).1]
    exact mul_le_one₀ (X.booked ..).2 (X.booked ..).1 (X.booked ..).2
  let R := flagP (G:=G)
  let M := Q*distPay η r Q m X.B
  let f' := combo x t (X.finale n)
  let F := R^(n+2)*(Q*M^(n+1))
  have hc (u : G.ColorIndex) : |∑ k : G.ColorIndex,f' u k*z (y,k)| ≤ R*(F*U) := by
    apply (Finset.abs_sum_le_sum_abs ..).trans
    refine (Finset.sum_le_sum (g:=fun _ => F*U) (fun k _ => ?_)).trans_eq (by rw [sum_const,nsmul_eq_mul,card_univ]; rfl)
    rw [abs_mul]; have hs : |f' u k| ≤ F := X.stack_bound θ n x t u k
    exact mul_le_mul hs (hj k) (abs_nonneg _) ((abs_nonneg _).trans hs)
  unfold qunique circle; dsimp only; rw [abs_mul, abs_of_pos (by norm_num : 0<(1/2:ℝ))]
  have hs : |∑ u : G.ColorIndex,z (x,u)*∑ k, f' u k*z (y,k)| ≤ R*(U*(R*(F*U))) := by
    apply (abs_sum_le_sum_abs ..).trans; refine (Finset.sum_le_sum (g:=fun _ => U*(R*(F*U))) (fun i _ => ?_)).trans_eq ?_
    · rw [abs_mul]; exact mul_le_mul (hi i) (hc i) (abs_nonneg _) hU
    rw [sum_const,nsmul_eq_mul,card_univ]; rfl
  apply (mul_le_mul_of_nonneg_left hs (by norm_num : 0≤ (1/2:ℝ))).trans_eq
  unfold capQ cap; dsimp only; rw [if_pos (enforce_arc X θ.room n z x t hz)]
  unfold centreQ etaS F R M m; ring
end YM.ConnectedActivityE6.Coat
