import YM.Extra.ITERATION_NO_LOSS.Inherited
import YM.Extra.ITERATION_NO_LOSS.Rebase
import YM.Extra.ITERATION_NO_LOSS.Roots
import YM.Next.EXTRACTION.Relay
import YM.Next.FLUCTUATIONS.Bare

/-!
# Regenerating pre-L budgets for stationary paths

Here and in the consumers the first index on a pair cost is the fineside
stage, the second is the destination (same or predecessor, not always a
different stage!). The raw apertures must have been estimated **before**
the working width or caps; the pre-L jets' price constants only after
this width, the determinant constants can also use the priced classical
bounds (all before D). No assert of any specific prices/widths achieved by a
Laurent lift or other dynamics. See `Mechanism` for actual estimates needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration
open Filter Function Lattice Wilson RG RG.Supply Precision Tree Bloch Bid Craft
open scoped Topology BigOperators
variable {G : Gauge}

/-- `eta` is the step strip in coarse units before input-dependent computations;
`fraction*clear` the remaining width prediction (finitely many within-call losses
**total**, can decrease fraction when including lift, cubic→quartic and
path-moment losses). `routes*eta` buys input phase tilt on fine paths after
division by L leaving half the incoming width. Endpoint of this ledger is
native-site `PathData.Bounds` (can include moment strengthening via `Charged.moments`). -/
structure Apertures where
  bare : ℕ → ℝ
  eta : ℕ → ℕ → ℝ
  fraction : ℕ → ℕ → ℝ
  routes : ℕ → ℕ → ℝ
  posB j : 0 < bare j
  posE j k : 0 < eta j k
  posF j k : 0 < fraction j k
  small j k : fraction j k ≤ 1
  routes_ge j k : 1 ≤ routes j k

/-- All before setting classical caps (but can use `width`). -/
structure ClassicalCosts where
  top : ℕ → ℝ
  fresh : ℕ → ℕ → ℝ
  top_nonneg j : 0 ≤ top j
  fresh_nonneg j k : 0 ≤ fresh j k

/-- Can also use the actual chosen classical cap. `det` is the prefactor on
the emitted fresh loop-array estimate AND `slope` controls the alpha error
*without* L or Λ, before all post-L estimates. -/
structure QuantumCosts where
  det : ℕ → ℕ → ℝ
  slope : ℕ → ℕ → ℝ
  det_nonneg j k : 0 ≤ det j k
  slope_nonneg j k : 0 ≤ slope j k

namespace Apertures
variable (U : Apertures) (K : MapPrices)

def clear (j k : ℕ) := min (min (K.α j) (K.α k)) (U.eta j k)
lemma clear_pos (j k) : 0 < U.clear K j k := lt_min (lt_min (K.alpha_pos _) (K.alpha_pos _)) (U.posE ..)

def port (j k : ℕ) := U.fraction j k*U.clear K j k
lemma port_pos (j k) : 0 < U.port K j k := mul_pos (U.posF ..) (U.clear_pos ..)
lemma port_clear (j k) : U.port K j k ≤ U.clear K j k := mul_le_of_le_one_left (U.clear_pos ..).le (U.small ..)

def width (P : Sheet G) (j : ℕ) := min (min (P.profile j).width (U.bare j)) (min (U.port K j j) (U.port K (j+1) j)) / 2
lemma width_pos (P : Sheet G) (j : ℕ) : 0 < U.width K P j := half_pos (lt_min
  (lt_min (P.profile j).width_pos (U.posB j)) (lt_min (U.port_pos ..) (U.port_pos ..)))
lemma width_exit (P : Sheet G) (j k : ℕ) (h : k ≤ j) (he : j ≤ k+1) : 2*U.width K P k ≤ U.port K j k := by
  rw [width,mul_div_cancel₀ _ (two_ne_zero' ℝ)]
  refine le_trans (min_le_right ..) ?_; rcases (show j=k ∨ j=k+1 by omega) with rfl|hj
  · exact min_le_left ..
  rw [hj]; exact min_le_right ..

end Apertures
namespace ClassicalCosts
variable (A : ClassicalCosts) (U : Apertures) (K : MapPrices)

def classicalMax (j k) := max (A.fresh j k)
    (max (Inherited.carryPrice (U.clear K j k) (K.Ω j) (K.Ω k) 3) (Inherited.carryPrice (U.clear K j k) (K.Ω j) (K.Ω k) 4))
def price (k : ℕ) := max (max 1 (A.top k)) (max (A.classicalMax U K k k) (A.classicalMax U K (k+1) k))
lemma price_ge (k : ℕ) : 1 ≤ A.price U K k := le_max_of_le_left (le_max_left ..)
lemma price_covers (j k) (h : k ≤ j) (he : j ≤ k+1) : A.classicalMax U K j k ≤ A.price U K k := by
  refine le_max_of_le_right ?_; rcases (show j=k ∨ j=k+1 by omega) with rfl|hj
  · exact le_max_left ..
  rw [hj]; exact le_max_right ..

def cap (j) := 6*A.price U K j
lemma cap_pos (j) : 0 < A.cap U K j := mul_pos (by norm_num) ((zero_lt_one' ℝ).trans_le (A.price_ge U K j))
end ClassicalCosts
open Inherited

/-- All pair thresholds for the taught paths; `credit` is the input stage. -/
structure Early (U : Apertures) (A : ClassicalCosts) (K : MapPrices) (credit : Stage) (j k : ℕ) (L : Side) : Prop where
  phase : 2*U.routes j k * U.eta j k ≤ credit.width*L.val
  contraction : A.cap U K j ≤ (L.val:ℝ)^2
  loop : 4 * diffPrice (U.clear K j k) credit.width (K.Ω j) (K.Ω k) ≤ (L.val:ℝ)^2

structure Before (P : Sheet G) (U : Apertures) (A : ClassicalCosts) (Q : QuantumCosts) (K : MapPrices) : Prop where
  bare j : 2*(P.profile j).width ≤ U.bare j
  roots j : (P.profile j).width ≤ K.α j
  port j k : k ≤ j → j ≤ k+1 → 2*(P.profile k).width ≤ U.port K j k
  row j : rootPrice (P.profile j).width (K.Ω j) ≤ (P.profile j).paths
  curves j : A.cap U K j ≤ (P.profile j).paths
  drift j k : k ≤ j → j ≤ k+1 → Q.slope j k + 1 ≤ (P.profile j).drift
  enough j k (L : Side) : k ≤ j → j ≤ k+1 → P.floorL j ≤ L.val → Early U A K (P.profile j) j k L

namespace Before
variable (U : Apertures) (A : ClassicalCosts) (Q : QuantumCosts) (K : MapPrices) (P : Sheet G)

private def stage (j : ℕ) : Stage :=
  let p := P.profile j
  let η := U.width K P j
  have hη := U.width_pos K P j
  let r := max p.clip.relaxation (12/η)
  let e := max (A.cap U K j) (max p.paths (rootPrice η (K.Ω j)))
  let d := max p.drift (max (Q.slope j j+1) (Q.slope j (j-1)+1))
  { p with
    width := η
    width_pos := hη
    paths := e
    paths_pos := (A.cap_pos ..).trans_le (le_max_left ..)
    drift := d
    drift_ge := p.drift_ge.trans (le_max_left ..)
    clip := { p.clip with relaxation := r, radius_pos := p.clip.radius_pos.trans_le (le_max_left ..) }
    slow_selector := (div_le_iff₀ hη).mp (le_max_right ..) }

private lemma priced (j k : ℕ) (p : Stage) : ∃ n : ℕ, ∀ L : Side, n ≤ L.val → Early U A K p j k L := by
  let bill := 4 * diffPrice (U.clear K j k) p.width (K.Ω j) (K.Ω k)
  let v := 2*U.routes j k*U.eta j k
  let cost := max (max (A.cap U K j) bill) (v / p.width)
  obtain ⟨n,hn⟩ := exists_nat_gt cost
  refine ⟨n,fun L hL => ?_⟩
  have hl : cost ≤ (L.val:ℝ) := hn.le.trans (by exact_mod_cast hL)
  have h1 : 1 ≤ (L.val:ℝ) := by exact_mod_cast L.pos
  have hsq := hl.trans (by nlinarith : (L.val:ℝ) ≤ (L.val:ℝ)^2)
  constructor
  · have hv := (div_le_iff₀ p.width_pos).mp ((le_max_right ..).trans hl : v/p.width ≤ _)
    rwa [mul_comm] at hv
  · exact le_trans (le_max_of_le_left (le_max_left ..)) hsq
  exact le_trans (le_max_of_le_left (le_max_right ..)) hsq

theorem issue : ∃ p : Sheet G, Upgrade P p ∧ P.first=p.first ∧ (∀ j,(p.profile j).width=U.width K P j) ∧
    P.floorL ≤ p.floorL ∧ (∀ j, (p.profile j).order=(P.profile j).order ∧ (p.profile j).power=(P.profile j).power ∧
      (p.profile j).supportExponent=(P.profile j).supportExponent) ∧ Before p U A Q K := by
  choose v hv using fun j k => priced U A K j k (stage U A Q K P j)
  let p := { P with profile := stage U A Q K P, floorL := fun j => max (P.floorL j) (max (v j j) (v j (j-1))) }
  have he (j) : 2*U.width K P j ≤ min ((P.profile j).width) (U.bare j) := by
    unfold Apertures.width; rw [mul_div_cancel₀ _ (two_ne_zero' ℝ)]; exact min_le_left ..
  have hw (j) := U.width_pos K P j
  refine ⟨p,⟨rfl,fun _ => rfl,fun j => by
      change U.width K P j ≤ _; linarith only [(he j).trans (min_le_left ..),hw j],
    fun _ => le_max_of_le_right (le_max_left ..),fun _ => le_rfl,
    fun _ => le_max_left ..,fun _ => le_max_left ..,fun _ => le_rfl⟩,rfl,fun _ => rfl, fun _ => le_max_left ..,fun _ => ⟨rfl,rfl,rfl⟩,?_⟩
  refine ⟨fun j => (he j).trans (min_le_right ..),fun j => ?_,U.width_exit K P, fun _ => le_max_of_le_right (le_max_right ..),fun _ => le_max_left ..,
      fun j k h he => le_max_of_le_right ?_,fun j k L h he hk => hv j k L (le_trans (le_max_of_le_right ?_) hk)⟩
  · have hz : U.port K j j ≤ K.α j := (U.port_clear K j j).trans ((min_le_left ..).trans (min_le_left ..))
    change U.width K P j ≤ _; linarith only [(U.width_exit K P j j le_rfl (by omega)).trans hz,hw j]
  all_goals rcases (show k=j ∨ k=j-1 by omega) with rfl|hk <;> first | exact le_max_left .. | rw [hk]; exact le_max_right ..

variable {P U A Q K} (h : Before P U A Q K)
include h
lemma boost {n : ℕ → ℕ} (hn : P.floorL ≤ n) : Before { P with floorL := n } U A Q K :=
  { h with enough := fun j k L he hf ht => h.enough j k L he hf ((hn _).trans ht) }
-- other callers may want to widen columns/stationary drift after having seen these prices.
end Before

lemma Early.fit {U A K credit j k L} (he : Early U A K credit j k L) : U.clear K j k ≤ credit.width/2 * L.val := by
  have hv := U.routes_ge j k; have hh : U.clear K j k ≤ U.eta j k := min_le_right ..; have ht := U.posE j k
  nlinarith only [he.phase,hv,hh,ht]
lemma Early.amplitude {U A K credit j k L} (he : Early U A K credit j k L) :
    A.cap U K j / (L.val:ℝ)^2 ≤ 1 ∧ A.cap U K j / (L.val:ℝ)^4 ≤ 1 := by
  have hl : 1 ≤ (L.val:ℝ) := by exact_mod_cast L.pos
  exact ⟨(div_le_one (by positivity)).2 he.contraction,(div_le_one (by positivity)).2
    (he.contraction.trans (pow_le_pow_right₀ hl (by omega)))⟩
end YM.Extra.Iteration
