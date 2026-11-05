import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.AtPose
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Supply
import YM.Planned.ATOM_FORCED_ESTIMATE.Held



/-!
# Retained suppression and a same-law integral application (including through ordered jets)

This is a subcomponent charge. No global volume-free support-cost
implication; e.g., paying every other invoice, summing these costs over
variants/decompositions, moving across stages, derivative interchange in a
full open extension still need more! The integral price through V jets here
is at evaluation (after rewriting), not differentiating the integrated
coefficient from hypotheses only at one point. For L² uses we *first*
price the rough word incl support and event on its own true Z marginal.
No asking that word to be supported by a trigger for the shifted argument
of a different law (or an independent covariance draw).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad
open Function Filter Metric Set Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian Spot Spot.Programme Notice Tariff
open AnalyticBridge.AnnulusRatioInsertions.Prism AnalyticBridge.AnnulusRatioInsertions.Parade SectorNext.Remainder
open MeasureTheory Push.SectorMeasure Presented Wisps Schur Bid ProjectorNext.Equivariance 
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

section measurable
variable {G : Gauge} {n : Side} {I : Type*} {V : Config G n}
private def stepTime (i : ℕ) : ℝ := (i:ℝ)⁻¹
private lemma timed : Tendsto stepTime atTop (𝓝[>] 0) := tendsto_inv_atTop_nhdsGT_zero.comp tendsto_natCast_atTop_atTop
private lemma timed₀ : Tendsto stepTime atTop (𝓝 0) := timed.mono_right nhdsWithin_le_nhds
private def proxy (F : Config G n → ℝ) : List (Directions G n) → Config G n → ℝ
  | [],U => F U
  | A::l,U => limUnder atTop (fun i : ℕ => (stepTime i)⁻¹ • (proxy F l (increment U (stepTime i • A)) - proxy F l U))
private lemma proxy_eq {F : Config G n → ℝ} (l : List (Directions G n)) (h : HasOrderAt F V l.length) : proxy F l V = leftDerivs F l V := by
  induction l generalizing V with
  | nil => rfl
  | cons A l ih =>
    unfold proxy
    apply Tendsto.limUnder_eq
    have he : l.length < (A::l).length := Nat.lt_succ_self _
    have ht := ((Next.Foundations.left_has A he h).tendsto_slope_zero_right.comp timed)
    refine ht.congr' ?_
    filter_upwards [timed₀.eventually (recur h A)] with i hi
    rw [ih (hi.fewer he.le),ih (h.fewer he.le)]; simp [Next.SectorChange.Motion.increment_zero]
private lemma proxy_meas [MeasurableSpace I] (F : I → Config G n → ℝ) (hF : ∀ W,StronglyMeasurable (fun p => F p W))
    (l : List (Directions G n)) (V : Config G n) : StronglyMeasurable (fun p => proxy (F p) l V) := by
  induction l generalizing V with
  | nil => exact hF V
  | cons A l ih => exact StronglyMeasurable.limUnder fun i => ((ih (increment V (stepTime i • A))).sub (ih V)).const_smul (stepTime i)⁻¹
end measurable

variable {G : Gauge} {c f : Side} {S : StepData c f} {d : Desk G S} {Q : Kiosk} {P : Patch} {Pt : Teller G}
    {Z : ChartRatio G} {χ : Chi} {r x θ E : ℝ} {power k n : ℕ}
    {ι H R α β γ I : Type} [Fintype ι] [DecidableEq ι] [Fintype H] [Fintype R] [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ] [Fintype I] [DecidableEq I]
    {A : Stores S} {F : Forest S.ratio} {κ : S.Choices} {V : Config G c} {X : Support c} {Ω : Set (Config G c)}
    {l : Viewport (spectacle d A F κ) X H R ι} {D : (spectacle d A F κ).Slices} {b : Finset ℕ} {q : Programme D b} {z : q.Run α β γ}
    {s : Seats l z} {a : Notice l} {B : Reading a z} {M : Income α β γ (H⊕R)} {o : Site c}

def ask (d : Desk G S) (E : ℝ) (n : ℕ) := E*Scales.b d.betaHat^n

def saving (d : Desk G S) (Q : Kiosk) (θ : ℝ) (m : ℕ) := Real.exp (-rateTrigger Q.cap θ*Scales.p G S.patch.L d.betaHat ^2 * m)


def payoff (T : Tariff α β γ I) := T.salary * 2^T.seat.card
omit [Fintype I] [DecidableEq I] [DecidableEq γ] in
lemma payoff_nn (T : Tariff α β γ I) [Fintype I] (h : T.Lease) : 0 ≤ payoff T := mul_nonneg h.solvent (by positivity)

def kitty (T : Tariff α β γ I) := (∏ i,T.port i)*(∏ i,T.wage i)* Real.exp (T.value + ∑ i∈T.coreᶜ, T.cost i)
def stageCost (Q : Install (G:=G) α β γ I) := kitty Q.rents * 2^(∑ i∈Q.big,(Q.sit i).card)
def rankCost (T : Tariff α β γ I) (k J i j : ℕ) := (T.sigmaRate k J)^i*T.ray^j * Moments.meter (Fintype.card I) 0 T.capacity (T.degreeTag i j)

omit [DecidableEq I] [DecidableEq γ] in
lemma rankCost_nn (T : Tariff α β γ I) (h : T.Lease) (k J i j : ℕ) : 0 ≤ rankCost T k J i j := by
  have hr := h.high; have h0 := h.size; unfold rankCost sigmaRate impulse Moments.meter Moments.inflate
  have hh := Reading.Clearance.degrees_pos k (Fintype.card α) (Fintype.card β) (Fintype.card γ) (Fintype.card I) J
  positivity

omit [DecidableEq I] [DecidableEq γ] in
lemma universal_cost (T : Tariff α β γ I) (k J i j : ℕ) : T.universal k J i j = payoff T * rankCost T k J i j := by
  unfold Tariff.universal Tariff.outside payoff rankCost Moments.meter; rw [pow_succ]; ring

def request (s : Seats l z) (Q : Kiosk) (M : Income α β γ (H⊕R)) (θ : ℝ) (o : Site c) (k : ℕ) := hire s Q.v M o Q.L k θ Q.cap

namespace Day
variable (h : Day Q θ E k n d) (hC : Clearing (spectacle d A F κ) V)
include h
omit [DecidableEq ι] [Fintype ι] in
lemma pays (s : Seats l z) (M : Income α β γ (H⊕R)) (o : Site c) : let T := request s Q M θ o k
    T.rents.Lease ∧ (M.expose.Nonempty → 0<T.rooted) ∧ (∀ i,T.watch i + ∑ j,T.hit j i ≤ Q.cap⁻¹/8) ∧
      0 < T.eps := ⟨s.lease Q.v M h.limits, (s.enters Q.v M h.limits h.beta h.marked 0).2.2, s.jointly Q.v M h.limits,Arc.pinch_pos h.limits.positive⟩

omit [Fintype ι] [DecidableEq ι] in
theorem savings (s : Seats l z) (M : Income α β γ (H⊕R)) (o : Site c) : let T := request s Q M θ o k; let m := T.expose.card
    ask d E n ^m * payoff T.rents ≤ saving d Q θ m * stageCost T := by
  intro T m; let R := T.rents; let x := (2:ℝ)^(∑ i∈T.big,(T.sit i).card)
  let y := Arc.tail Q.cap (anxious G S.patch.L d.betaHat θ d.input.beta) m
  have hz : R.salary = kitty R * y := by
    unfold Tariff.salary kitty y Arc.tail; rw [mul_assoc _ (Real.exp _), ← Real.exp_add,sub_eq_add_neg]; congr 2
    congr 1; change - (Arc.pinch Q.cap*(m*anxious G S.patch.L d.betaHat θ d.input.beta ^2)) = _; ring
  have hy : 0≤ask d E n:= mul_nonneg h.cost_nn (pow_nonneg (zero_le_one.trans (Scales.size _)) _)
  have hh := (h.pays s M o).1
  have hr : 0≤ kitty R := mul_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _=> hh.present _) (Finset.prod_nonneg fun _ _=>hh.wages _)) (Real.exp_pos _).le
  have ht : (2:ℝ)^R.seat.card ≤ tuck G ^m*x := by
    unfold tuck x; rw [← pow_mul, Nat.mul_comm (Fintype.card G.ColorIndex), ← pow_add]; exact pow_le_pow_right₀ (by norm_num) T.seats_count
  unfold payoff stageCost
  change ask d E n ^m *(R.salary * _) ≤ _*(kitty R*x)
  rw [hz]
  calc
    _ ≤ (kitty R*x)*(y*tuck G^m*(ask d E n)^m) := by
      convert! (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (mul_nonneg hr (Arc.tail_pos ..).le)) (pow_nonneg hy m)) using 1; ring
    _ ≤ _ := ((mul_le_mul_of_nonneg_left (h.rebates m) (mul_nonneg hr (by unfold x; positivity))).trans_eq (mul_comm ..))

include hC
omit [Fintype ι] [DecidableEq ι] in
theorem admitted (hO : Orders B M s Q.v θ (4*d.radius) Q.L o V k) :
    B.Clearance (4*d.radius) (request s Q M θ o k).rents V (d.out.dirBound o) k := by
  obtain ⟨hx,hy⟩ := h.capacity A F κ V hC.flags
  exact orders h.limits hC hx hy h.marked h.beta hO h.charts
omit [Fintype ι] [DecidableEq ι] in
lemma atTerm (o : Site c) (hT : Terms s V) (hA : Ancillary B M s θ V) : B.Rough V (request s Q M θ o k).rents := by
  obtain ⟨hx,hy⟩ := h.capacity A F κ V hC.flags
  exact rough h.limits hC hx hy h.marked h.beta hT hA o Q.L rfl

omit hC [DecidableEq ι] in
/-- At fixed V estimate all struck and unstruck occurrences and any authorized event support on ONE local FKer
and under its integral, including positive order with change of variables.
Absolute ∫ at that pose. Does NOT interchange derivatives under ∫ (would require open-neighborhood
extra estimates). Does not assume the combined Z-exp bill, paying it incl residual spare before BOTH uses.
-/
theorem collected_of (hx : B.Clearance (4*d.radius) (request s Q M θ o k).rents V (d.out.dirBound o) k) (hm : B.Shutter Ω (4*d.radius)) (hΩ : Ω ∈ 𝓝 V)
    (N : List (Directions G c)) (hn : N.length ≤ k) (hd : ∀ i∈N, d.out.dirBound o i) :
    let T := request s Q M θ o k; let R' := T.rents; let m := T.expose.card
    let f p := leftDerivs (fun Y => B.endorsed Q.outer Y p) N V; let μ := pullLaw G H R ι
    Integrable f μ ∧
      ask d E n ^m * (∫ p, ‖f p‖ ∂μ) ≤ saving d Q θ m * stageCost T * rankCost R' k (Fintype.card H) N.length 0 := by
  intro T R' m f μ
  have hh := hx.cash h.room hΩ h.allows hm N hn hd
  have ht p := hx.success h.room hΩ h.allows hm p
  obtain ⟨ha,hb⟩ := a.repaid R' k N.length 0 Q.outer hx.leased h.room V hx.pane hx.bought
  have hs : StronglyMeasurable f := by
    let F (p : Reel G H R ι) Y := B.endorsed Q.outer Y p
    have hy (Y : Config G c) : Measurable (B.endorsed Q.outer Y) := Curtain.rewrite_meas_of d.chart d.g Q.outer (l.copy Y) (a.C Y) (a.tide Y)
      (a.readable Y) (fun x z => B.word Y (x,z)) (B.member Y) h.room
    have hZ p : proxy (F p) N V=f p := proxy_eq _ ((ht p).smooth.fewer hn)
    exact funext hZ ▸ proxy_meas F (fun W => (hy W).stronglyMeasurable) N V
  have hi : Integrable f μ := ha.mono' hs.aestronglyMeasurable (Eventually.of_forall hh)
  have hv := (integral_mono hi.norm ha hh).trans hb
  rw [universal_cost] at hv
  refine ⟨hi,((mul_le_mul_of_nonneg_left hv (pow_nonneg (mul_nonneg h.cost_nn (pow_nonneg (zero_le_one.trans (Scales.size _)) _)) _)).trans ?_)⟩
  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (h.savings s M o) (rankCost_nn R' hx.leased ..)

omit [DecidableEq ι] in
theorem collected (hO : Orders B M s Q.v θ (4*d.radius) Q.L o V k) (hm : B.Shutter Ω (4*d.radius)) (hΩ : Ω ∈ 𝓝 V)
    (N : List (Directions G c)) (hn : N.length ≤ k) (hd : ∀ i∈N, d.out.dirBound o i) :
    let T := request s Q M θ o k; let R' := T.rents; let m := T.expose.card
    let f p := leftDerivs (fun Y => B.endorsed Q.outer Y p) N V; let μ := pullLaw G H R ι
    Integrable f μ ∧
      ask d E n ^m * (∫ p, ‖f p‖ ∂μ) ≤ saving d Q θ m * stageCost T * rankCost R' k (Fintype.card H) N.length 0 :=
  h.collected_of (h.admitted hC hO) hm hΩ N hn hd
end Day
end YM.PhysicalNext.JointLoad
