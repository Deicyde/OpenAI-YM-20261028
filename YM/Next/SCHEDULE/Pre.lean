import YM.Next.SCHEDULE.Melt
import YM.Shift.Osc
import YM.Work.A15
import YM.Work.B04

/-!
# Pre-L floors

Enforce ALL gates at both adjacent transitions. Include particular repeated
costs. `.shrink`: pay the pre-L coefficient C_J/L of the inherited E at that
transition with a further multiplier C_J (choose a common upper bound here).
`.exchange`: support exponents incl extra and lowest pre-L operation prices,
all halo sites, no assumption their number bounded. `.cone`: the separate
support damping C_J L^d exp(-c_J L^(1/3)) in singleton transfer. Error terms
paid AFTER L. The `.ladder` exponent covers products made e.g. at the
weak-comparison stages. Any other pre-L demands may increase the floors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter RG RG.Supply Bid Precision Function Set Lattice
open scoped Topology

/-- Choose these after melt. One fee per (`j` fine→ `i` coarse).
`weakHeight` max b in p^b for work stretches; `cost`, `multiplicity` may
include pre-L inputs to these stretches depending on FINAL adjacent profile
parameters. Never estimate a cost repeated an unbounded number of times on a
plateau by a post-L one-time fee. `guard` is lowest additional *incoming* A to
plan to work at IF working at multiple support exponents. -/
structure Exchange where
  radius : ℕ
  extra : ℝ
  guard : ℝ
  cost : ℝ
  sep : ℝ
  weakHeight : ℝ
  multiplicity : ℝ
  ok : 0 ≤ extra ∧ 0 < guard ∧ 1 ≤ cost ∧ 0 < sep ∧ 0 ≤ weakHeight ∧ 0 ≤ multiplicity

/-- `radius` includes all pre-L halo costs relative to B (e.g. enlarge Fproj
to cover flag reads); not hiding dependence on numerical L here. -/
def Exchange.foot (e : Exchange) := ((e.radius+6)+(e.radius+6)+1)^4

/-- Uses `j` for an upper bound on D. -/
def coneFee (L C c : ℝ) (j : ℕ) := C/L+C*L^j*Real.exp (-c*L^((1:ℝ)/3))

variable {G : Gauge}
structure Buy (S : Survey G) (q : Quote) (e : Exchange) (j i : ℕ) (L : ℝ) : Prop where
  block : 3 ≤ L
  exchange : 10*(e.foot:ℝ)*(S.o.A j+e.extra) / L ≤ min (S.o.A j) e.guard/4
  phase : q.widths.loads j i / L ≤ q.widths.width j / 2
  path : (q.classicalCost.cap j)/L^ (2:ℕ) ≤ 1/8
  loop : q.finish.loop j i/L^ (2:ℕ) ≤ 1/4
  shrink : e.cost^ (2:ℕ)/L ≤ 1/16
  cone : coneFee L e.cost e.sep j ≤ (1/2:ℝ)/L^((2:ℝ)/5)
  ladder : ((j:ℝ)+1) * (e.weakHeight+4) * e.multiplicity * Real.log e.cost ≤ Real.log L

private lemma cone_cheap (C c : ℝ) (h : 0 < c) (j : ℕ) :
    ∀ᶠ L : ℝ in atTop, coneFee L C c j ≤ (1/2:ℝ)/L^((2:ℝ)/5) := by
  let p : ℝ := 2/5
  let a : ℝ := 1/3
  have ha : 0 < a := by norm_num [a]
  have hl : 0 < 1-p := by norm_num [p]
  have h1 := ((tendsto_const_nhds (x:=C)).div_atTop (tendsto_rpow_atTop hl)).eventually
    (ge_mem_nhds (show 0 < (1/4:ℝ) by norm_num))
  have H := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (((j:ℝ)+p)/a) c h).comp (tendsto_rpow_atTop ha)
  have h2 := (H.const_mul C).eventually
    (ge_mem_nhds (show C*0 < (1/4:ℝ) by norm_num))
  filter_upwards [h1,h2,eventually_gt_atTop (0:ℝ)] with L h1 h2 hL
  change C/L^(1-p) ≤ 1/4 at h1
  change C*((L^a)^(((j:ℝ)+p)/a)*Real.exp _) ≤ 1/4 at h2
  rw [← Real.rpow_mul hL.le, mul_div_cancel₀ _ ha.ne', Real.rpow_add hL, Real.rpow_natCast] at h2
  rw [Real.rpow_sub hL, Real.rpow_one, div_div_eq_mul_div] at h1
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL p)).2
  change (C/L+C*L^j*Real.exp (-c*L^a))*L^p ≤ 1/2
  calc
    _ = C*L^p/L+C*(L^j*L^p*Real.exp (-c*L^a)) := by ring
    _ ≤ _ := by dsimp only at h2; linarith

lemma Buy.afford (S : Survey G) (q : Quote) (e : Exchange) (j i : ℕ) : ∀ᶠ L in atTop, Buy S q e j i L := by
  have hh (x y : ℝ) (h : 0 < y) : ∀ᶠ L : ℝ in atTop, x/L ≤ y :=
    ((tendsto_const_nhds (x:=x)).div_atTop tendsto_id).eventually (ge_mem_nhds h)
  have hQ (x y : ℝ) (h : 0 < y) : ∀ᶠ L : ℝ in atTop, x/L^ (2:ℕ) ≤ y :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).eventually (hh x y h)
  have hr := e.ok.2.1
  filter_upwards [eventually_ge_atTop (3:ℝ),
    hh (10*(e.foot:ℝ)*(S.o.A j+e.extra)) _ (div_pos (lt_min (S.o.pos j) hr) (by norm_num : (4:ℝ)>0)),
    hh (q.widths.loads j i) _ (show 0 < q.widths.width j / 2 from half_pos (q.widths.wp _)),
    hQ (q.classicalCost.cap j) _ (by norm_num : 0 < (1/8:ℝ)),
    hQ (q.finish.loop j i) _ (by norm_num : 0 < (1/4:ℝ)),
    hh (e.cost^ (2:ℕ)) _ (by norm_num : 0 < (1/16:ℝ)),cone_cheap e.cost e.sep e.ok.2.2.2.1 j,
    Real.tendsto_log_atTop.eventually_ge_atTop (((j:ℝ)+1)*(e.weakHeight+4)*e.multiplicity*Real.log e.cost)] with L h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩

/-- Reach of a conference at C3 prices pinned pre-L. -/
structure Prepaid (S : Survey G) (K : MapPrices) (q : Quote) (e : ℕ → ℕ → Exchange) (v : ℕ → ℕ) : Prop where
  pins : Pinned (S.paper q v) S.X K
  higher : S.floorL ≤ v
  each (D : Rolls (S.paper q v)) (j i : ℕ) : Adj j i → Buy S q (e j i) j i (D.L j).val
  cash (D : Rolls (S.paper q v)) : ∀ a : Levels G, a.clock.stage=S.melt q → a.clock.factor=D.L →
    Bank q.finish.W a ∧ roomCost a q.finish.W

lemma Prepaid.floors (S : Survey G) (K : MapPrices) (h : Pinned S.sheet S.X K) (q : Quote) (e : ℕ → ℕ → Exchange) :
    ∃ f : ℕ → ℕ, ∀ v ≥ f, Prepaid S K q e v := by
  have hx := tendsto_natCast_atTop_atTop (R:=ℝ)
  choose l hl using fun j => eventually_atTop.1 (hx.eventually <| (Buy.afford S q (e j j) j j).and (Buy.afford S q (e j (j-1)) j (j-1)))
  obtain ⟨k,hk⟩ := Bid.buffer q.finish.W (S.paper q S.floorL) (fun j => S.ahead q j)
  refine ⟨fun i ↦ max (l i) (max (S.floorL i) (k i)),fun v hv => ⟨(h.later (S.forecast q v)),
    fun i => le_trans (le_max_of_le_right (le_max_left ..)) (hv i),?_,?_⟩⟩
  · intro D j i he
    obtain ⟨h1,h2⟩:=hl _ _ ((le_max_left ..).trans ((hv j).trans (D.large j).need))
    rcases he.cases_back with h|h <;> subst i
    · exact h1
    exact h2
  exact fun D a h1 h2 => hk v (fun i => (le_max_of_le_right (le_max_right ..)).trans (hv i)) D a h2 h1

open Pressure Pressure.Testing

/-- Extra energy prescription. Keep the actual response κ explicit: bids
made AFTER this (post-L) may depend on it. `floorBeta` measures entrance in
x = coarse hat-coupling β̂. These data (issued pre any calendar) apply on any
depth and period via the indicated Teller. -/
structure Radios {P : Sheet G} (K : MapPrices) (D : Rolls P) where
  W : ℕ → ℕ → ℝ
  strength : ℕ → ℕ → ℝ
  floorBeta : ℕ → ℕ → ℝ
  station j i : 0 < W j i
  sound j i : 0 < strength j i
  reaches j i : Adj j i → P.first ≤ i → ∀ b ≥ floorBeta j i,
    Teller.live (query P K j i) (D.L j) (W j i) (fun S T _ A x U k V =>
      strength j i*(fiery G x (D.L j))^2*A.shares ≤ A.assessed T x U (S.prediction U k) V) b

def PreGrant (P : Sheet G) (K : MapPrices) := ∀ D : Rolls P, ∀ m : ℕ → ℕ → ℝ,
  ∃ R : Radios K D, ∀ j i, m j i ≤ R.W j i

/-- The extra fees `m` on W can use different post-L prices at EVERY stage,
not bounded uniformly over the schedule. -/
lemma PreGrant.joint (P : Sheet G) (K : MapPrices) (A : ∀ j i, Teller.Grants (query P K j i)) :
    ∃ f : ℕ → ℕ, ∀ v ≥ f, PreGrant { P with floorL := v } K := by
  obtain ⟨k,hk⟩ := pricing_order P K A
  refine ⟨k,fun v hv D m => ?_⟩
  let p' : Sheet G := { P with floorL := v }
  -- Auxiliary theta and delay ONLY to read the commission; not constraining
  -- choices of PostCost or theta at these L.
  obtain ⟨T,-⟩ := Protection.exists_margin D (fun _ => 1) (fun _ => zero_lt_one)
  let d : Delays T := ⟨fun _ => 0,fun _ _ => 0,fun _ => 0,fun _ => 0⟩
  have hr (j i : ℕ) : ∃ w μ x : ℝ, m j i ≤ w ∧ 0 < w ∧ 0 < μ ∧ ∀ (h : Adj j i) (_ : P.first ≤ i), ∀ b ≥ x,
      Teller.live (query p' K j i) (D.L j) w (fun S T _ A x U k V =>
        μ*(fiery G x (D.L j))^2*A.shares ≤ A.assessed T x U (S.prediction U k) V) b := by
    let y := max 1 (m j i)
    have hp : 0 < y := lt_of_lt_of_le zero_lt_one (le_max_left ..)
    by_cases h : Adj j i ∧ P.first ≤ i
    · obtain ⟨Y,-,-,-,-,F,g,hF⟩ := hk v hv D y hp.le T d
      obtain ⟨hw,μ,hμ,H⟩ := g.receipts i j h.1.1 h.1.2 h.2
      exact ⟨F j i,μ,_,(le_max_right ..).trans (hF _ _),hw,hμ,fun _ _ => H⟩
    exact ⟨y,1,0,le_max_right ..,hp,zero_lt_one,fun u a => (h ⟨u,a⟩).elim⟩
  choose w u x hh hw hu he using hr
  exact ⟨⟨w,u,x,hw,hu,he⟩,hh⟩

/-- Get K witnesses first. No assumption of universal Energy grant unless
actually requesting this extra pair of floors also. Usable with
`Integrated.pressure_grants` given EBare or specialized to just these queries. -/
theorem before (S : Survey G) : ∃ K : MapPrices, ∀ (q : Quote) (e : ℕ → ℕ → Exchange),
    (∃ f : ℕ → ℕ, ∀ v ≥ f, Prepaid S K q e v) ∧
    ((∀ i j, Teller.Grants (query (S.paper q S.floorL) K i j)) →
      ∃ f : ℕ → ℕ, ∀ v ≥ f, Prepaid S K q e v ∧ PreGrant (S.paper q v) K) := by
  obtain ⟨K,hK⟩:=commit S.sheet S.X
  refine ⟨K,fun q e => ?_⟩
  obtain ⟨f,hf⟩:=Prepaid.floors S K hK q e
  refine ⟨⟨f,hf⟩,fun ha => ?_⟩
  obtain ⟨l,hl⟩:=PreGrant.joint (S.paper q S.floorL) K ha
  exact ⟨fun i => max (f i) (l i),fun v hv => ⟨hf v (fun i => (le_max_left ..).trans (hv i)),hl v (fun i => (le_max_right ..).trans (hv i))⟩⟩
end YM.Next.Scheduling
