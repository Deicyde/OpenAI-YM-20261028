import YM.Extra.ITERATION_NO_LOSS.Rebuild
import YM.Extra.WILSON_STARTUP.ForMix
import YM.Further.ITERATION_RECIPE_PRODUCER.Crown
import YM.Progress.JOINT_CALENDAR.Delivery

set_option warningAsError false

/-!
# Joint-calendar interface: placing the boundary and recurrence invoices

For E §vsh. Release in pre-L order, then ALL sufficiently grown v and
arbitrary Rolls, then post-L prices incl. Wilson RCake and gap/rates' *use*
budgets through Paid. Does NOT pay Heating or trajectory in-situ estimates
by these number inequalities; a producer still has to forecast rates at
these pre-L and post-L positions and solve the fresh physical invoices AT their
exact scope with these same choices. No arbitrary boosting preserving a
solved analytic problem after the fact!
-/
noncomputable section
set_option autoImplicit false
namespace YM.Further.IterationRecipe
open Filter Function Lattice Wilson RG RG.Supply Precision Bid Pressure Exterior Tree Extra.Iteration Calibration Next.Scheduling
open Progress.Joint WilsonStartup Next.Scheduling.Weak
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

def shutters (K : MapPrices) (U : Apertures) (z : Strips) := drawing K { z with
  launch j := min (U.bare j / 2) (z.launch j)
  emits j i := min (U.port K j i / 2) (z.emits j i)
  top_rate j := lt_min (half_pos (U.posB j)) (z.top_rate j)
  rate j i := lt_min (half_pos (U.port_pos K j i)) (z.rate j i) }

def pigment (s : Survey G) (K : MapPrices) (U : Apertures) (A : ClassicalCosts) (p : Figures) := ink K { p with
  beginCost j := max ((request s A).cap U K j) (p.beginCost j)
  pos j := le_max_of_le_right (p.pos j) }

def balance (H : QuantumCosts) (b : Finish) : Finish := { b with
  number j i := max (b.number j i) (H.slope j i)
  drift_nn j i := le_max_of_le_left (b.drift_nn j i) }

def written (s : Survey G) (K : MapPrices) (U : Apertures) (A : ClassicalCosts) (H : QuantumCosts) (q : Quote) : Quote :=
    ⟨shutters K U q.widths, pigment s K U A q.classicalCost,balance H q.finish⟩

variable {s : Survey G} {K : MapPrices} {U : Apertures} {A : ClassicalCosts} {H : QuantumCosts} {q : Quote}
local notation "q✶" => written s K U A H q






variable {B₀ : Authorities G} {P : Desk B₀} {e : ℕ → ℕ → Exchange} {V : Rebuild.Census}



variable {v : ℕ → ℕ} {D : Rolls (s.paper q v)} {Θ : Protection D} {W : Supply.Delays Θ}
    {B : Beam K D}



/-- Additional boost before `Joint.receive`. Mixture extras are just the
Wilson boundary bills from WILSON_STARTUP (must transport to widened layout
at call); not `Multi.Thick` on a full trajectory. Cool/Heating likewise
not to be confused: no advancing curve data through Regime or Actual here.
-/
structure Begins (H : QuantumCosts) (V : Rebuild.Census) (F : Rebuild.Fuel D) (W : Supply.Delays Θ) : Prop where
  warm : Warm H W
  cool : Rebuild.Cool V F W
  top : Timing.funded s.B.frames s.B.entry (s.paper q v) W.betaEntry
  markers : Mixture.funded (s.paper q v) W.betaEntry

lemma Begins.later {W' : Supply.Delays Θ} {F : Rebuild.Fuel D} (h : Begins H V F W) (hh : Boost W W') : Begins H V F W' :=
  ⟨h.warm.boost hh.beta hh.shells,h.cool.raise hh.beta,fun j hj x hx a N => h.top j hj x ((hh.beta j).trans hx) a N,
    fun j hj x hx a N => h.markers j hj x ((hh.beta j).trans hx) a N⟩

lemma Begins.issue (hG : G.Simple) (hv : Rebuild.Open V (s.paper q v)) (H : QuantumCosts) (F : Rebuild.Fuel D) (W : Supply.Delays Θ) :
    ∃ W' : Supply.Delays Θ, Boost W W' ∧ Begins H V F W' := by
  have h1 : Boost W (warmup H W) := ⟨fun _ => le_max_left ..,le_rfl,fun _ => le_max_left ..,le_rfl⟩
  obtain ⟨S,hs,hg,hE,hβ,hC⟩ := Rebuild.prices F (warmup H W) hG hv
  have h2 : Boost (warmup H W) S := ⟨hβ,hE.ge,hs.ge,hg.ge⟩
  obtain ⟨r,hr,hR⟩ := Timing.choose s.B.frames s.B.entry S fun j _ => s.direct_cap j
  obtain ⟨t,ht,hT⟩ := Mixture.first_edition S
  let f (i : ℕ) := max (r i) (t i)
  let W' : Supply.Delays Θ := { S with betaEntry := f }
  have h3 : Boost S W' := ⟨fun i => (hr i).trans (le_max_left ..),le_rfl,le_rfl,le_rfl⟩
  exact ⟨W', h1.chain (h2.chain h3), (warmed H W).boost (h2.chain h3).beta (h2.chain h3).shells,hC.raise h3.beta,
    hR f (fun i => le_max_left ..),hT f (fun i => le_max_right ..)⟩

structure Equip (H : QuantumCosts) (V : Rebuild.Census) (F : Rebuild.Fuel D) (W : Supply.Delays Θ) (B : Beam K D) (R : Radios K D)
    (e : ℕ → ℕ → Exchange) (u : ℕ → ℕ → Postage) (m : ℕ → ℕ) (f : ℕ → Focus) (c : ℕ → ℝ) (d x : ℕ → ℕ) : Prop where
  begins : Begins H V F W
  loaded : Loaded B W e u m f
  extents : Extent d c W
  routes : Routed e x W
  bumper : Bumper e W
  tx : Transmitting R W
  contest : Testing.Ringing K R.W W

theorem issue (hG : G.Simple) (hs : Package s K q e v P.l P.γ P.b) (hd : Designing K q)
    (hv : Rebuild.Open V (s.paper q v)) (H : QuantumCosts) (D : Rolls (s.paper q v)) (extraW : ℕ → ℕ → ℝ) :
    ∃ (B : Beam K D) (R : Radios K D), (∀ i j,extraW i j ≤ R.W i j) ∧
      ∀ (u : ℕ → ℕ → Postage) (m : ℕ → ℕ) (f : ℕ → Focus) (extra : ℕ → ℝ), (∀ i,0 < extra i) →
      ∃ T : Protection D,T.theta ≤ extra ∧
        ∀ (rate : ℕ → ℝ) (t : ℕ → ℕ) (F : Rebuild.Fuel D) (W₀ : Supply.Delays T), ∀ c d x,
          ∃ W : Supply.Delays T, Boost W₀ W ∧ Equip H V F W B R e u m f c d x ∧
          ∀ r : ℝ,∃ Y : Bar W,r ≤ Y.value ∧ ∀ J : Wait Y,
            ∃ I : Wait Y, Behind J I ∧ Billed I e f ∧ (∃ a : Levels G,Paid I a) ∧
              ∀ a : Levels G,Paid I a → Attenuated (B.price u) a rate t := by
  obtain ⟨B,R,hW,hR⟩ := hs.receive hd D extraW
  refine ⟨B,R,hW,fun u m f extra hx => ?_⟩
  obtain ⟨T,hT,h⟩ := hR u m f extra hx
  refine ⟨T,hT,fun rate t F W₀ c d x => ?_⟩
  obtain ⟨W,hw,hb⟩ := Begins.issue hG hv H F W₀
  obtain ⟨W',he,hL,hm,hd,hB,ht,hR,h⟩ := h rate t W c d x
  refine ⟨W',hw.chain he,⟨hb.later he,hL,hm,hd,hB,ht,hR⟩,fun r => ?_⟩
  obtain ⟨Y,hY,hy⟩ := h r
  refine ⟨Y,hY,fun J => ?_⟩
  obtain ⟨I,hI,hf,ha,h⟩ := hy J
  refine ⟨I,hI,hf,ha,fun a ha => ?_⟩
  obtain ⟨M,H,h⟩ := h a ha
  exact h.sized
end YM.Further.IterationRecipe
