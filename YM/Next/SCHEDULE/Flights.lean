import YM.Next.SCHEDULE.Stadium

/-!
# Books actual-height appointments

Only the funding pass, not any guarantee that a shell or loop witness fits.
Provides work also on a cofinal sequence with scale strictly decreasing
(eligible shape for e.g. Trials.scale/window/same_stage). No independence in
period choices permitted. Offsets, separated placements and compatibility of
Born families at those points would still have to be actually proved.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Weak
open Filter Function RG RG.Supply Bid Lattice Pressure Precision Real Clock Instrument
open scoped Topology

variable {G : Gauge}



/-- Cite both heights at same k with same ordered periods. -/
lemma Bench.frames {a : Levels G} {j k : ℕ} {L : ℝ} {e : Exchange} {F : Focus} (h : Bench a j k L e F)
    (b : ℝ) (hb : 0 ≤ b) (hl : 1<L) :
    let p:=a.clock.monitor k; let M:ℝ := a.clock.coverSize k
    (∃ u m, A L p M b u m) ∧ ∀ r c : ℝ, F.positive ≤ r → r ≤ b → F.lower ≤ c → c ≤ 1 →
      ∃ u m, B L p M b r c u m := by
  let x := a.clock.hatBeta k
  obtain ⟨hE,hP,-⟩:=Deployment.clock_eqns a.clock k
  obtain ⟨hx,hy,-⟩:=h.cases_here.runway
  obtain ⟨hS,hR⟩:=h.cases_here.length
  dsimp only; rw [hP,hE]; exact heights F _ _ _ _ hy hx hl hb hS hR





variable {s : Survey G} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
variable {D : Rolls (s.paper q v)} {Θ : Protection D} {V : Delays Θ} {Y : Bar V}




end YM.Next.Scheduling.Weak
