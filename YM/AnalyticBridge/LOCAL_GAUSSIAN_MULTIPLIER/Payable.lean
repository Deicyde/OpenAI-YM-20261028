import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Domination

/-!
# Integral consumer, unforced and value licenses

Prices are per LOCAL multiplier. Does not grant summation over parents,
different placements, polynomial reanchoring counts or the schedule.
`Rally` carries a possibly quite different lease on a neighborhood
(needed only qualitatively). Especially don't infer it across a boundary
of a profile/flag from one set of values on the supported configurations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian
open Next.SectorChange.Rows YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented Metric
open Curtain Tariff Spot.Programme Spot Notice Moments Integral
open ProjectorNext.Equivariance
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {u : Spot d}
  {H R K α β γ : Type} [Fintype H] [Fintype R] [Fintype K] [DecidableEq H] [DecidableEq R]
  [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
  {X : Support c} {l : Viewport u X H R K} {D : u.Slices} {b : Finset ℕ} {q : Programme D b}
  {n : q.Run α β γ} {a : Notice l}
namespace Reading
variable {B : Reading a n} {V : Config G c} {r t : ℝ} {k : ℕ} {o : Site c} {T E : Tariff α β γ (Component G H R)} {Ω : Set (Config G c)}

namespace Rally

omit [Fintype K] in
/-- A route to the strictly LOCAL qualitative `_Rally` input (continuation
need not keep sharp budgets). Do not use positive-definite branch without
checking, even on the center and with empty-index cases. -/
lemma entrance (hr : Ready d.chart d.g r) (ht : 0 ≤ t) (hh : t < r) (hv : Ω ∈ nhds V)
    (hs : B.Shutter Ω t)
    (hp : ∀ᶠ i in nhds V, Clearance B t E i (d.out.dirBound o) k)
    (hC : ContinuousAt (fun w => coat (a.C w)) V) : ∃ s : Set (Config G c), V∈s ∧ Rally B o k t r s E := by
  have he := hC.inv₀ (coat_pos (hp.self_of_nhds).pane).ne'
  let M := (coat (a.C V))⁻¹+1
  have hh' : (coat (a.C V))⁻¹ < M := by unfold M; linarith
  have hl : ∀ᶠ i in nhds V,(Clearance B t E i (d.out.dirBound o) k ∧ i∈Ω) ∧ (coat (a.C i))⁻¹≤ M :=
    (hp.and hv).and (he.eventually (ge_mem_nhds hh'))
  obtain ⟨s,hx,ho,hV⟩ := _root_.eventually_nhds_iff.mp hl
  exact ⟨s,hV,hr,hh,ht,ho,fun i hi => hs i (hx _ hi).1.2, ⟨M,(inv_pos.mpr (coat_pos (hp.self_of_nhds).pane)).le.trans hh'.le,
    fun i hi => (hx _ hi).2⟩, fun i hi => (hx _ hi).1.1⟩








end Rally

namespace Clearance



omit [Fintype K] in
/-- Also show the β aggregation truly at these rows before estimating. -/
lemma same_core (h : Clearance B t T V (d.out.dirBound o) k) (hV : u.Clearing V) :
    ∀ i∈T.core,∃ I : RowPosts c f,n.settled i=.inl I ∧
      ∀ p : Visual u, B.logs i V (l.info p)=u.residualFee V p I := by
  intro i hi; obtain ⟨I,he⟩ := h.action i hi
  refine ⟨I,he,fun p => ?_⟩
  rw [B.logsReached i V p hV,q.constPage V p _ hV (n.settles i),he]; rfl
end Clearance

/-- Value-only packet criterion for rough/hard output use. -/
structure Rough (B : Reading a n) (V : Config G c) (T : Tariff α β γ (Component G H R)) : Prop where
  pane : (a.C V).PosDef
  bought : Peak (a.C V) T.capacity
  leased : T.Lease
  action : Residues n T
  charges p : B.HeldAt V p → Earn (B.marked V) p T p.2


end Reading
end YM.AnalyticBridge.LocalGaussian
