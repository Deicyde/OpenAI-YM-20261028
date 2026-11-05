import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Ember
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Ride
import YM.Planned.ATOM_FORCED_ESTIMATE.Moments

/-!
# Common-family zero-order use with an actual selected compulsory portfolio

Requires the tower apertures of that very portfolio, and local OTHER letter
inputs only when its gate isn't zero. Holder on the SINGLE conditional law
again. Do NOT need to break up `brigade` or even localize those other bounds
away from its support. Direct ratio insertions via `Cradled` & `Arc.r4` (not
position chain exponents), expanded operand via the new Lease. Can e.g. test
partially grouped selections with both conventions (but not a statement that
a cascade with arbitrary insertions is an unmodified density integrand!).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad
open Function Filter Metric Set Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian Spot Spot.Programme Notice Tariff
open AnalyticBridge.AnnulusRatioInsertions AnalyticBridge.AnnulusRatioInsertions.Prism Breeze Parade SectorNext.Remainder Portfolio
open MeasureTheory Push.SectorMeasure Presented Wisps Schur Bid Planned.Forced.Moment Matrix
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

structure Paint where
  u : ℝ
  v : ℝ
  a : ℝ
  M : ℝ
  H : ℝ
  tint : ℝ

variable {G : Gauge} {c f : Side} {S : StepData c f} {d : Desk G S} {Q : Kiosk} {Pt : Teller G} {P : Patch}
    {Z : ChartRatio G} {χ : Chi} {θ E x r : ℝ} {k n power : ℕ}
    {ι H R α β γ : Type} [Fintype ι] [Fintype H] [Fintype R] [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ]
    {A : Stores S} {F : Forest S.ratio} {κ : S.Choices} {V : Config G c} {X : Support c}
    {l : Viewport (spectacle d A F κ) X H R ι} {D : (spectacle d A F κ).Slices} {b : Finset ℕ} {q : Programme D b} {z : q.Run α β γ}
    {s : Seats l z} {a : Notice l} {B : Reading a z} {M : Income α β γ (H⊕R)}

def lumped (P : Paint) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (G : Gauge) (Γ : Finset (Pick (Active A x F))) :=
  ∏ i∈Γ,P.tint * fares S G A F x P.u P.v P.a P.M P.H i

/-- Keeps separate the L4 prices of the literal *unexpanded block*
ratio letters  as implemented in Precipitation, usable at once
with any portfolio and the leased word. -/
def Medium (P : Paint) (G : Gauge) (Y : Patch) (Pt : Teller G) (x : ℝ) : Prop :=
  ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=Y → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
  ∀ (A : Stores S) (F : Forest S.ratio) (κ : S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
  ∀ β ∈ Icc (Scales.y G Y.L x/2) (2*Scales.y G Y.L x), ∀ (χ : Chi) (d : ℝ), 0<d → d ≤ 1 → 2*d<firstRadius G →
  ∀ Γ : Finset (Pick (Active A x F)), let v := Arc.wires Γ (Arc.coal (soaked S T A F κ V χ x d (coupling β)))
    let U := (piHaar G (Frozen A x F)).prod (Gaussian.cloud (fog A F T x V κ))
    Measurable v ∧ Power U 4 (fun y => ‖v y‖) (lumped P A F x G Γ)

lemma painting (G : Gauge) (Y : Patch) (Pt : Teller G) (hY : Y.Branches Pt.bind G) : ∃ P : Paint, ∀ᶠ x in atTop, Medium P G Y Pt x := by
  obtain ⟨η,L,hη,hL,h⟩ := visions G Y Pt hY
  obtain ⟨m,hm,H⟩ := Arc.r4 (G:=G) L (hη.trans_le hL)
  obtain ⟨u,v,a,M,D,hu,hv,ha,hM,hD,hP⟩ := oasis Y Pt hY
  refine ⟨⟨u,v,a,M,D,m⟩,?_⟩
  filter_upwards [hP L (hη.trans_le hL),h] with x hx h
  intro c f S T hS hr ht A F κ V hV β hβ χ d hd he hi Γ v' U
  obtain ⟨hC,h1,-⟩ := h S T hS hr ht A F V κ hV
  obtain ⟨⟨hw,hh⟩,hz,hγ⟩ := hx S T hS hr ht β hβ A F κ V χ d hV hd he hi Γ
  have hp : Measurable v' := Finset.measurable_fun_prod Γ fun i hi => Arc.readable _ _ (hz i hi)
  obtain ⟨hI,hB⟩ := H (piHaar G (Frozen A x F)) hC.posSemidef h1 hw hh hz hγ
  have heq y : ‖v' y‖^4 = v' y ^4 := (show Even 4 by decide).pow_abs _
  refine ⟨hp,Finset.prod_nonneg (fun i hi => mul_nonneg (zero_le_one.trans hm) (hw i hi).1), Eventually.of_forall fun _ => norm_nonneg _,hp.norm.aestronglyMeasurable,?_,?_⟩
  all_goals simp_rw [heq]; assumption




namespace Day
variable {H' Y B0 σ e' : ℝ} {l' D' N : ℕ} {w : Paint}
  (h : Day Q θ E k n d) (hc : Calling Pt d.chart χ power r d.betaHat d) (hC : Clearing (spectacle d A F κ) V)
  (hP : Rates Pt S.patch.L l' D' N d.W r B0 H' Y σ e' d.betaHat d.chart) (hw : Medium w G S.patch Pt d.betaHat)
  (o : Site c) (hT : Terms s V) (R0 R1 : ℕ) (hR : Mooring D' l' d.betaHat R0 R1) (hN : 4≤N)
  (X' : Finset (Stores S)) (hi : Itemized A l' (radiusB d.betaHat) X') (Γ : Finset (Pick (Active A d.betaHat F)))
include h hc hC hP hw hT hR hN hi


end Day
end YM.PhysicalNext.JointLoad
