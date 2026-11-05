import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.CoatG
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rainbows

/-! # Gauged literal tests, coverage and kernels -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Hues
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll  
open Gas Ursell Trees    Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {n c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C η r Q Y : ℝ} {R : Rep G f} {L : Side} {B : ℕ}
variable (X : Coat T F) (z : Site c→ G.El) (p : P.Funds S T) (ht : ShellAccess S G X.x W X.width C)
variable (u : Directions G f)

lemma storm_g (h : S.patch.Branches S.kernel G) (a : Stores S) (W : ℝ) (R : Rep G f) (k : Finset ℕ)
    (i : Panic c f) : (sluice X z).rawStorm (spinRow S z u) W a R k i=X.rawStorm u W a R k i := by
  unfold rawStorm; rw [banks X z u]
  let Y:=sluice X z; let t:= constantGauge z S.ratio; let U:=X.input u
  rcases i with p|p|p|p|p <;> dsimp only [Sum.elim]
  · unfold Mask.fine; rw [SectorMeasure.toll_gauge]; rfl
  · unfold Mask.noise; dsimp only [sluice,rinse, wrapY,Hot,Coat.t]; rw [feed z U X.k h,wire_gauge]
  · unfold Tags.pinMass; refine congr_arg₂ (·*·) rfl ?_
    change S.patch.predictorMass S.kernel (S.connector (gauge t U) X.k.1 p) _= _
    rw [S.updateGauged h]; exact (S.patch.bond_gauge (h:=h) ..).1
  · unfold Tags.siteMass; rw [expandAt_gauge]; refine congr_arg₂ (·*·) rfl ?_
    exact (S.patch.frame_gauged h ..).1
  unfold Contract.charges; simp_rw [RG.gauge_flags]
lemma flags_g (h : S.patch.Branches S.kernel G) (a W : ℝ) (R : Rep G f) (k : Finset ℕ) (i : WarningAt c f) :
    (sluice X z).detect (spinRow S z u) W a R k i=X.detect u W a R k i := by
  rcases i with i|i
  · change (if mandatory X.seeds X.B i then _ else _)=(if mandatory .. then _ else _); split
    next => rfl
    next he => rw [mandate,storm_g (X:=X) _ _ h]; rfl
  change (if X.Hot i∧i∉X.plaza (X.seeds.dome (304*X.B)) then _ else _)= _
  unfold detect aura; dsimp only [Sum.elim]; rw [binding]

private lemma masked_inv {n} (j : ℝ) (Q : Support n) (f : Config G n→ ℝ) (he : GaugeInvariant f) :
    GaugeInvariant (RG.masked j Q f) := by
  intro t V
  by_cases hp : Healthy j Q V
  · rw [RG.masked_eq _ _ _ _ hp,RG.masked_eq, he t V]; simpa only [Healthy,gauge_flags] using hp
  rw [RG.masked_ne _ _ _ _ hp,RG.masked_ne]; simpa only [Healthy,gauge_flags] using hp
private lemma pair_inv (f : Pairs n) (R : PathData G) (p : Clip) (s t : ℕ) (b r : ℝ) :
    GaugeInvariant (fun a=> pairValue R p b s t r a f) := by
  intro z V
  simp only [pairValue,Work.F05.pull_gauge_zero, pairTail,DataKernel.kept, PathData.ellTerms,Work.F05.slot_gauge,
    ← map_smul,duet]
lemma inhalesG {R : Rep G f} (h : Intake P T X.x R) (a : ℝ) (i : LogLetter c f) :
    (sluice X z).inhale R a (spinRow S z u) i=X.inhale R a u i := by
  unfold inhale; rw [banks X z u,mandate];
  let w := X.input u; let B := gauge (constantGauge z S.ratio) w; let b:= -orientation*R.beta
  change expo T X.x R B (gauge z X.V) _ * _= _
  have hp {d} (T : ℕ→Atom G d) (ht : ∀ i,(T i).Invariant) (b : ℝ) (f : Trans f) : translateValue R.p T b B f=translateValue R.p T b w f := by
    unfold translateValue Atom.placed B; rw [Work.F05.pull_gauge_zero];
    refine congr_arg₂ (·*·) rfl (masked_inv (G:=G) _ _ _ ?_ _ _)
    intro k U; unfold Atom.unmasked; simp_rw [Work.F05.slot_gauge]; exact ht _ _ _
  refine congr_arg₂ (· * ·) ?_ rfl
  rcases i with i|i|i|i|i|i
  · exact congr_arg Neg.neg (masked_inv _ _ _ (h.cap.labels.regular.smooth i).symmetry (constantGauge z S.ratio) _)
  · exact hp _ (fun i=> (h.cap.paths.invariant _).2.1) ..
  · exact hp _ (fun i=> (h.cap.paths.invariant _).2.2) ..
  · exact hp _ (fun i=> (h.cap.paths.invariant _).1) ..
  · exact pair_inv i R.path R.clip (till X.x) 1 R.p.threshold b _ _
  exact pair_inv i T.down T.low X.R S.patch.L.val (Pressure.temp X.x) (-b) z X.V
end YM.ConnectedActivityE6.Hues
