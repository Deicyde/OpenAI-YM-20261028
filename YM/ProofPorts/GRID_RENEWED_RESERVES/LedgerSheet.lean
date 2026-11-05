import YM.AnalyticNext.GRID_STOP_ATTENUATION.Coarrival.Open
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Path
import YM.Push.GRID_APPROXIMATION.Roll
import YM.Push.LOCAL_SPLITTING.Atoms




/-! # Packed Wire

Wire.Wire can be larger. Use a COMMON choice of Pack lane.
No merging before the mask, and support list x retained even for zeros.
Resources consumed on forced Pack registration pays actual threshold and
support every time.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GridRenewal.Mag
open MeasureTheory Filter Function Lattice RG Wilson Pressure Source Labels
open Push.Local YM.AnalyticNext.GridStop Multi Push.RelayDifference
open scoped Classical Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side} {d : ℕ}

/-- Pre-mask germs & Pack data. We carry the *unit* separately.
Have to STORE the same supports for all Linear operations (below).
`Pack.ofAddress` includes exact forced inventory. Genuine addresses
in use checked at the actual threshold, no canonical-flags substitutions. -/
abbrev Film (G : Gauge) (n : Side) := (ℕ → Config G n → ℂ) × (Pack n → Config G n → ℂ)
abbrev Tablet (F : Frame G d) (n : Side) := F.Coeff × Film G n
variable {F : Frame G d} {o : Site n} {P : Rep G n} (X : ℕ → Support n) (h : Multi.Room P)
variable {A : Hol G} {S : SectionData F}

def applyRoom : Tablet F n →ₗ[ℂ] Coarrival.Wire F n where
  toFun u := (u.1,u.2.1,Primary.allocate h u.2.2)
  map_add' u v := by
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change Primary.allocate h (u.2.2+v.2.2)=Primary.allocate h _ + Primary.allocate h _; funext i
    unfold Primary.allocate; dsimp only [Pi.add_apply]; split; rfl; exact (zero_add 0).symm
  map_smul' z u := by
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change Primary.allocate h (z • u.2.2)= z • Primary.allocate h _; funext i
    unfold Primary.allocate; dsimp only [Pi.smul_apply]; split; rfl; exact (smul_zero z).symm









variable {X} {r s w δ t a b : ℝ} {u v : Film G n}

/-- Entry-wise prices *on the support dictionary at this scale*, not maximised across a full volume. -/
structure GaugeFilm (P : Rep G n) (X : ℕ→Support n) (o : Site n) (r s a b : ℝ) (u : Film G n) : Prop where
  center i : o∈X i
  smooth i : P.p.Regular (X i) (u.1 i)
  live i : Multi.Legible P.p i (u.2 i)
  carry i : u.2 i ≠ 0 → o∈i.zone
  pass : ∃ f : ℕ → ℝ, SumBudget (fun i => burn P.p r (X i)*f i) a ∧ ∀ i,P.p.supBounds o (X i) (u.1 i) (f i)
  badge : ∃ f : Pack n→ℝ,(∑ i,burn P.p s i.zone*f i)≤ b ∧ ∀ i,0≤f i∧∀ U,‖u.2 i U‖≤f i

















variable {x y : Tablet F n}
structure Stylus (P : Rep G n) (X : ℕ→Support n) (o : Site n) (A : Hol G) (r κ paid : ℝ) (x : Tablet F n) : Prop where
  currency : 0 < κ
  bound : ∃ a b : ℝ, GaugeFilm P X o r r a (κ*b) x.2 ∧ a+b ≤ paid
  dark i : x.2.1 i 1=0
  post i : Nonwrapping (X i) o → A.PiVanish d o (x.2.1 i)

variable {paid κ : ℝ}















end YM.GridRenewal.Mag
