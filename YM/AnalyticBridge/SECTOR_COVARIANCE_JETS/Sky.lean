import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Pan
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen

set_option warningAsError false

/-!
Period uniform on the actual step data, exact GaussianSector endpoint metric.
Use on fixed-L post-prices only prior to the choice of entrance threshold.
Different arbitrary W ok with same radius-test but no claim that a costed
C from one can be silently switched to the other inside push.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree Matrix
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent (native Bundle Cost)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k n : ℕ} {σ d r C x η g b : ℝ}

/-- The C of Gaussian.SectorChange evaluated on the *selected* geometry.
It does not change as more of the affine constant `source` is read (on Y,
chart extension, indicators etc.) but is on the full ACTUAL active list.
Completion.lean's `stocked` prices unused positions by identity.
-/
def prism (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x : ℝ) (V : Config G c)
    (B : Directions G c) := fog A F T x (increment V B) t



structure Sky (G : Gauge) (p : Teller G) (P : Patch) (x C r : ℝ) (k : ℕ) (σ b η g : ℝ) : Prop where
  growth : 120≤radiusB x
  branch : Trust G p P x C r k σ η
  shade : ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → p.Funds S T →
    100*(1+radiusB x) ≤ c.val → ∀ (V : Config G c) (t:S.Choices) (A : Stores S) (F : Forest S.ratio),
      A.flags=RG.flags (temp x) V → ∀ B : Directions G c, ‖B‖ ≤ r →
        Installed (front A F) (pilot T A F t x V) (panels A F) B σ (rate (-b) (radiusB x)) C g k

/-- Main actual production theorem. Fixed `P` (including L) and
`Teller`. `x=hatBeta_m`, chart directions of `B` here unscaled. Threshold
here pays analytic and gap slacks even in *non-flag-licensed* patches within
`r` sup-log of the licensed field WITH FLAGS HELD, where the data remain
honest finite-order germs. Extension at equality ordinary exp-log jets with
same bona fide formula on the real branch. Flags/Allocation themselves are only to
multiply the contribution, are NOT objects differentiated here.

`Sky.shade`: Π_u and inverse jets and discrepancies, C and C
inverse/precision and residual exponential estimates.

Price uses *both*
row and column weights and actual window.

Every atom/location kept; 's
normalized t,t' price is available from `spendDirection` (order zero in E
uses constant, every j>0 stronger costing ε^j in normalized directions).

Conditional on same physical row/branch inputs as `committed` theorem.
This is not the Schedule/Density equality, log determinant estimates, or
pricing of remaining multipliers. -/
theorem fromTeller (P : Patch) (G : Gauge) (p : Teller G) (hB : P.Branches p.bind G) (k : ℕ) :
    ∃ C r σ b η g : ℝ, 0<C ∧ 0<r ∧ 0<σ ∧ 0<b ∧ 0<η ∧ 0<g ∧ ∀ᶠ x : ℝ in atTop,
      Sky G p P x C r k σ b η g := by
  obtain ⟨C,r,d,η,hc,hr,hd,hη,h⟩ := trusting P G p hB k
  obtain ⟨M,σ,b,g,hm,hC,hs,hu,hb,hg,H⟩ := aperture P G hd hc hη k
  refine ⟨M,r,σ,b,η,g,hm,hr,hs,hb,hη,hg,?_⟩
  filter_upwards [h,H] with x hx hz
  obtain ⟨hp,hE⟩ := hz
  refine ⟨hp,?_,?_⟩ <;> intro c f S T hS hT hv V t A F hA B hU
  · obtain ⟨h1,h2,h3,h4,h5,h6⟩ := hx S T hS hT hv V t A F hA B hU
    intro g H; exact ⟨reducePay h1 hu hC le_rfl, reducePay h2 hu hC le_rfl,h3,h4,fun z =>
      (h5 z).trans (mul_le_mul_of_nonneg_right hC (sumSq_nn z)),h6⟩
  obtain ⟨-,h1,h2,-,-,-⟩ := hx S T hS hT hv V t A F hA B hU
  apply hE (front A F) (pilot T A F t x V) (panels A F) B _ ?_ h1 h2 (boards A F G hp)
  · intro y hy; rw [← hS]; exact (terraced S G A F x _ hy).1
  intro B; rw [pilot_eq]; unfold Matrix.IsSymm; rw [transpose_mul,transpose_transpose]

/-- Quick view of just the matrices used in the shifted measure and its
adjustment. Consumers should read the *same fields*, not
re-generate a direction by varying the sector decisions. -/
lemma directly (P : Patch) (p : Teller G) (hp : Sky G p P x C r k σ b η g) (hc : 0<C)
    (S : StepData c f) (T : Tube G S) (hP : S.patch=P) (hT : p.Funds S T) (hg : 100*(1+radiusB x)≤c.val)
    (V : Config G c) (t:S.Choices) (A : Stores S) (F : Forest S.ratio) (hV : A.flags=RG.flags (temp x) V)
    (B : Directions G c) (hh : ‖B‖ ≤ r) :
    let A' := pilot T A F t x V; let C' := prism T A F t x V; let p := front A F (G:=G) (x:=x)
    let y := rate (-b) (radiusB x)
    (C' B).PosDef ∧ (A' B).PosDef ∧
      RatesPaid p p σ C k C' B ∧ RatesPaid p p σ (y*C) k ((fun x => (C' x)⁻¹)-A') B ∧
      RatesPaid p p σ C k (fun x => (C' x)⁻¹) B ∧ RatesPaid p p σ (y*C) k (C'-(fun x => (A' x)⁻¹)) B := by
  intro A' C' p' y; have he := hp.shade _ T hP hT hg V t A F hV B hh
  have hi : obscure (panels A F) A' = C' := rfl
  rw [← hi,← invertOnly,← invertOnly]; refine ⟨he.definite,(hp.branch _ T hP hT hg V t A F hV B hh).2.2.2.1,he.mist,he.precision,?_,he.unmask⟩
  simpa only [drain,add_zero,inv_one,mul_one] using ((he.second.full 0 le_rfl).mild le_rfl hc.le)
end YM.AnalyticBridge.Covariance
