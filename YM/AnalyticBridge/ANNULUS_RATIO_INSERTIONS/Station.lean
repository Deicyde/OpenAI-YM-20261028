import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Inlet
import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Paired
import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Sundry

/-!
# E convention full sector price, every b label and every Φ charge

Assortment consumer. Include paired log from the actual positive window,
post-L buy now adequate for using this choice also. Express explicitly
remaining multiplier income on the exact invoice. This is NOT sufficient
off the real intake, nor promising any bounds on those remaining
terms nor on the normalized vacuum remainder. Can use even if only part of
the real consumption will be needed at once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Portfolio
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations Next.Fluctuations.Sector
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented LabelSum
open SectorNext.Remainder SectorNext.Remainder.Affine Harvest Dress FS Push.AbsoluteSums.Packets
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Joint buying sufficient for Agency. B,E aperture prices afterwards
fixed, use exact on correct V incl external seeds. Optionally price other
choices of L instead (`Inlet` route). -/
structure Rates (P : Teller G) (N : Side) (l D n : ℕ) (w K E η L κ e' x : ℝ) (Z : ChartRatio G) : Prop where
  eta : 0 < η
  width : η ≤ L
  fsct : Belongs P N L η x
  thermal : Budget P N w κ Z K E l D n (packageCost (G:=G) η L) e' x

theorem purchase (Z : ChartRatio G) (P : Teller G) (hZ : LocalRatio Z) :
    ∃ i : ℕ, ∀ N : Side,i≤N.val → ∀ᶠ w : ℝ in atTop, ∃ κ K E η Y, ∀ l D n e',∀ᶠ x in atTop, Rates P N l D n w K E η Y κ e' x Z := by
  obtain ⟨i,hi⟩ := fare Z hZ P
  refine ⟨i,fun N hr => ?_⟩
  obtain ⟨L,η,hη,hL,H⟩ := hail P N
  filter_upwards [hi N hr] with w hw
  obtain ⟨κ,K,E,hx⟩ := hw
  refine ⟨κ,K,E,η,L,fun l D n e' => ?_⟩
  filter_upwards [H,hx l D n (packageCost (G:=G) η L) e'
    (mul_nonneg (Nat.cast_nonneg _) (perSlot_pos hη hL))] with x hz ha
  exact ⟨hη,hL,hz,ha⟩

variable (A : Stores S) (T : Tube G S) (x w : ℝ) (V : Config G c) (k : S.Choices) (q : Chi)
  (d : ℝ) (J : ChartRatio G) (p : Rep G f) (F : Forest S.ratio)
  (m : Mean (G:=G) A x F)
  (X : Finset (Stores S)) {D R R' : ℕ} (uniform : Bool) (b : Finset ℕ)

variable {P : Teller G} {K E η L κ e' : ℝ} {l n : ℕ} {N : Side}
  (hJ : LocalRatio J) (hT : P.Funds S T) (hP : Rates P N l D n w K E η L κ e' x J)
  (he : S.patch.L=N) (hx : 100*(1+radiusB x)≤c.val)
  (hA : A.flags=RG.flags (temp x) V)
  (hD : d=K*fiery G x N) (hp : p.beta∈Set.Icc (Scales.y G N x/2) (2*Scales.y G N x))
  (hR : Mooring D l x R R') (hl : 11≤l) (hn : 4≤n) (hi : Itemized A l (radiusB x) X)

include hJ hT hP he hx hA hD hp hR hn hi
def seedsBought := ∑ i∈X, i.shares
omit hJ hT hP he hx hA hD hp hR hn hi in
lemma seeds_total (l : ℕ) : seedsBought (accounts A l (radiusB x))=A.shares := by
  have he := account_total (g:=fun i=> (i.shares:ℝ)) (B:=radiusB x) (l:=l) (A:=A) (fun _ _ => rfl)
  rw [← Nat.cast_sum] at he; exact_mod_cast he



variable (B : BudgetPoint) {σ C' Λ δ ω₀} (h : p.Lawful σ C' Λ δ ω₀) (hB : p.p.threshold=fiery G x S.patch.L)

include hl h hB






end YM.AnalyticBridge.AnnulusRatioInsertions.Portfolio
