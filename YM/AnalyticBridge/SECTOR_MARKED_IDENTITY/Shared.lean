import YM.AnalyticBridge.SECTOR_MARKED_IDENTITY.License
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen


set_option warningAsError false

/-!
# Sum in the SAME endpoint-pair prescription and Haar normalization

Sufficient hypotheses, to be booked in the committed consumer. The positive
β clause is explicit; not inferring prices by assuming every flag record is
consistent. All equalities at all V, also wrong flags. `outer` budgets the
nested integral and its absolute version even for use with coarse spectators.
As in `SectorChange.accounted`, no assertion one can interchange dV inside
the V-dependent Gaussian. `balance` gives an exact total of the fully
prefactored absolute integrals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Marked
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open Gaussian Rows YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid
open YM.Push.SectorMeasure YM.Next.Fluctuations.Sector
open YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {x w : ℝ}
variable (T : Tube G S) (x : ℝ) (R : Rep G f)
  (F : Forest S.ratio) (D : Allocation G S x w) (q : Chi) (J : ChartRatio G) (d : ℝ)

/-- Noncircular socket shared by all sources. -/
structure Bought : Prop where
  lawful : ∃ σ n Λ δ l : ℝ, R.Lawful σ n Λ δ l
  funds : ∃ P : Teller G, P.Funds S T
  beta : 0 < R.beta
  fitted : Fits T R x
  permits (A : Stores S) (k : S.Choices) (V : Config G c) : A.flags=RG.flags (temp x) V →
    Permitted x V k A F D J d R.beta (fog A F T x V k) (meanLog A F T x V k q d)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def amount (u : Config G f → X) (A : Stores S) (k : S.Choices) (V : Config G c) : X :=
    afterChange T x V k A R (shots S x) F D q J d (fog A F T x V k) (meanLog A F T x V k q d) u

/-- Equal to weighted nested integral of the norm, NOT norm of answer. -/
def magnitude (u : Config G f → X) := amount T x R F D q J d (fun U => ‖u U‖)

def paidSum (u : Config G f → X) (V : Config G c) :=
    ∑ A, ∑ k, amount T x R F D q J d u A k V

lemma magnitude_nested (u : Config G f → X) (A k V) :
    let C := fog A F T x V k; let m := meanLog A F T x V k q d
    magnitude T x R F D q J d u A k V = outside T x V A R F J C *
      ∫ Y, (∫ z, ‖ink T x V k A R (shots S x) F D q J d C m u Y z‖ ∂cloud C)
        ∂piHaar G (Frozen A x F) := by
  intro C m; unfold magnitude amount afterChange; simp_rw [ink_norm]; rfl

variable {T x R F D q J d}

namespace Bought
variable (L : Bought T x R F D q J d)
include L

lemma branches : S.patch.Branches S.kernel G := L.funds.elim fun _ h => funds_branch h

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace X]
  {u : Config G f → X}

/-- Every summand has a license, even before gauge-invariant assembly. -/
theorem fixedTerm (he : Envelope u) (A : Stores S) (k : S.Choices) (V) :
    Permission T x V k A R (shots S x) F D q J d (fog A F T x V k)
      (meanLog A F T x V k q d) u := by
  obtain ⟨σ,n,Λ,δ,l,h⟩ := L.lawful
  obtain ⟨P,hT⟩ := L.funds
  exact fixed T x V k A R _ F D q J d h hT L.fitted (L.permits A k V) he

theorem row (he : Envelope u) (A V) :
    output D F R.beta u A V = ∑ k, amount T x R F D q J d u A k V :=
  Finset.sum_congr rfl fun k _ => (L.fixedTerm he A k V).result

/-- Actual Haar-block `push` with absolute-integrability receipt already
available termwise. -/
theorem apply_push (he : Envelope u) (hi : GaugeInvariant u) : S.push R.beta u = paidSum T x R F D q J d u := by
  funext V; unfold paidSum; simp_rw [← L.row he]; exact (push_columns D F R.beta u L.branches (Env.integrableX he _) hi V).symm

omit [CompleteSpace X] in
lemma joint_before (he : Envelope u) (A k) :
    Envelope (fun a : F.Slice G × Config G c => before x a.2 k A R F D u a.1) := by
  let g (k : S.Choices) (a : F.Slice G × Config G c) :=
    through S F R.beta a.2 (fun _ i => u (F.drape i)) k a.1
  apply D.portion_env L.branches A F g k
  have hm : Measurable (fun a : F.Slice G × Config G c => F.drape a.1) :=
    F.continuous_drape.measurable.comp measurable_fst
  exact Env.scale (env_tagged R.beta k L.branches hm measurable_snd) (Env.along he hm)

/-- Permits following the inner calculation by the coarse Haar integral,
or multiplication by a coarse probe. Nested integral order. -/
theorem outer (he : Envelope u) (A k) :
    Envelope (amount T x R F D q J d u A k) ∧ Envelope (magnitude T x R F D q J d u A k) := by
  have hh := L.joint_before he A k
  constructor
  · rw [show amount T x R F D q J d u A k = fun V => ∫ a, before x V k A R F D u a ∂F.order G from
      funext fun V => (L.fixedTerm he A k V).result.symm]
    exact Env.marginal hh _
  rw [show magnitude T x R F D q J d u A k = fun V => ∫ a, ‖before x V k A R F D u a‖ ∂F.order G from
    funext fun V => (magnitude_nested ..).trans (L.fixedTerm he A k V).absolute.symm]
  obtain ⟨hm,B,hB⟩ := hh
  apply Env.marginal (g:=fun (y : F.Slice G × Config G c) => ‖before x y.2 k A R F D u y.1‖)
  exact ⟨hm.norm,B,fun y => (Real.norm_of_nonneg (norm_nonneg _)).trans_le (hB y)⟩



end Bought
end YM.Next.SectorChange.Marked
