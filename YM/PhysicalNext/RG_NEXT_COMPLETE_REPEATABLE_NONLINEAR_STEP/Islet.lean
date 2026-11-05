import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Channels
import YM.Extra.SOURCE_HISTORIES.Tickets
import YM.Further.ROOTED_INTERACTING_REMAINDER.Station
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sash

/-!
# Traveller for an isolated regular singleton

One θ average with the actual charging labels and their *full* E6
singleton dependency stencil. Force output flags allowed away from it:
even the Addressed law on these. Use after selecting any fixed weighting
of forests determined independently of the field. θ predictor reference
probability in these formulas is JUST the attempt law (uniform on possible
choices); no pretending that's the likelihood law elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat
open Lattice Set MeasureTheory Tree Function Wilson Pressure RG Next.SectorChange Next.Fluctuations
open Push.AbsoluteSums Push.SectorMeasure JointLoad JointLoad.Heir JointLoad.Psalm
open ConnectedActivityE6 AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussian
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {c f : Side} {S : StepData c f} {R : Desk G S}

def headed (Z : RegularAddress f) (x : ℝ) (l : ℕ) : RegularAddress c :=
  ⟨S.ratio.parent Z.site,yFoot S Z.support x l,halo_subset _ _ (Finset.mem_image_of_mem _ (show Z.site∈inspected Z.support from Finset.mem_union_left _ Z.anchor))⟩



lemma nearby_zero (X : Support f) (l : ℕ) (x : ℝ) :
    Disjoint (bareStores S).place (yFoot S X x l) := by simp [bareStores,Stores.place]

-- Forest assembly arguments A are full vector, not a posterior resample.
section ticket
variable {Λ : Type} [Fintype Λ] [Nonempty Λ] (forest : Λ → Forest S.ratio)
    (R : Desk G S) (l r : ℕ) (hB : 0 < radiusB R.betaHat) (hl : 500 ≤ l) (hr : l+5≤ r) (D : JointLoad.Heir.Record) (i : ℕ)

abbrev projects (R : Desk G S) (l : ℕ) (i : ℕ) : RegularAddress c := headed (S:=S) (R.labels.reg i) R.betaHat l

/-- Weighted θ and forest average, mask-free principal calculation. -/
def script : Heir.Script G S (R.labels.reg i).support (projects R l i).support r R.betaHat where
  Tag := Λ × S.Choices
  Keys p := Key (R.labels.reg i).support R.betaHat (forest p.1)
  chart _ := bareStores _
  forest p := forest p.1
  θ p := p.2
  fits p := seatsAt _ _ l hB hl (forest p.1) _ (nearby_zero ..)
  profile p := Pitch.muffler R _ D
  moves p := guard_natural R.profile _
  coefficient _ := (Fintype.card (Λ × S.Choices):ℝ)⁻¹
  admissible := by
    let n : ℝ := Fintype.card (Λ × S.Choices)
    have hh : 0<n := Nat.cast_pos.mpr Fintype.card_pos
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change n*|n⁻¹| ≤ 1; rw [abs_of_pos (inv_pos.mpr hh),mul_inv_cancel₀ hh.ne']
  fields := (Footprint.inspected_price S.ratio l _ _ hB).trans (Corona.halo_mono (Nat.mul_le_mul_right _ hr) (Finset.Subset.refl _))

abbrev seeded (R : Desk G S) (V : Config G c) : Stores S :=
    {bareStores S with flags := RG.flags (temp R.betaHat) V}

variable {V : Config G c} (h : Healthy (temp R.betaHat) (projects R l i).support V)
    (hp : ∀ (F : Forest S.ratio) (k : S.Choices), (fog (seeded R V) F R.tube R.betaHat V k).PosDef)



end ticket
end YM.PhysicalNext.Repeat
