import YM.Next.UV_STRESS.Aligned

/-!
# Adapt Both h-copy Pricing tasks using the singleton G09 and true mixed cost

Keep the supplied Duets physically linked over linked interval ℓ,..,k with given k **birth**.

The
architecture stops at ℓ where the marker path radii prove
a payoff.

Not necessarily the level r where coordinate matched.

No closure descent
promised through earlier past of Duets.

Rather strong addressing proposals (Format)
in this sufficient estimate, see Aligned.

If physical histories of this shape
aren't available, can just supply less restrictive direct Radial receipts, or even
weaker input physical estimates above them in Foundation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Lattice Wilson Overlay Marker RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G) {F : Extraction.Order}
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable {d N p ℓ r k h : ℕ}

def gainRead (k ℓ : ℕ) (w : ℝ) := 4*(1+(C.path.levels.params k).columns)*w / Bid.gainChart C.path k ℓ

/-- The purely material itinerary except at the target stop ℓ. -/
structure Before (X : Stair C R N p) (k ℓ d : ℕ) : Prop where
  sets : ℓ≤k ∧ k≤N
  boosts m : ℓ ≤ m → m<k → ∀ s,X.echo C m s= Ride.bump (C.S.block m).val s (fun _ => d) •
    (operation C p m).push (C.path.β N p (m+1)) (X.echo C (m+1) s)
  past m : ℓ < m → m ≤ k → (X.representation m).Active ∧ ∃ w u c d b,(X.representation m).Radial w u c d b
  origins m : ℓ ≤ m → m < k → ∀ i,(X.representation m).origins i=(operation C p m).ratio.parent ((X.representation (m+1)).origins i)





structure Numeric (k ℓ : ℕ) (W w : ℝ) : Prop where
  interest : W*gainRead C k ℓ w ≤ 1
  regular : W*slope_fee (lenses C ℓ)*(1+stencil_fee C ℓ)*gainRead C k ℓ w ≤ 1
  extra : W*(Real.sqrt (C.path.levels.clock.forcedAllowance ℓ))*gainRead C k ℓ w ≤1





/-- Require same choice of history AND exact propagation/many-point mix.
Singleton Born estimate can be asked down to an earlier reference, carrying
explicitly the lit densities thru the common interval. Not pricing a Duet on
an arbitrary synthetic chain. Intake still a true many-source price. To attest
birth need exact `echo` targets separately.
-/
structure Cov (X : Stair C R N p) (k ℓ d : ℕ) (W : ℝ) : Prop where
  budget : ∃ (s : Bid.Worth) (w : ℝ) (r : ℕ), 0≤w ∧ r ≤ ℓ ∧ Numeric C k ℓ W w ∧
    Bid.roomCost C.path.levels s ∧ Bid.Bank s C.path.levels ∧ stencil_at C ℓ d ∧
      (X.representation ℓ).Active ∧ Mix.Stubs.far (A:=X.representation ℓ) ∧
        (∃ T : Mix.Stubs (X.representation ℓ), T.intake (fun _ => W)) ∧
        ∀ i : V, ∃ P : Bid.Duet C.path (C.labels.level d) N p r k,
          Bid.Duet.Woke P C.params s (C.localSection d) w ∧
            Nonempty (GridPattern C P (X.representation ℓ) i) ∧
              ∀ m : ℕ,ℓ ≤ m → m ≤ k → X.echo C m (R.fire i)=(P.voice m).density (P.atPoint m) (C.localSection d) (C.path.rep N p m)






end YM.Next.UVStress
