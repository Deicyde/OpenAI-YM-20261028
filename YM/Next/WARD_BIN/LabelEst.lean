import YM.Next.WARD_BIN.Cloud
import YM.Next.WARD_BIN.Gates
/-!
# Actual centered comparison bound

At an arbitrary fixed stopping level, don't charge replicated marker count to
discard it. Use the entire Lane.works incl roots, density push and unmarked
normalizer to estimate all path phases; specialize to this tiling using literal
orientation. Extend sufficiently-slow fused wages to all ℓ centers later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Array
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Overlay Bid Wheels Crest Extraction Cells
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {C : Family G} {W : Worth} {F : Extraction.Order}
  {d ℓ N p i l m : ℕ} {c u x v w : ℝ} {A : Chart C d} {Z : Shelf A}













-- Need a θ once globally, below can choose arbitrarily less than G09 γ.
def gust (T : Schedule) (θ : ℝ) (N : ℕ) := Real.exp (-θ*T.scale N)


-- both entrances: stage conditions mesh uniform (Door, Fits...) and
-- at physical period need *later mesh* for Cloud bill.
structure Loggia (Z : Shelf A) (ℓ m : ℕ) : Prop where
  deep : ℓ ≤ m
  shore : C.ref d ≤ m
  T i : m ≤ i → Door C ℓ i d
  quota i : m ≤ i → ∃ b, Quota C d b i ∧
    ∀ N p, ∀ h : Z.horizon ≤ N, i < N → Volley (Z.page N p h) b i


structure Veranda (A : Chart C d) (N p ℓ m : ℕ) : Prop where
  fit : m≤N
  bearing : A.Bearing N p
  circle : coverNumber (face C N p).B (native C N p A.art.cover) ≤ 1
  size : cord A.art.cover+cord A.art.cover < (C.path.levels.clock.coverSize N)^2
  costs : Fintype.card (Cloud.Strong (Cast C ℓ p))*(Real.exp ((A.art.cover.card*Fintype.card (Cast C ℓ p):ℕ)*cash C N)-1) ≤
      κ C.path N*cap₂ C N



end YM.WardBin.Array
