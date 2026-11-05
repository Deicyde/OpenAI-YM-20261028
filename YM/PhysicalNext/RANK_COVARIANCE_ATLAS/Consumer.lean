import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.FlatLaw
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Gates
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Tag


/-!
`M : C.Makes` etc as upstream red inputs. The stronger data of the actual
cut-kernel and reweighted matches (`Interaction` here) STILL required at the
charged epochs. All origins and rows etc remain on that same course which is
where these invoices would be presented also. Don't drop any support or claim
those remaining estimates from the uncut reference identity. No assumed
commissioning of this supplier to arbitrary Wilson trajectory sizes/prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix Precision Next.Free RG FreeResolvent Tree Bid
open Next.Rank Next.Rank.Atlas Next.Rank.Tapes Next.Rank.Station Next.Rank.Peak Next.Rank.Perch Next.Rank.Flux
open Next.Rank.Spindle Marker Glyph Filter Wilson Value Ac Cells Edition Dash Extraction Org Spec OS OS.Ground Analysis
open scoped Topology BigOperators ComplexConjugate Matrix.Norms.Frobenius ContDiff ENNReal NNReal Classical

variable {G : Gauge} {C : Family G}
local notation "Y" => C.path.levels

/-- E-style use-site history receipts for the unmasked matching. Express
as EXTRA data on this C (C.Makes by itself has no such `ShapePort`). E.g. use
along with a retained Horizon from Joint.Wares etc, providing here the ties
to the same Family.Path, paid Larger, etc. Keep that witness not choosing a
mini-detached B from just the stage prices. -/
structure Binding (C : Family G) where
  world : Horizon C.path.levels
  prices : MapPrices
  share : ℕ → ℕ → ℝ
  present : ShapePort C.path.levels world share
  pays : world.Suffices prices
  sworn : ∀ N i, i≤N → ∀ p, Bid.Sworn (world.H N i) (C.S.side i p) G
  sized : ∀ i p, Bid.Larger (G:=G) (C.path.levels.clock.op i p)
  paths : ∀ N i, i≤N → ∀ p, Attached (world.H N i) (C.path.rep N p i).path

/-- One concrete portal with ready equations to give TO an estimator working
on the gauges. Doesn't say the program can generate such matching unmasked
path data. With B and C.Makes produce the identities on all their supported
slices. So an E-style use with a restart still using those same paths & clips
gets this exact flat comparator. If needed for a step prove those links for
the restart's actual Rep -- not inferred from market receipts here. A `tag`
means literal `Choices`, not any cut kernel from `Lead`! -/
def Uncut (C : Family G) (B : Binding C) : Prop := ∀ N i p (h : i<N),
    let S:=C.path.levels.clock.op i p
    let V:= C.path.rep N p (i+1)
    ∀ (F : Forest S.ratio),
      (∀ t : S.Choices,
        Precision.hessian F t V.clip V.path 0 0=treeMatrix G S F (B.world.H N (i+1)).metric ∧
          Affine.primary S F t V.clip V.path (fun _=>true) 0=treeMatrix G S F (B.world.H N (i+1)).metric) ∧
        Normal.scope stem (flatLinks B.pays h F)=(track (stamp C.path.levels N p) i).Q ∧
          ∀ v x, froth (flatColumn B.world N i p F v) x = Complex.re (Normal.reads ((stamp C.path.levels N p).path i) (fun j=> (froth v j:ℂ)) x)

variable (M : C.Makes)
include M in
lemma uncut (B : Binding C) : Uncut C B := by
  intro N i p h S V F; refine ⟨fun t=>?_,principal_match B.present B.pays h F (B.sized i p),mean_identity B.present B.pays h F⟩
  have he:= M.wilson.represents N p (i+1) h; have ht : V.clip=(C.path.levels.params (i+1)).clip :=he.clip
  rw [ht]; have hx:=he.good.paths
  exact actual_metric B.pays h F (B.sized _ _) V.path t (B.sworn N (i+1) h p) (ht ▸ hx) (B.paths N _ h p)

variable {R : Table C.book}
variable {d : ℕ} (O : HaarBudget G) (K : Cohesion C d) (X : Columns C R d)



-- A simple direct clearance condition. PreSheet use in separate file.
def Tender (k : ℕ) := Clearance (prepared C.path.levels.clock.kernel) (C.path.levels.clock.J k) d K.atoms K.fixed (wheel Y k) (clim Y k)








end YM.PhysicalNext.RankCovariance
