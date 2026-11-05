import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Filaments
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Loyalty

/-!
# Parents tested through stencils. Tails NEED old R at pinned points

Even with `pull` on actual torus orientations, and actual `m`-kept arrays from old scale.
Require R belongs to same order and Fits (as step). This is a numerical proof for ancestor gatherings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Coverage.Shed
open Function Lattice RG Precision Wilson Pressure Pressure.Stores MeasureTheory Push.SectorMeasure
open Matrix Push.SectorMeasure.Oriented Push.AbsoluteSums Tree Next.Fluctuations Filter Win Win.Promise Finset
open Centered Aff Aff.Mint Wages Jewels   Mixed Work.E03 Exterior Bloch Turn Calls
open scoped Topology BigOperators ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S}

variable {x C : ℝ} {A A' : Stores S} {F : Forest S.ratio} {Y : Mint T F A x} {Y' : Mint T F A' x} {X : Support c}

-- native support bridge
lemma slots_track (s : Slot) (x : Site n) (V W : Config G n)
    (h : Agrees ↑(s.stencil.image (fun v => wrap n v+x)) V W) : s.atSite V x=s.atSite W x := by
  apply s.covered (expandAt x V) (expandAt x W)
  intro j hj hv
  unfold expandAt
  apply h; exact mem_image_of_mem _ hj
  exact mem_image.mpr ⟨_,hv,by dsimp; rw [map_add,wrap_step]; abel⟩

lemma bundled {d : ℕ} (s : Fin d→Slot) (x : Site n) (V W : Config G n) (p)
    (h : Agrees ↑(Paths.bundle x s) V W) : (s p).atSite V x = (s p).atSite W x := by
  apply slots_track
  apply agrees_mono h; intro i hi
  exact mem_insert_of_mem (mem_biUnion.mpr ⟨p,mem_univ p,hi⟩)

lemma mask_track (s : Support n) (p : Config G n → ℝ) (V W : Config G n) (h : LocalOn ↑s p)
    (hp : Agrees ↑(inspected s) V W) (t : ℝ) : masked t s p V=masked t s p W := by
  have ht := RG.flags_agree t V W s hp
  have hy := h V W (agrees_mono hp (Finset.coe_subset.mpr Finset.subset_union_left))
  have hv : Healthy t s V ↔ Healthy t s W := by simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,ht]
  by_cases hh : Healthy t s V
  · rw [masked_eq _ _ _ _ hh, masked_eq _ _ _ _ (hv.mp hh),hy]
  rw [masked_ne _ _ _ _ hh, masked_ne _ _ _ _ (mt hv.mpr hh)]

lemma for_atom {k : ℕ} (b : Atom G k) (i : Site n) : LocalOn ↑(b.footprint i) fun U => b.unmasked U i := by
  intro V W h
  rw [Paths.atom_foot] at h
  unfold Atom.unmasked; simp_rw [bundled b.leg i V W _ h]

lemma for_rim {Λ : ℝ} (R : PathData G) (j : Buttons n) (K : Clip) (t : ℝ) (d : ℕ) (p : Site n → Site c)
    (hp : ∀ i a,separation (p i) (p (i+step a))≤1)
    (he : Bid.LaneCounts R x t K Λ d p) (V W : Config G n)
    (h : Agrees ↑(fringe R j) (pull j.1 0 V) (pull j.1 0 W))
    (hh : AgreeNear p (p j.2.2.1) (radiusB x/50+4) (pull j.1 0 V) (pull j.1 0 W)) :
    chiffon R K j (till x) d t V= chiffon R K j (till x) d t W := by
  let u := j.2.2; let U := pull j.1 0 V; let Y := pull j.1 0 W
  have hv i := bundled (Paths.duplex R j.2.1 j.2.2.2) j.2.2.1 U Y i h
  have hx : R.ellTerms (u.1,j.2.1) u.2.1 U=R.ellTerms (u.1,j.2.1) u.2.1 Y := congr_arg (fun v : G.Color => (R.row j.2.1 u.2.1).1 • v) (hv 0)
  have hy : R.ellTerms (u.1,j.2.1) u.2.2 U=R.ellTerms (u.1,j.2.1) u.2.2 Y := congr_arg (fun v : G.Color => (R.row j.2.1 u.2.2).1 • v) (hv 1)
  unfold u U Y at *
  unfold chiffon drain
  simp only [kept_rows _ hp R he _ hh,hx,hy]

section residues
variable (h : Shed F Y Y' X) {P : Teller G} (hT : P.Funds S T) (hC : Optic T x C) {z z' : ArrayR G f} (hx : Spans S X (radiusB x) z z')
    (R : Rep G f)

include h hT hC hx






variable {σ c' Λ δ w : ℝ}








omit hT hx in
lemma resets (i : Buttons c) (β : ℝ) (hp : rib T.down (plain c) x i ⊆X) : reset i x β T Y.V= reset i x β T Y'.V := by
  have he := hC.giant
  let H := fringe T.down i; let b := radiusB x
  have hZ p (hi : p∈H) : lens X (i.1.act p) (30*b) := by
    have hx : i.1.act p∈partWay T.down (plain c) i := mem_image_of_mem _ (mem_image.mpr ⟨_,hi,collar p⟩)
    exact (labels _ _ _ _ hx (show 30*b ≤ 120*b by omega)).extends_to hp
  have hv := pull_agreesCoarse i.1 i.2.2.1 (D:=radiusB x/50+4) (fulcrum h _ (30*b) _ (by omega)
    (hZ i.2.2.1 (mem_insert_self ..)))
  unfold reset; refine congr_arg _ (for_rim T.down i _ _ _ _ (fun i j => Work.E03.sep_step i j) hC.down _ _ ?_ hv)
  intro j hj _
  exact pull_agreesCoarse i.1 j.1 (D:=1) (h.fulcrum (i.1.act j.1) (30*b) _ (by omega) (hZ _ hj)) j (by simp)
end residues
end YM.AnalyticNext.ConnectedActivity.Coverage.Shed
