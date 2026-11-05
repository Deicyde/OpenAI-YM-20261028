import Mathlib.RingTheory.Nilpotent.Exp
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Curving
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Cylinder
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Probe
import YM.Push.PRICE_COMPILER.Authors
import YM.SectorNext.RECONNECTED_LOCALITY.Gaussian
import YM.UVNext.PRICED_KERNELS.Echo

/-!
# The tested physical stencil for central curvature reads

* Keep *every* site in X (including those required for walks), and test every
  plaquette with an incident site there. Do not shrink actual masks. W logs
  include even the halo bonds needed for these tests. Not claiming the full
  held-data supports of any sector factor are given by these sets!
* Actual Gaussian read coordinates finite subset from that W (select on links,
  then with every color). Same e then l as WeightedAt. Variable cardinality
  to allow reads all throughout this clearing. Not a high-arity charge: still
  no claim about products of density letters with quadratic growth, nor a
  comparison on coordinates e.g. across many separate boxes of a torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Rows Tree Push.SectorMeasure
open Extra.Iteration Extra.Iteration.Scales YM.AnalyticBridge.LocalGaussianLaws Remote Local
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}

/-- Occasion index. Same based transported slot may be requested many times. -/
structure Occasion (G : Gauge) (n : Side) where
  location : Site n
  link : Slot
  color : G.ColorIndex

namespace Occasion
variable (v : Occasion G f)
def face := Work.F03.slotFace v.link v.location
def coordFace : Body 2 f := (v.face.1,plaquette v.face.2)
def bead : FreeResolvent.Slot G f 2 := FreeResolvent.ix v.coordFace v.color

def place : Support f := v.link.stencil.image (fun i => wrap f i + v.location)
lemma path_mem {u : Cover} (h : u∈Lattice.visits 0 v.link.walk) :
    wrap f u + v.location ∈ v.place := mem_image_of_mem _ (mem_union_left _ (List.mem_toFinset.mpr h))
lemma face_mem : v.face.1 ∈ v.place := mem_image_of_mem _
  (mem_union_right _ (List.mem_toFinset.mpr (show v.link.offset ∈
    Lattice.visits v.link.offset (Lattice.square v.link.plaq.val.1 v.link.plaq.val.2) from List.mem_cons_self)))
end Occasion

/-- All four physical positive bonds of any tested plaquette. The
third and fourth entries are stored positively even for slots which need
their inverses in faceValue. Duplicates in this set don't affect the read
set; don't use this to shorten the *evaluations*. -/
def bones (p : Cell f) : Finset (Bond f) :=
    {(p.1,p.2.val.1),(p.1+step p.2.val.1,p.2.val.2),(p.1+step p.2.val.2,p.2.val.1),(p.1,p.2.val.2)}
lemma first_bone (p : Cell f) : (p.1,p.2.val.1)∈bones p := by simp [bones]
lemma second_bone (p : Cell f) : (p.1+step p.2.val.1,p.2.val.2)∈bones p := by simp [bones]
lemma third_bone (p : Cell f) : (p.1+step p.2.val.2,p.2.val.1)∈bones p := by simp [bones]
lemma last_bone (p : Cell f) : (p.1,p.2.val.2)∈bones p := by simp [bones]

/-- Include path/slot reads on X; for the Healthy/mask reads
include the FULL physical plaquette neighborhood as well. -/
structure Covers (X : Support f) (W : Finset (Bond f)) : Prop where
  inPlace : ∀ e : Bond f, e.1∈X → e∈W
  flags : ∀ p : Cell f, (∃ x∈X, x∈touched p) → bones p ⊆ W

/-- In particular covers a path step from these starts. -/
lemma Covers.from_start {X : Support f} {W : Finset (Bond f)} (h : Covers X W) : ∀ v : Occasion G f,
    v.place ⊆ X → ∀ e : Edge Cover, e.1 ∈ Lattice.visits 0 v.link.walk →
      (wrap f e.1+v.location,e.2) ∈ W := fun v hv _ he => h.inPlace _ (hv (v.path_mem he))







/-- Use only W at this price. -/
def Reachable (S : StepData c f) (o : Site c) (x : ℝ) (W : Finset (Bond f)) :=
  ∀ i∈W, separation o (S.ratio.parent i.1) ≤ radiusB x / 4







variable {F : Forest S.ratio} {x β : ℝ} {A : Stores S}

abbrev Window (A : Stores S) (F : Forest S.ratio) (x : ℝ) (W : Finset (Bond f)) :=
  {i : Active A x F // i.val.val ∈ W}
abbrev SlotsW (A : Stores S) (F : Forest S.ratio) (x : ℝ) (W : Finset (Bond f)) (G : Gauge) :=
  Window A F x W × G.ColorIndex

def accessing (A : Stores S) (F : Forest S.ratio) (x : ℝ) (W : Finset (Bond f)) (G : Gauge) :
    SlotsW A F x W G ↪ In x A F (G:=G) :=
  ⟨fun i => (i.1.val,i.2),fun _ _ h => Prod.ext (Subtype.ext (congr_arg Prod.fst h)) (congr_arg (fun i : In x A F (G:=G) => i.2) h)⟩

def loading (A : Stores S) (F : Forest S.ratio) (x : ℝ) (W : Finset (Bond f)) (G : Gauge) :=
  (accessing A F x W G).trans (loadLink A F x)

lemma may_access (A : Stores S) (F : Forest S.ratio) {x : ℝ} {o : Site c} {W : Finset (Bond f)}
    (h : Reachable S o x W) (G : Gauge) :
    lives _ F A o (radiusB x / 4) (accessing A F x W G) := fun i => h _ i.1.2

/-- Uniform (P.L fixed) ceiling on the number of color-coordinate reads.
Chosen independent of period, use even for varying local support sizes. -/
def ceiling (G : Gauge) (P : Patch) (x : ℝ) :=
    Fintype.card (Site P.L) * (((2*radiusB x+1)^4) * Fintype.card Axis) * Fintype.card G.ColorIndex
lemma ceiling_pays (P : Patch) (A : Stores S) (F : Forest S.ratio) {x : ℝ} {o : Site c} {W : Finset (Bond f)}
    (hP : S.patch=P) (h : Reachable S o x W) (G : Gauge) :
    Fintype.card (SlotsW A F x W G) ≤ ceiling G P x := by
  have ht := reach o _ (may_access A F h G)
  apply Nat.cast_le (α:=ℝ) |>.mp (ht.trans ?_)
  unfold slotCount LocalJet.chips LocalJet.grain ceiling
  subst P; rw [two_mul]; simp only [Nat.cast_mul]; gcongr <;> omega


section profiles
/-- In fluctuation units, including all tape coordinates, don't average over angles. -/
def Guards (W : Finset (Bond f)) (Z : Gaussian.Vec (In x A F (G:=G))) (r : ℝ) :=
    ∀ i : Window A F x W, ‖tape Z i.val‖ ≤ r

/-- On the joint cloud; no tacit independence, no assertion about reads of
an interacting factor. Scale parameter `r`: support in this bound, plateau
at r/2. (Nonzero support suffices.) -/
structure GuardPrice (W : Finset (Bond f)) (Γ : Gaussian.Vec (In x A F (G:=G)) → ℝ) (r : ℝ) : Prop where
  borel : Measurable Γ
  probability (z) : Γ z ∈ Set.Icc 0 1
  support (z) : Γ z ≠ 0 → Guards W z r
  plateau (z) : Guards W z (r/2) → Γ z=1



/-- Literal smooth product guard on W. Not a broad link chart on the
physical variables--the input of *this* guard is Z. -/
def veil (W : Finset (Bond f)) (q : Chi) (r : ℝ) (Z : Gaussian.Vec (In x A F (G:=G))) :=
    ∏ i : Window A F x W, broad q (r/2) (tape Z i.val)

lemma veil_smooth (W : Finset (Bond f)) (q : Chi) (r : ℝ) : ContDiff ℝ ∞ (veil (A:=A) (F:=F) (G:=G) (x:=x) W q r) := by
  apply contDiff_prod (f:= fun (i : Window A F x W) (z : Gaussian.Vec (In x A F (G:=G))) => broad q (r/2) (tape z i.val))
  intro i hi
  exact (broad_smooth _ _).comp ((contDiff_apply _ _ i.val).comp ((gaugeCount (ι:=Active A x F) (G:=G)).contDiff))
lemma paid_veil (W : Finset (Bond f)) (q : Chi) (r : ℝ) (hr : 0<r) :
    GuardPrice W (veil (A:=A) (F:=F) (x:=x) (G:=G) W q r) r := by
  refine ⟨(veil_smooth W q r).continuous.measurable,fun z =>
    ⟨prod_nonneg fun i _ => (broad_range q (tape z i.val) (r/2)).1,?_⟩,?_,?_⟩
  · unfold veil
    apply prod_le_one
    exact fun _ _ => (broad_range ..).1
    exact fun _ _ => (broad_range ..).2
  · intro z hz i
    have hx := broad_span q (d:=r/2) (by positivity) (tape z i.val)
      (fun h => hz (prod_eq_zero (mem_univ i) h))
    linarith only [hx]
  intro z hz
  exact prod_eq_one fun i _ => broad_one q (by positivity) (hz i)
end profiles
end YM.PhysicalNext.PhysicalGuard7f546.Curved
