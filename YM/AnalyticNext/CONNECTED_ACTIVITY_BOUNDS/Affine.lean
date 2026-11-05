import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Charts2
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Windows
import YM.Push.SECTOR_MEASURE.Oriented


/-!
# The operated cut rows; an actual affine subtraction

Use ONE stack with all channels and the very same κ and
prediction. Slight variant of E auxiliary Gaussian for our expense
certificate. The affine constants use the true rooted branches of the
step (incl actual choice sharing); the affine operator uses **flat cut
row formula transported to V by the indicated paths**. Applied in the
appropriate *actual* link orientations using `barV`. A valid alternative
to differentiating in analytic neighborhoods about `barV`. Doesn't assert
its equality to that latter prescription at V; keep the exact difference
from the energetic rows. All subsequent estimates take this D. Not a
change to the theorem or to `Move`, `critical`, or kinetic calibration.

All projected anchors on physical positions with signs retained; not an
independent spelling of the same base in each halo. Choose all F,I rows
outside a slightly smaller (~8B) halo for subtraction, not testing exact
potential stencil incidence. This harmlessly includes rows of constant
affine subtraction when there are no active coefficients; contributes with
both signs (retain the constant). Need to earn comparison and gap OUTSIDE
this halo. C,D,N,L kept as costs unchanged. Precision identity completion on
all inactive coordinates (tree included). Frozen inputs to the shell affine
form use the SAME actual frozen Y, but use a bounded smooth extension of the
relative-log chart, not assume they'll stay small after dropping masks.
Haar scale of that chart and the pull identity checked separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Matrix Lattice RG Wilson Pressure Pressure.Stores Precision Tree Exterior
open Turn Push.SectorMeasure Push.SectorMeasure.Oriented
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

-- Coordinates and truth are always on positive links, no transpose
-- convention implicit.
abbrev Vars (G : Gauge) (f : Side) := Bond f × G.ColorIndex
abbrev ArrayR (G : Gauge) (f : Side) := Vars G f → ℝ

def lie (x : ArrayR G n) : Directions G n := fun i => WithLp.toLp 2 (fun j => x (i,j))

def real (x : Directions G n) : ArrayR G n := fun i => (x i.1) i.2


lemma lie_real (x : Directions G n) : lie (real x) = x := rfl

def form (x : Directions G n) : fieldDir G n 1 := fun b => x (b.1,axisEquiv.symm b.2)

lemma collect_form (x : Directions G n) : collect G (form x) = x := by
  funext b
  unfold collect form; dsimp only; rw [show coord _ = axisEquiv _ from rfl, Equiv.symm_apply_apply]

/-- Minimum distance over projected endpoints. -/
def points (S : StepData c f) (i : Bond f) := (pinPos i).image S.ratio.parent

def activeB (A : Stores S) (F : Forest S.ratio) (B : ℕ) : Finset (Bond f) :=
  Finset.univ.filter (fun i => i∉ F.trunks ∧ Disjoint (points S i) (A.dome (10*B)))



-- weight sqrt by all Signed, including both-parts F
abbrev Pos (_S : StepData c f) := Signed × (Twin f ⊕ Bond c)
abbrev Ix (G : Gauge) (S : StepData c f) := Pos S × G.ColorIndex

def weight := (Fintype.card Signed:ℝ)⁻¹

lemma weight_pos : 0<weight := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

def center (S : StepData c f) : (Twin f ⊕ Bond c) → Site c :=
  Sum.elim (fun i => S.ratio.parent i.1.1) Prod.fst

def choosing (A : Stores S) (B : ℕ) : Finset (Pos S) := Finset.univ.filter
  (fun i => i.1.act (center S i.2) ∉ A.dome (8*B))

/-- Row-centered gauge using only actual V links. May restrict to called
stencils when using the definition. `V` here already in row orientation. -/
def corner (i y : Site n) := route 0 (lift (y-i)) 1

def aiming (V : Config G n) (x y : Site n) := travel V x (corner x y)

lemma finish (i y : Site n) : stop i (corner i y) = y := by
  unfold corner
  have h := Work.E03.stop_route i 0 (lift (y-i)); rw [map_zero, add_zero,wrap_lift] at h
  rw [h]; abel

/-- Gauge rotation (per site), distinct from Signed reidentification. -/
def rotateG (x : Directions G n) (u : Site n → G.El) : Directions G n :=
  fun e => G.adjoint (u e.1) (x e)

def untwine (S : StepData c f) (p : Pos S) (V : Config G c) (x : Directions G f) : Directions G f :=
    rotateG (maps p.1 (replica S.ratio V) x) (aiming (pull p.1 0 V) (center S p.2) ∘ S.ratio.parent)

/-- Actual square vectors. `v` (`Mv`, `Mw`) uses row R and true clipped
and clamped V even on instances with geometry holes. `choice` refers to
the transported SAME tag. -/
def target (T : Tube G S) (R : ℕ) (δ : ℝ) (i : Pos S) (k : S.Choices) (V : Config G c) (U : Config G f) : G.Color :=
    let X := pull i.1 0 V; let W := pull i.1 0 U
    i.2.elim (fun p => T.Xf R W p - T.Mv R δ X p)
      (fun b => Pressure.Tube.Z S (S.prediction W (choice i.1 k)) X b - T.Mw R δ X b)

/-- Flat linearization of `Xf` on F and I (no target v,V variation in
this derivative). `R` counts TRUE fine walk length including the final
plaquette. Faces and root Q are in their row-specific orientation. Use
on funded paths for the actual amplitudes. -/
def level (T : Tube G S) (R : ℕ) (i : Twin f) (x : Directions G f) : G.Color :=
    if i.2 then ∑' l : ℕ,
      (let v := T.up.row i.1.2 l
       if v.2.length ≤ R then v.1 • Work.F03.faceCurl (Work.F03.slotFace v.2 i.1.1) (form x) else 0)
    else Real.sqrt T.high.direct • Work.F03.faceCurl i.1 (form x)

def derivative (T : Tube G S) (R : ℕ) (p : Pos S) (V : Config G c) (x : Directions G f) : G.Color :=
    let q := untwine S p V x
    p.2.elim (fun i => level T R i q) (fun i => Next.Fluctuations.zLin S (form q) 0 i)

/-- D already in weighted units, active columns; zero rows on other
anchors. Include potential stencils even where derivative happens to vanish. -/
def scale (T : Tube G S) (x : ℝ) (V : Config G c) : Matrix (Ix G S) (Vars G f) ℝ :=
    Matrix.of fun i j => Real.sqrt weight * (derivative T (till x) i.1 V (lie (Pi.single j 1))) i.2

def Dmat (T : Tube G S) (F : Forest S.ratio) (x : ℝ) (A : Stores S) (V : Config G c) :=
    Matrix.of fun (i : Ix G S) (j : Vars G f) =>
      if i.1∈choosing A (radiusB x) ∧ j.1∈activeB A F (radiusB x) then scale T x V i j else 0

-- Weights in chart support chosen after L, passed in. `r` for the
-- Lie ball here, not radiusB. Use actual `LocalH.snap`.
def hold (H : Chi) (r u : ℝ) (U : G.El) :=
    if U∈G.lieExp '' Metric.ball 0 r then
      let x := LocalH.snap G U
      H.innerShare u ‖x‖ • x
    else (0:G.Color)

def fixed (H : Chi) (F : Forest S.ratio) (r u : ℝ) (A : Stores S) (B : ℕ) (V : Config G c) (Y : F.Slice G) :=
    real (fun (j : Bond f) => if j∉ F.trunks ∧ j∉ activeB A F B then
      hold H r u (F.drape Y j * (replica S.ratio V j)⁻¹) else 0)

def zeroed (T : Tube G S) (A : Stores S) (x : ℝ) (q : S.Choices) (V : Config G c) (a : ArrayR G f) : Ix G S → ℝ :=
  fun i => if i.1∈choosing A (radiusB x) then
    Real.sqrt weight * target T (till x) (temp x) i.1 q V (replica S.ratio V) i.2 + (scale T x V *ᵥ a) i else 0

def gram (T : Tube G S) (F : Forest S.ratio) (x : ℝ) (A : Stores S) (V : Config G c) :=
    let D := Dmat T F x A V
    D.transpose * D + Matrix.diagonal (fun (j : Vars G f) => if j.1 ∉ activeB A F (radiusB x) then 1 else 0)

def window (S : StepData c f) (B : ℕ) (j : Bond f) : Finset (Bond f) :=
    Finset.univ.filter (fun i => ¬ Disjoint (points S i) (halo (B/4) (points S j)))

def eyes (S : StepData c f) (G : Gauge) (B : ℕ) : Win.Windows (Vars G f) where
  panel i := (window S B i.1) ×ˢ Finset.univ
  owns i := Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    let y := S.ratio.parent i.1.1
    have h : y ∈ points S i.1 := Finset.mem_image_of_mem _ (by simp [pinPos])
    intro he; exact Finset.disjoint_left.mp he h (halo_subset (B/4) (points S i.1) h) ⟩,
    Finset.mem_univ _⟩

/-- Produce U in active charts even after dropping guards, no logarithm
re-read on active links until protected; tree and frozen exact extension
arguments retained. -/
def install (A : Stores S) (F : Forest S.ratio) (B : ℕ) (V : Config G c) (Y : F.Slice G) (x : ArrayR G f) : Config G f :=
  F.drape (fun i => if i.val∈activeB A F B then G.lieExp (lie x i.val) * replica S.ratio V i.val else Y i)

lemma real_tree (A : Stores S) (F : Forest S.ratio) (B : ℕ) (V : Config G c) (Y : F.Slice G) (x : ArrayR G f) :
    SliceSet S F (install A F B V Y x) := fun i h => F.on_tree _ ⟨i,h⟩

-- unfolding checks

lemma plateau_zero (H : Chi) (F : Forest S.ratio) (r u : ℝ) (A : Stores S) (B : ℕ)
    (V : Config G c) (Y : F.Slice G) (j : Vars G f) (h : j.1∈ activeB A F B) : fixed H F r u A B V Y j=0 := by
  simp only [fixed,real,h,not_true_eq_false,and_false, if_false]; rfl

lemma path_length (x y : Site n) : (corner x y).length ≤ 4*separation x y := by
  unfold corner
  let l := lift (y-x)
  have ha : allAxes 1=[0,1,2,3] := by decide
  rw [separation_comm]; unfold separation; let h := pdist (y-x)
  change (route 0 l 1).length ≤ 4*h
  have hb i : (l i).natAbs ≤ h := component_le ..
  simp [route,ha,axisRoute,Lattice.straight]; have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3; omega

end YM.AnalyticNext.ConnectedActivity.Aff
