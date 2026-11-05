import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Stencil
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Weights

/-!
# Check covariance on a concrete local implementation

An optional producer of the W **symmetry** facts using actual stencil
operations as . Encode by linear combinations of real component
samples; include the chosen real coefficient (normalization of D in
) in the combination, as well as the color contraction; the later
real section and nonzero-initial tests will require actually using coefficients
that fit. Slot t powers are NOT part of the term/combination: `Packet.X`
inserts at use. Prove `PhysicalAction` for these W stencils given they are
combined by the literal signed axis rules.

This symmetry proof doesn't choose the coefficients. Doesn't assert arbitrary
combinations give faithful/gauge-invariant operators or have correct leading
value or rank! Use with E.g.  upstream choices (real WEideal
splitting, including color invariance and normalization, expanded out as
linear combinations; can pad lists/separate summands for literal axis
transforms). No assertion any of the spectral receipts is supplied by these
premises. All transfers/reads still need to use the *very same* W through
the Campaign gate above.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance.Stencil
open Function Filter Labels Lattice Wilson RG Source Analysis Push.CutoffProjectors Packet
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}

/-- One curl sample. No antisymmetric extension convention needed. -/
structure Sample (G : Gauge) where
  i : Axis
  j : Axis
  l : List Axis
  w : Walk
  component : G.ColorIndex

def Sample.value (D : Sample G) (U : Config G n) (x : Site n) : ℝ :=
  landed U (clover D.i D.j U) D.l D.w x D.component

def Sample.onAxis (s : Signed) (D : Sample G) : Sample G :=
  ⟨s.perm D.i,s.perm D.j,D.l.map s.perm, D.w.map (·.rotate s), D.component⟩

def Sample.polarity (s : Signed) (D : Sample G) := (sign s D.j * sign s D.i) * stackSign s D.l





def material (l : List (Sample G)) (U : Config G n) (x : Site n) := (l.map (fun i => i.value U x)).prod

def phaseProduct (s : Signed) (l : List (Sample G)) := (l.map (fun i => i.polarity s)).prod





/-- Pair against **one** gradient leg. Expand the functional over the
components. No real/complex conjugations inside the basis sum. -/
structure Blend (G : Gauge) where
  i : Axis
  l : List Axis
  w : Walk
  component : G.ColorIndex
  clovers : List (Sample G)

namespace Blend
variable (D : Blend G)

def readCurrent (U : Config G n) (x : Site n) (A : Directions G n) : ℝ :=
  landed U (current D.i U A) D.l D.w x D.component * material D.clovers U x

def onAxis (s : Signed) : Blend G :=
  ⟨s.perm D.i,D.l.map s.perm,D.w.map (·.rotate s),D.component,D.clovers.map (Sample.onAxis s)⟩

def winding (s : Signed) : ℝ := sign s D.i * stackSign s D.l * phaseProduct s D.clovers




end Blend

section Differentiating

private lemma linStack (U : Config G n) (i : Axis) (x : Site n) (l : List Axis) :
    IsLinearMap ℝ fun A : Directions G n => stack U (current i U A) l x := by
  have hl (x : Site n) (a : Step) : IsLinearMap ℝ (fun A : Directions G n => sensor U A x a) := by
    unfold sensor; split
    · constructor
      · intro h g; simp; abel
      intro h g; simp
    constructor <;> intros <;> rfl
  induction l generalizing x with
  | nil =>
    change IsLinearMap ℝ fun A => aperture G i _
    constructor
    · intro v w; unfold aperture; rw [(hl x _).1,(hl x _).1]; simp only [smul_add,smul_sub]; abel
    intro v w; unfold aperture; rw [(hl x _).2,(hl x _).2,← smul_sub,smul_comm v]
  | cons i l ih =>
    simp only [stack,centered,aperture]
    constructor
    · intro v w; rw [(ih _).1,(ih _).1]; simp only [map_add,smul_sub,smul_add]; abel
    intro v w; rw [(ih _).2,(ih _).2,map_smul,map_smul,← smul_sub,smul_comm v]

lemma reading (D : Blend G) (U : Config G n) (x : Site n) : IsLinearMap ℝ (D.readCurrent U x) := by
  let k := material D.clovers U x
  unfold Blend.readCurrent landed
  constructor
  · intro v w; rw [(linStack U D.i _ D.l).1, map_add]; simp [add_mul]
  intro v w; rw [(linStack U D.i _ D.l).2, map_smul]; exact mul_assoc .. -- smul_eq_mul


















end Differentiating
section Bonds

variable {d : ℕ} {F : Frame G d} {ι : Type*} [Fintype ι]
variable (L : ι → Blend G) (q : ι → SourceSpace F →ₗ[ℂ] ℂ)

/-- At o evaluate X, using the specified cutoff stencil family and the actual
matrix group and Ad links. In  notation, against real gradient input A
this tests finite sums of `⟨C(U), D(U) A⟩` by linearity and the real
orthonormal basis. No extra scale factors beyond those in the chosen
coefficients q. -/
def forms (o : Site n) : SeedWeights F n where
  toFun v U e j := ∑ i, q i v * ((L i).readCurrent U o (Packet.forward e j) : ℝ)
  map_add' v w := by funext U e j; simp [add_mul,Finset.sum_add_distrib]
  map_smul' a v := by funext U e j; simp [mul_assoc,← Finset.mul_sum]



/-- Real, signed choice after combining the actual stencil operations. -/
structure Combines : Prop where
  brushes (s : Signed) : ∃ e : Equiv.Perm ι,
    (∀ i, L (e i) = (L i).onAxis s) ∧
    ∀ i v, q (e i) (sw F s v) = (((L i).winding s:ℝ):ℂ) * q i v
  real (i : ι) (v : SourceSpace F) : q i (cw _ v) = star (q i v)


















end Bonds
end YM.ProjectorNext.Equivariance.Stencil
