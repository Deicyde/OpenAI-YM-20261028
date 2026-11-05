import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Divergence
import YM.Push.CUTOFF_PROJECTORS.Signed

/-!
# Covariant choices on the weight side

What operation on the *actual link vector field* suffices? Provide an
exact local covariance gate. One concrete way to pass it, as in : a
whole signed-group average (and real-form average if necessary) on the
stencils/operators. The transforms in the average act on BOTH the link
vector field, with its real color directions, and the input basis/parameters
(in the opposite sense). Give a production of covariant weights by such an
operation. It has no `Family` or convergence premises. Issues like gauge
stencil estimates, attaining the wanted triangular normalization, and
choosing transfer data on these weights still need work. In particular we
do *not* arbitrarily average a packet **after** charging any other bills.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Labels Lattice Wilson RG Push.CutoffProjectors Packet
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}











/-- Move the WHOLE vector field to the target independently stored links. -/
def carries (s : Signed) (b : Site n) : (Vectors G n) →ₗ[ℂ] (Vectors G n) where
  toFun W U e j :=
    let q := (bonds s b).symm e
    weighs W (pull s b U) q (roll s b U q (cbasis G j))
  map_add' W V := by funext U e j; simp [weighs,mul_add,Finset.sum_add_distrib]
  map_smul' c W := by funext U e j; simp [weighs,← Finset.mul_sum,mul_left_comm]











section Parameters
variable {d : ℕ} (F : Frame G d)

/-- The input of `Packet.X` actually lives in this submodule. -/
abbrev SourceSpace := equationSpace F

def sw (s : Signed) : SourceSpace F →ₗ[ℂ] SourceSpace F :=
  ((turn F s).comp (SourceSpace F).subtype).codRestrict _ fun v => equation_oriented F s v v.2

def cw (v : SourceSpace F) : SourceSpace F := ⟨star v.val,equation_realForm F v v.2⟩

lemma sw_mul (s t : Signed) (x : SourceSpace F) : sw F (s*t) x = sw F s (sw F t x) := Subtype.ext (turn_mul F s t x)
lemma sw_one (x : SourceSpace F) : sw F 1 x = x := Subtype.ext (turn_one F x)


lemma cw_add (x y : SourceSpace F) : cw F (x+y) = cw F x + cw F y := Subtype.ext (star_add ..)
lemma cw_smul (t : ℂ) (x : SourceSpace F) : cw F (t • x) = star t • cw F x := Subtype.ext (star_smul ..)

lemma scaled_turn (s : Signed) (t : ℝ) (x : SourceSpace F) :
    scaledEquations F t (sw F s x) = sw F s (scaledEquations F t x) := Subtype.ext (F.scaling ..)

lemma scaled_bar (t : ℝ) (x : F.Coeff) : F.scaled t (star x) = star (F.scaled t x) := by ext1; simp [mul_comm]

lemma scaled_cw (t : ℝ) (x : SourceSpace F) : scaledEquations F t (cw F x) = cw F (scaledEquations F t x) :=
  Subtype.ext (scaled_bar F t x)

abbrev SeedWeights (n : Side) := SourceSpace F →ₗ[ℂ] Vectors G n

variable {F}
structure PhysicalAction (W : SeedWeights F n) : Prop where
  signed (s : Signed) (v : SourceSpace F) : Reorients s 0 (W v) (W (sw F s v))
  real (v : SourceSpace F) : W (cw F v) = star (W v)
  varies (v : SourceSpace F) (e j) : Slopes fun U => W v U e j

def conjugated (W : SeedWeights F n) : SeedWeights F n where
  toFun v := star (W (cw F v))
  map_add' v w := by rw [cw_add,map_add,star_add]
  map_smul' t v := by rw [cw_smul,map_smul,star_smul,star_star]; rfl












end Parameters
end YM.ProjectorNext.Equivariance
