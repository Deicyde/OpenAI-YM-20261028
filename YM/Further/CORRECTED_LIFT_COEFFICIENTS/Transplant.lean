import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Orbit
/-!
# Compatibility of exact k charts with the basis

One sufficient layout. Require these exact history/covariance movements if
claiming the resulting test moves. Do not conditionally adopt a NEW sym scan
for Offers on another layout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.Compass
open Filter Function Set Lattice Wilson RG Source Source.Drops Labels Cells Extraction
open Push.Corrected Push.Corrected.Issue Push.CutoffProjectors Next.Foundations
open ProjectorNext.Equivariance
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {C : Family G} {m p d N t : ℕ} (B : Screen C m p t) (s : Signed)

structure Tribe (C : Family G) (d m N p : ℕ) : Prop where
  sense (s : Signed) (v : C.label d) : Issue.primary C (turn _ s v) m N p=turn (C.labels.level d) s (Issue.primary C v m N p)
  -- one sufficient version for short history pulls
  arrays (s : Signed) : ∃ g : Equiv.Perm ℕ, (∀ i, paper C d m N p (g i)=(paper C d m N p i).image (affine s 0)) ∧
      ∀ i, short C d m N p i → ∀ v : C.label d, annal C (turn _ s v) m N p (g i)=annal C v m N p i ∘ pull s 0



variable (hP : vacancy B s)

omit hP in
private lemma spun (i : ℕ) (g : Equiv.Perm ℕ) (hx : ∀ i, paper C d m N p (g i)=(paper C d m N p i).image (affine s 0)) :
    short C d m N p (g i) ↔ short C d m N p i := by unfold short; simp_rw [hx,moves_cost]





def shine {G : Gauge} {n : Side} (s : Signed) (i : Dial G n) : Dial G n := (Face.send s 0 i.1,i.2)

def CopperMotion {G : Gauge} {n : Side} (Q : Copper G n) (s : Signed) := ∀ i j,
    wind s i.1.2 * wind s j.1.2 * Q.P (shine s i) (shine s j) = Q.P i j



def turning (s : Signed) (d : ℕ) (G : Gauge) : Snap G d →L[ℝ] Snap G d :=
    LinearMap.toContinuousLinearMap (LinearMap.pi fun i => (Taylor.turn s.ortho⁻¹).comp (LinearMap.proj i))







end YM.Further.CorrectedLift.Compass
