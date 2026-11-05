import YM.Push.LOOP_COEFFICIENT.Block.Landmark

/-!
# Adjusted joints from maps on first Haar increments

Intermediate port: cost on linear-stationary fields about zero (but
actual base, one & two jets, masked neither in Z nor in the path sum).
No map-drift piece in this comparison. Only the adjusted operator needs
pre-choice bounds. The gap input here is a hypothesis on flat fibers, not
on any higher determinant derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Set Filter Lattice Laurent RG Wilson Precision Exterior Bloch Complex Block.Portal
open scoped Topology ContDiff BigOperators
variable {a b d J E F : Type} [Fintype a] [Fintype b] [Fintype d] [DecidableEq a] [DecidableEq b] [DecidableEq d] [Fintype J] [Fintype E] [Fintype F] [DecidableEq J] {n : Side}
open scoped Matrix.Norms.Frobenius in
omit [Fintype b] in
lemma Models.congr {A : Grid n J d} {B : Grid n E a} {C : Grid n F b} {f g V} (h : Models A B C f V) (he : g =ᶠ[𝓝 0] f) : Models A B C g V := ⟨h.smooth.congr_of_eventuallyEq he,by rw [actualMatrix,actual_congr cmat he]; exact h.sync⟩
namespace Block
variable {L c f : Side} {G : Gauge} {Y : Lights G L} {W : PathData G} {p : Clip} {S : StepData c f} {r : Ratio c f}

structure Pier (G : Gauge) (L : Side) where
  bearer : Vertex (Axes G) (Axes G) (JointType G L)
  stress : Vertex (Axes G) (Axes G) (Axes G)
  offset : Vertex (Axes G) (ScalarBlock G L) (JointType G L)

namespace Pier
variable (P : Pier G L) (Y) (W p)
def mask := ((worm Y).pow depth).mul P.offset
def field := (torch Y).add (P.mask Y)
def bow := (P.bearer.transpose.mul P.stress).mul P.bearer
def fabric : JointVertex G L := ((mounted (slab Y W p)).add P.bow).add ((P.field Y).transpose.mul (P.field Y))

open scoped Matrix.Norms.Frobenius
variable {T : Lights G r.count} {K : Pier G r.count}
structure Serves (P : Pier G r.count) (t : S.Choices) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (χ : Shear G c f) : Prop where
  left : ∀ᶠ z in 𝓝 0, projectFine G c f * χ z = projectFine G c f
  hχ : Sheared χ
  bonds : Models (linksGrid G c) (linksGrid G c) (jointGrid G r) (fun z => Loops.rate (Zmap t) (background G S A z) * χ z) P.bearer
  loads : Models (linksGrid G c) (linksGrid G c) (linksGrid G c) (fun z => cost (penalty S (vary 1 z)) (Zmap t (background G S A z))) P.stress
  nodes : Models (linksGrid G c) (coarseNodes G r) (jointGrid G r) (fun z => (mu S)^2 • (X₀ t (background G S A z) * χ z)) P.offset

lemma Serves.adjusted {t χ A σ C Λ} (hs : Serves K t A χ (S:=S)) (ht : Projects r (linksGrid G f) (linksGrid G c) (cmat (liftMatrix G A)) T) (hw : W.Bounds p σ C Λ) : Models (linksGrid G c) (jointGrid G r) (jointGrid G r) (onAdjusted p W t A χ) (K.fabric T W p) := by
  have hf : Models (linksGrid G c) (coarseNodes G r) (jointGrid G r) (fun z => completion t (background G S A z) * χ z) (K.field T) := by
    refine (((mill_models ht).mul (front_models G r)).add (((worm_models ht).pow _).mul hs.nodes)).congr (hs.left.mono fun z hz => ?_)
    dsimp only; rw [completion,positions_background,Matrix.add_mul,Matrix.mul_assoc _ (projectFine G c f),hz,Matrix.smul_mul,Matrix.mul_assoc (_^depth),Matrix.mul_smul,ratio_mu S r]
  have he z (hz : projectFine G c f * χ z = projectFine G c f) : (χ z).transpose * cost (mainTerm p W ∘ positions) (background G S A z) * χ z =
      (projectFine G c f).transpose * cost (mainTerm p W) (vary 1 (liftMatrix G A *ᵥ z)) * projectFine G c f := by rw [cost_input hw,positions_background,← Matrix.mul_assoc,← Matrix.mul_assoc,← transpose_mul,hz,Matrix.mul_assoc _ (projectFine G c f),hz]
  refine (((((front_models G r).transpose.mul (slab_models ht hw)).mul (front_models G r)).add ((hs.bonds.transpose.mul hs.loads).mul hs.bonds)).add (hf.transpose.mul hf)).congr (hs.left.mono fun z hz => ?_)
  rw [onAdjusted,onBase,baseVector,Matrix.mul_add,Matrix.mul_add,Matrix.add_mul,Matrix.add_mul,he z hz]; simp only [transpose_mul, Matrix.mul_assoc]
end Pier
end YM.Push.Loops.Block
