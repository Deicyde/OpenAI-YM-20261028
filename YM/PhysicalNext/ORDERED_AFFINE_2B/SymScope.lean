import YM.AnalyticBridge.SECTOR_AFFINE_JETS.LinkBasis
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymWhole
import YM.PhysicalNext.ORDERED_AFFINE_2B.Till


/-!
# Symmetric supports/hops prices for Thing *before* any reads

Discardable iff a long containing-distance pair, BEFORE asking even
censor or masks. Everything else even x/y metadata and unexamined
angles retain with both projected endpoints. charge the actual `shots`
by the symmetric potential stencil proved earlier. These rules commute
literally with H; rotation that makes initial-site allowances shift
can instead use these covers. No claim that supports for the multiplier
can be these, including at hard tests or plateau complements. . All within constants in output units with geometry delay.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Scope
open Function Filter Set Lattice RG Wilson Precision Tree Pressure Stores
open Next Next.SectorChange AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor Whole Matrix
open Further Further.CurvedGaussianJets Jets Tracks Completion SymRows SymWhole  
open AnalyticBridge AnalyticBridge.Covariance Terrain
open MeasureTheory SectorNext.Vacuum
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {d j m n : ℕ} {x : ℝ}

-- Not actual label material region. Specific complete supports
-- assigned to the scalar/determinant price requests (inc negative
-- eligibility decisions, no cutoff line or unselected scans erased).
def nearStart (S : StepData c f) (i : Bond f) := S.ratio.parent i.1

def both (S : StepData c f) (i : Bond f) (x : ℝ) := Finset.univ.filter fun z : Site c => ∃ y∈Next.SectorChange.points S i, separation y z ≤ 13*radiusB x



def Angle (S : StepData c f) (x : ℝ) (p : Run (Bond f) d) := ∀ i : Fin d,
    ∀ y∈Next.SectorChange.points S (p i.castSucc), ∀ z∈ Next.SectorChange.points S (p i.succ), separation y z ≤ 50*Whole.rail x

lemma both_spec (i : Bond f) (y : Site c) : y∈both S i x ↔ ∃ z∈Next.SectorChange.points S i, separation z y ≤ 13*radiusB x := by simp [both]

lemma near_mem (i : Bond f) : nearStart S i ∈ Next.SectorChange.points S i := Set.mem_insert ..
lemma both_halo (i : Bond f) {y : Site c} (h : separation (nearStart S i) y ≤ 13*radiusB x) : y∈both S i x := (both_spec ..).2 ⟨_,near_mem _,h⟩


section spin
open Locations Channels
variable (s : Signed) (b : Site c) (p : Run (Bond f) d)
abbrev back (s : Signed) (b : Site c) (S : StepData c f) := diagram s b S
lemma turns : Angle S x ((back s b S)∘p) ↔ Angle S x p := by
  unfold Angle; simp_rw [Function.comp_apply,show ∀ i : Bond f, back s b S i=sendEdge s (S.ratio.embed b) i from fun _=>rfl,
    moves_points,Set.forall_mem_image,affine,separation_translate,separation_signed]


end spin

variable {p : Run (Bond f) d}
lemma hired (h : Angle S x p) : Hops (nearStart S) (watch*rail x) p := by
  intro i; exact (h i _ (near_mem _) _ (near_mem _)).trans (by unfold watch; omega)







variable {A : Stores S} {F : Forest S.ratio} {k : S.Choices} {T : Tube G S} {V : Config G c}
  {σ : ℝ} {J : Tab} (h : J.Ships n m σ T F A k x V)
include h




end YM.PhysicalNext.OrderedAffine2B.Scope
