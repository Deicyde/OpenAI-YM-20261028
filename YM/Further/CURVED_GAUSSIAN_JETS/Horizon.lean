import YM.Further.CURVED_GAUSSIAN_JETS.Curvature
import YM.Progress.STATIONARY_SCENES.SliceGap
import YM.SectorNext.VACUUM_NORMALIZATION.Scheme



/-!
# Real period interpretation for the retained Ψ, K, and all cuts by Forest

First without a size estimate; positivity/both estimates in Gap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Flat
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Wilson Tree RG Precision
open Progress.StationaryScenes Bid Exterior FlatTree Bloch
open Green (link)
open Fiber
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {G : Gauge} {c f n : Side} (S : StepData c f) (F : Forest S.ratio)
abbrev OneForm (n : Side) := Body 1 n

def rail : Matrix (OneForm f) F.Free ℝ := (1:Table (OneForm f)).submatrix id (link F)
lemma rail_at (v : Vec F.Free) (i : Edge (Site f)) : (rail S F *ᵥ v) (wheel f i) = blank F v i := by
  unfold blank rail Matrix.mulVec dotProduct
  split <;> rename_i h
  · refine Finset.sum_eq_zero fun j _ => ?_
    have he : wheel f i ≠ link F j := fun hh => j.property ((wheel f).injective (a₂:=j.val) hh ▸ h)
    simp only [Matrix.submatrix_apply,id_eq,Matrix.one_apply, if_neg he,zero_mul]
  have he (j : F.Free) : wheel f i = link F j ↔ (⟨i,h⟩:F.Free)=j := (link F).injective.eq_iff (a:=(⟨i,h⟩:F.Free)) (b:=j)
  simp only [Matrix.submatrix_apply,id_eq, Matrix.one_apply,he]; simp



variable (H H' : Bed) (b : Towers S.patch.L)

def response := (extracted S F (installed S.ratio b.A0)).submatrix (link F) id
lemma whole_response : rail S F * response S F b=extracted S F (installed S.ratio b.A0) := by
  let W := installed S.ratio b.A0
  apply ext_of_mulVec_single; intro i
  rw [← mulVec_mulVec]
  funext j; obtain ⟨j,rfl⟩ := (wheel f).surjective j
  rw [rail_at,blank]; split
  · exact (stays F W _ _ ‹_›).symm
  rfl

def history := Fiber.principal (d 1 f*rail S F) (H.metric.acts f) (probe S*rail S F) S.kernel.penalty


lemma kinetic (t : Towers.Diagonal S H H' b) :
    let u := rail S F
    Bare (d 1 f * u) (d 1 c) (H.metric.acts f) (H'.metric.acts c) (probe S*u) S.kernel.penalty (response S F b) := by
  intro u
  obtain ⟨hQ,hK⟩ := stationed F _ _ _ t.trial
  have he := whole_response S F b
  constructor
  · calc
      _ = u.transpose*(K (H.metric.acts f) * extracted S F (installed S.ratio b.A0)) := by
        unfold K strength; rw [← he]; simp only [Matrix.transpose_mul,Matrix.mul_assoc,u]
      _ = _ := by rw [hK, transpose_mul, Matrix.mul_assoc]; rfl
  rw [Matrix.mul_assoc, he,hQ]; rfl

/-- Q and curvature-noise cross at actual conditional Hessian.
No Θ/strip operations here. -/
theorem transfer (t : Towers.Diagonal S H H' b) (hd : (history S F H).PosDef) :
    (history S F H)⁻¹*(S.kernel.penalty • (probe S*rail S F).transpose) = response S F b ∧
      Schur.schur (history S F H) (S.kernel.penalty • (probe S*rail S F).transpose) (S.kernel.penalty • 1) = K (H'.metric.acts c) := by
  have hb := kinetic S F H H' b t
  have hx := hb.marginal S.kernel.penalty_pos.ne' hd 0
  exact ⟨hb.home S.kernel.penalty_pos.ne' hd, by simpa only [history,zero_add] using! hx⟩










end YM.Further.CurvedGaussianJets.Flat
