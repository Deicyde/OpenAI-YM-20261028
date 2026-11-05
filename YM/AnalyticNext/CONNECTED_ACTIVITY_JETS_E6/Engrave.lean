import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Impasto

/-!
# Slots, charge matrix jets

Uniform no cardinal factors; Gauge constants depend only true G. Leg along
scaled V. Allows later multiplying either adjoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Exterior Wilson
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {v u d e : ℝ} {k : ℕ}
open Brush

lemma scaleL {g : E→G.Mat} (p : Brush k u d g x) :
    Brush k ((royalty G)⁻¹*u) d (fun x=> G.projectColor (g x)) x := by
  let L := G.projectColor.toContinuousLinearMap
  apply p.report L
  have hx : 1≤royalty G := royalty_ge _
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x=> ?_
  rw [mul_comm,← div_eq_mul_inv]; exact G.project_norm _

-- `cutLog` analyticity requires own proofs later.
lemma sculpt {g : E→G.El} (p : Brush k (royalty G) d (G.mat ∘ g) x) :
    Brush k 1 d (fun i=> G.curvature (g i)) x := by
  have hf := p.separating (reverse p)
  have hh := scaleL (hf.smul (1/2:ℝ))
  apply hh.climb _ le_rfl
  have he := royalty_ge G; rw [Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; apply le_of_eq
  field_simp; ring

lemma decorate {g : E→G.El} {a : E→ G.Color} (p : Brush k u d (G.mat ∘ g) x) (q : Brush k v e a x) :
    Brush k (u*(v*u)) (d+e+d) (fun i=> G.adjoint (g i) (a i)) x := by
  have h := q.report G.colorMat.toContinuousLinearMap (v:=royalty G) (ContinuousLinearMap.opNorm_le_bound _
    (zero_le_one.trans (royalty_ge G)) fun i=> (G.colorMat_norm _).le)
  have he := p.paints h; have hv := scaleL (he.paints (reverse p))
  apply hv.climb ?_ le_rfl
  apply le_of_eq; have hi := royalty_ge G; field_simp

lemma slot_cost (s : Slot) {U : E → Config G c} (o : Site c) (hd : 0≤d) (hp : ∀ j,
    Brush k (royalty G) d (fun i => G.mat (U i j)) x) : Brush k (royalty G ^2) (2*s.length*(d*royalty G))
      (fun i=> s.atSite (U i) o) x := by
  let p := Work.F03.slotFace s o
  have ht : Brush k (royalty G) (4*(d*royalty G)) (fun i=> G.mat (faceValue (U i) p)) x := by
    convert! (tour (square p.2.val.1 p.2.val.2) p.1 hd hp) using 1
  simp_rw [Work.F03.atSite_path]; apply (decorate (g:=fun i=> travel (U i) o s.walk) (tour s.walk o hd hp)
    (sculpt (g:=fun i=> faceValue (U i) p) ht)).climb
  · rw [pow_two,one_mul]
  unfold Slot.length
  have hf : 0 ≤ d*royalty G := mul_nonneg hd (zero_le_one.trans (royalty_ge _)); push_cast; linarith
end YM.ConnectedActivityE6.Blaze
