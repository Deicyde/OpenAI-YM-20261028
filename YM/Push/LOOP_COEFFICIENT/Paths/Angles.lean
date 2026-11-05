import YM.Push.LOOP_COEFFICIENT.Grids
import YM.Push.LOOP_COEFFICIENT.Paths.Hessian
import YM.Push.LOOP_COEFFICIENT.Paths.Palette

/-!
# Two successive link angles and left Hessian input banks
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Matrix Set Function Filter Metric Lattice Laurent RG Wilson Bloch Work.F02
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

/-- `true` = background, `false` = left increment. -/
abbrev Angles (G : Gauge) := Bool × Axes G

def angle (b : Bool) (i : Axis) : CSpace (Angles G) →L[ℂ] CColor G := ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (b,i,j)

def letterAngle (b : Bool) (i : Axis) (z : CSpace (Angles G)) : G.Mat := if b then
  NormedSpace.exp (-complexLie G (angle true i z)) * NormedSpace.exp (-complexLie G (angle false i z))
  else NormedSpace.exp (complexLie G (angle false i z)) * NormedSpace.exp (complexLie G (angle true i z))

lemma exp_diff : ContDiff ℂ ω (NormedSpace.exp : G.Mat → G.Mat) := contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic x).contDiffAt
lemma letter_diff (b : Bool) (i : Axis) : ContDiff ℂ ω (letterAngle (G:=G) b i) := by
  unfold letterAngle; have he (b) : ContDiff ℂ ω ((complexLie G) ∘ angle b i) := (complexLie G).contDiff.comp (angle (G:=G) b i).contDiff
  cases b
  · exact (exp_diff.comp (he false)).mul (exp_diff.comp (he true))
  exact (exp_diff.comp (he true).neg).mul (exp_diff.comp (he false).neg)
@[simp] lemma letter_zero (b : Bool) (i : Axis) : letterAngle (G:=G) b i 0 = 1 := by simp [letterAngle]
lemma letter_bounds (G : Gauge) {σ : ℝ} (h : 0<σ) : ∃ ρ : ℝ, 0<ρ ∧ ∀ b i (z : CSpace (Angles G)), ‖z‖≤ρ → ‖letterAngle b i z - 1‖ ≤ radius σ := by
  have he : ∀ᶠ z : CSpace (Angles G) in 𝓝 0, ∀ b i, ‖letterAngle b i z - 1‖ ≤ radius σ := eventually_all.mpr fun b => eventually_all.mpr fun i =>
    (show Tendsto (letterAngle b i) (𝓝 (0:CSpace (Angles G))) (𝓝 1) by simpa using! (letter_diff (G:=G) b i).continuous.tendsto 0).eventually (show closedBall 1 (radius σ) ∈ 𝓝 (1:G.Mat) from closedBall_mem_nhds _ (radius_pos h)) |>.mono (fun z hz => by simpa [dist_eq_norm] using hz)
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ/2, half_pos hδ,fun b i z hz => hb (by simpa using hz.trans_lt (half_lt_self hδ)) b i⟩

lemma letter_cancel (b : Bool) (i : Axis) (z : CSpace (Angles G)) : letterAngle b i z * letterAngle (!b) i z = 1 := by
  letI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℂ _
  have hp (z : G.Mat) : NormedSpace.exp z * NormedSpace.exp (-z) = 1 := by erw [← NormedSpace.exp_add_of_commute (Commute.refl z |>.neg_right),add_neg_cancel,NormedSpace.exp_zero]
  have he (x y : G.Mat) : NormedSpace.exp x * NormedSpace.exp y * (NormedSpace.exp (-y) * NormedSpace.exp (-x)) = 1 := by rw [mul_assoc _ (NormedSpace.exp y),← mul_assoc (NormedSpace.exp y), hp,one_mul,hp]
  unfold letterAngle; cases b
  · exact he _ _
  simpa only [neg_neg] using! he (-complexLie G (angle true i z)) (-complexLie G (angle false i z))

def portion (z : Co n (Angles G) → ℝ) (b : Bool) : Loops.Links G n := fun i => z (i.1.1,b,i.1.2,i.2)
def merged (z : Co n (Angles G) → ℝ) : Config G n := vary (vary 1 (portion z true)) (portion z false)
lemma merged_read (z : Co n (Angles G) → ℝ) (x : Site n) (i : Axis) : letterAngle false i (cvec (fun j => z (x,j))) = G.mat (merged z (x,i)) := by
  have he b : angle (G:=G) b i (cvec (fun j => z (x,j))) = colorUp G (paint G _ (portion z b) (x,i)) := rfl
  change NormedSpace.exp _ * NormedSpace.exp _ = _; simp only [he,complexLie_real,merged,vary,bump,G.mat_mul,G.mat_lieExp,Pi.one_apply,mul_one]
lemma merged_inv (z : Co n (Angles G) → ℝ) (x : Site n) (i : Axis) : letterAngle true i (cvec (fun j => z (x,j))) = G.mat (merged z (x,i))⁻¹ := by
  rw [show G.mat (merged z (x,i))⁻¹ = _ from G.mat_inv _,← one_mul (letterAngle true _ _), ← G.mat_star_mul (merged z (x,i)),mul_assoc,← merged_read]; rw [show letterAngle false i (cvec (fun j => z (x,j))) * letterAngle (G:=G) true i (cvec (fun j => z (x,j))) = 1 from letter_cancel false i _, mul_one]
lemma portion_diff (b : Bool) : ContDiff ℝ ω (fun z : Co n (Angles G) → ℝ => portion z b) := contDiff_pi.mpr fun _ => contDiff_apply ..
lemma merged_diff : MatDiffAt (merged (G:=G) (n:=n)) 0 := ((matDiffAt_const 1).vary (portion_diff true).contDiffAt).vary (portion_diff false).contDiffAt

def channel (n : Side) (b : Bool) : Matrix (Co n (Angles G)) (BondKey G n) ℝ := of fun x i => if x=(i.1.1,b,i.1.2,i.2) then 1 else 0

def lane (b : Bool) : Matrix (Angles G) (Axes G) ℂ := of fun i j => if i=(b,j) then 1 else 0
lemma channel_apply (b : Bool) (z : Loops.Links G n) (x : Site n) (u : Bool) (i : Axis) (j : G.ColorIndex) : (channel n b *ᵥ z) (x,u,i,j) = if u=b then z ((x,i),j) else 0 := by
  by_cases he : u=b <;> simp [channel,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,ite_mul,ite_and,he]
lemma lane_apply (b u : Bool) (v : CSpace (Axes G)) (i : Axes G) : (lane b *ᵥ v) (u,i) = if u=b then v i else 0 := by by_cases he : u=b <;> simp [lane,Matrix.mulVec,dotProduct,ite_mul,he]
lemma channel_routed (b : Bool) (i : Site n) : Routed (Equiv.refl (Co n (Angles G))) (linksGrid G n) i i (cmat (channel n b)) (lane b) := by
  refine Routed.of_vector fun v => funext fun ⟨x,u,j,k⟩ => ?_; rw [plane_apply,Equiv.refl_apply,lane_apply]
  by_cases hh : u=b <;> simp [cmat_apply,Bloch.approached,channel,Fintype.sum_prod_type,ite_and, Matrix.mulVec,dotProduct,apply_ite (fun r : ℝ => (r:ℂ)),ite_mul,plane, hh, linksGrid]

lemma merged_channel (v w : Loops.Links G n) : merged (channel n true *ᵥ v + channel n false *ᵥ w) = vary (vary 1 v) w := by
  unfold merged; congr 1
  · congr 1; funext ⟨⟨x,i⟩,j⟩; simp [portion,channel_apply]
  funext ⟨⟨x,i⟩,j⟩; simp [portion,channel_apply]
lemma bank_channel (f : Config G n → ℝ) (v : Loops.Links G n) : bank (channel n false) (channel n true) (f ∘ merged) v = cost f (vary 1 v) := by unfold bank cost; simp only [Function.comp_def,merged_channel]
end YM.Push.Loops.Paths
