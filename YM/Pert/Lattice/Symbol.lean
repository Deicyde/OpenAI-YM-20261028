import YM.Pert.Lattice.Cubical
import YM.Pert.Lattice.TopLinear
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Margins
/-! Top Wick subtraction covariance on the infinite lattice, not a continuum kernel used as coefficients. -/
set_option autoImplicit false
set_option maxRecDepth 9000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Pert.Full
open Lattice Filter MeasureTheory Matrix Set Bare Labels
open scoped Topology BigOperators ENNReal
variable {G : Gauge} {d e j : ℕ}
abbrev CosKey (G : Gauge) (d : ℕ) := {z : Labels.Key G // z.1 ≤ d}
instance : Fintype (CosKey G d) := by
  refine Fintype.ofInjective (fun (z : CosKey G d) => (Sigma.mk (β:=fun i : Fin (d+1) => Fin (dim G i.val)) ⟨z.val.1,by omega⟩ z.val.2)) ?_
  intro u v h; apply Subtype.ext; apply Sigma.ext _ _
  · exact congrArg (Fin.val ∘ Sigma.fst) h
  exact (Sigma.ext_iff.mp h).2

structure Channel (G : Gauge) where
  sine : Bool
  axis : Axis
  color : G.ColorIndex
deriving Fintype, DecidableEq

def material (c : Channel G) (p : E4) : Lattice.Links ℤ G.Color := fun l : Edge Cover =>
   ((if c.axis=l.2 then (1:ℝ) else 0) * wave c.sine l.1 p) • EuclideanSpace.basisFun G.ColorIndex ℝ c.color
lemma mat_cont (c : Channel G) (l : Edge Cover) : Continuous (fun p : E4 => material c p l) := by
  unfold material; fun_prop
lemma wide_base_cont (V : E4 → Lattice.Links ℤ G.Color) (h : ∀ l, Continuous (fun p=> V p l)) (s : Signed) (x : Cover) : Continuous (fun p => wideCore G j x (wideLink G s (V p))) := by
  refine continuous_pi (fun i : Axis => continuous_pi fun k : Axis => continuous_pi fun r : Fin j→Axis => ?_)
  simp_rw [wideCore_apply,wideCurl,wideLink_apply]; fun_prop (disch := assumption)
lemma premap_cont {F : E4 → Bare.Response G j} (hF : Continuous F) (g : Bare.Response G j →ₗ[ℝ] Labels.Taylor G j) : Continuous (g ∘ F) := g.continuous_of_finiteDimensional.comp (f:=F) hF
lemma one_core_cont (s : Signed) (a : ℝ) (x : Cover) (V : E4 → Lattice.Links ℤ G.Color) (h : ∀ l, Continuous (fun p=> V p l)) : Continuous (fun p=> (Labels.Taylor.turn (j:=j) s.ortho ∘ₗ (a^(-(j+2:ℤ)) • Bare.radialMap) ∘ₗ wideCore G j (affine s⁻¹ 0 x) ∘ₗ wideLink G s) (V p)) := by
  apply premap_cont (wide_base_cont V h s (affine s⁻¹ 0 x)) (Labels.Taylor.turn s.ortho ∘ₗ (a^(-(j+2:ℤ)) • Bare.radialMap))
lemma whole_apply (a : ℝ) (x : Cover) (U : Lattice.Links ℤ G.Color) : wideLinear G j a x U = (Fintype.card Signed:ℝ)⁻¹ • ∑ s : Signed,
  (Labels.Taylor.turn s.ortho ∘ₗ (a^(-(j+2:ℤ)) • Bare.radialMap) ∘ₗ wideCore G j (affine s⁻¹ 0 x) ∘ₗ wideLink G s) U := by simp [wideLinear]
lemma core_sum_cont {D : Type} [AddCommMonoid D] [TopologicalSpace D] [ContinuousAdd D] [SMul ℝ D] [ContinuousConstSMul ℝ D] (F : Signed → E4 → D) (c : ℝ) (h : ∀ s, Continuous (F s)) : Continuous (fun x => c • ∑ s : Signed, F s x) := (continuous_finsetSum (s:=Finset.univ) (fun s _ => h s)).const_smul c
lemma wide_cont (a : ℝ) (x : Cover) (V : E4 → Lattice.Links ℤ G.Color) (h : ∀ l, Continuous (fun p=> V p l)) :
     Continuous (fun p => wideLinear G j a x (V p)) := by
  simp_rw [whole_apply]; exact core_sum_cont (D:=Labels.Taylor G j) _ _ (fun s=> one_core_cont (G:=G) (j:=j) s a x V h)

def leg (a : ℝ) (z : Key G) (c : Channel G) (p : E4) : ℝ := (axes G z.1).coord z.2 (wideLinear G z.1 a (0:Cover) (material c p))
lemma leg_cont (a : ℝ) (z : Key G) (c : Channel G) : Continuous (fun p => leg a z c p) := by
  unfold leg
  have e : Continuous ((axes G z.1).coord z.2 : Labels.Taylor G z.1→ℝ) := LinearMap.continuous_of_finiteDimensional _
  exact e.comp (wide_cont _ _ _ (mat_cont c))

def spectral (a : ℝ) (u v : Key G) (p : E4) : ℝ := (delta p)⁻¹ * ∑ c, leg a u c p * leg a v c p
def link (a : ℝ) (u v : Key G) := volumeFactor * ∫ p in cube, spectral a u v p
lemma spectral_s (a : ℝ) (u v : Key G) : spectral a u v = spectral a v u := funext fun p => by unfold spectral; simp only [mul_comm (leg a u _ _) (leg a v _ _)]
lemma link_symm (a : ℝ) (u v : Key G) : link a u v = link a v u := by simp [link,spectral_s a u v]
lemma spectral_integrable (a : ℝ) (u v : Key G) : IntegrableOn (spectral a u v) cube := by
  have H := continuous_finsetSum (Finset.univ (α:=Channel G)) (fun c _ => (leg_cont a u c).mul (leg_cont a v c))
  obtain ⟨C,hC⟩ := IsCompact.exists_bound_of_continuousOn cube_compact H.continuousOn
  exact delta_integrable.mul_bdd H.aestronglyMeasurable ((ae_restrict_mem cube_compact.isClosed.measurableSet).mono hC)

variable (G d) in
def shellCov (a : ℝ) : Matrix (CosKey G d) (CosKey G d) ℝ := of (fun u v => link a u.val v.val)
lemma form_spectral (a : ℝ) (v : CosKey G d → ℝ) (p : E4) : v ⬝ᵥ ((of fun i j : CosKey G d => spectral a i.val j.val p) *ᵥ v) =
   (delta p)⁻¹ * ∑ c, (∑ i : CosKey G d, leg a i.val c p * v i)^2 := by
  let f (i : CosKey G d) (c : Channel G) := leg a i.val c p
  let t (c : Channel G) := ∑ i, f i c * v i
  have row (u : CosKey G d) :
      ((of fun i j : CosKey G d => spectral a i.val j.val p) *ᵥ v) u = (delta p)⁻¹ * ∑ c, f u c * t c := by
    unfold Matrix.mulVec dotProduct spectral
    change ∑ i : CosKey G d, ((delta p)⁻¹ * ∑ c, f u c * f i c) * v i = _
    dsimp only [t]; simp_rw [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
  change (∑ i : CosKey G d, v i * _) = (delta p)⁻¹ * ∑ c : Channel G, t c ^ 2
  simp_rw [row,mul_left_comm _ (delta p)⁻¹,← Finset.mul_sum]
  apply congrArg ((delta p)⁻¹ * ·); simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_
  simp only [← mul_assoc,← Finset.sum_mul]; rw [show ∑ i, v i * f i c = t c from Finset.sum_congr rfl fun i _ => by ring]; ring
lemma integrate_link (a : ℝ) (v : CosKey G d → ℝ) :
  v ⬝ᵥ (shellCov G d a *ᵥ v) = volumeFactor * ∫ p in cube, v ⬝ᵥ ((of fun i j : CosKey G d => spectral a i.val j.val p) *ᵥ v) := by
  unfold shellCov link dotProduct Matrix.mulVec; simp only [dotProduct,of_apply,← mul_assoc,Finset.mul_sum]; simp_rw [mul_assoc,← integral_mul_const,← Finset.mul_sum]
  simp_rw [mul_left_comm _ volumeFactor,← Finset.mul_sum]; apply congrArg (volumeFactor * ·); rw [integral_finsetSum _ fun i _ => Integrable.const_mul (integrable_finsetSum _ fun j _ => (spectral_integrable a _ _).mul_const (v j)) (v i)]
  apply Finset.sum_congr rfl; intro b _; rw [integral_const_mul]; congr 1
  rw [integral_finsetSum]; exact fun i _ => (spectral_integrable a _ _).mul_const (v i)
lemma shellCov_pos (a : ℝ) : (shellCov G d a).PosSemidef := by
  apply posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨IsHermitian.ext (fun u v => link_symm _ _ _),fun x => ?_⟩
  rw [star_trivial,integrate_link]; simp_rw [form_spectral]
  unfold volumeFactor; exact mul_nonneg (by have := Real.pi_pos; positivity) (integral_nonneg fun p => by unfold delta; positivity)
end YM.Pert.Full
