import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shutter
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Trail

/-!
# Block gauges for precision and local logs

Use ONLY for estimates: transform the stored real V, never branch
reset. The plate is independent of Y,k,width, except stencil predicates
on seeds. Other quantities (b,C,V) might need genuine Y transformed.
Do not treat this as transporting all integrand legs via `rinse`; the
row transforms use transported D constitutive law. Frame G verified.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

namespace Rotation
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

def shade (z : ι→G.El) (v : ι × G.ColorIndex → ℝ) : ι × G.ColorIndex → ℝ :=
    stand fun i => G.adjoint (z i) (erect G v i)
def colorwise (z : ι→G.El) : Matrix (ι × G.ColorIndex) (ι × G.ColorIndex) ℝ := Matrix.of (fun i j =>
    shade z (stand (sing j)) i)

omit [Fintype ι] in
lemma off (z : ι → G.El) (i j : ι×G.ColorIndex) (hi : i.1 ≠ j.1) : colorwise z i j=0 := by
  simp only [colorwise,of_apply,shade,rises,stand,sing,Pi.single_eq_of_ne hi,map_zero]; rfl
lemma shade_act (z : ι→G.El) (u : ι × G.ColorIndex → ℝ) : colorwise z *ᵥ u=shade z u := by
  funext p
  let U := erect G u
  let x : G.Color →ₗ[ℝ] ℝ := LinearMap.comp (LinearMap.proj p.2) (WithLp.linearEquiv 2 ℝ _).toLinearMap
  let L : (ι → G.Color) →ₗ[ℝ] ℝ := x.comp ((G.adjoint (z p.1)).comp (LinearMap.proj p.1))
  have he (v : ι → G.Color) : L (∑ i, stand v i • sing i) = L v := congr_arg L (stand_spanned v)
  change _ = L U; rw [← he,map_sum]; simp_rw [map_smul]
  unfold Matrix.mulVec dotProduct; refine sum_congr rfl fun q _ => ?_
  change L (sing q)*u q = u q * L (sing q)
  ring
lemma shade_pair (z : ι→G.El) (v w : ι × G.ColorIndex → ℝ) : dotProduct (colorwise z *ᵥ v) (colorwise z *ᵥ w)=dotProduct v w := by
  let A := colorwise z
  have he (u) : dotProduct (A *ᵥ u) (A *ᵥ u)=dotProduct u u := by
    unfold A; rw [shade_act]; unfold shade
    change dotProduct _ _ = dotProduct (stand (erect G u)) (stand (erect G u)); rw [← stand_squared,← stand_squared]; simp
  change dotProduct (A *ᵥ v) (A *ᵥ w)=dotProduct v w
  have hv := he (v+w); simp only [Matrix.mulVec_add,dotProduct_add,add_dotProduct,he] at hv
  rw [dotProduct_comm (A *ᵥ w) (A *ᵥ v),dotProduct_comm w v] at hv; nlinarith
lemma inverse_up (z : ι→G.El) : (colorwise z).transpose * colorwise z=1 := by
  refine Matrix.ext_iff_mulVec.mpr ?_; intro v; let K := colorwise z
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]; funext i
  let u : ι × G.ColorIndex → ℝ := Pi.single i 1
  have hp (g : ι × G.ColorIndex → ℝ) : dotProduct u g=g i := by
    unfold dotProduct
    rw [Finset.sum_eq_single i]
    · unfold u; simp
    · intro j _ he; unfold u; rw [Pi.single_eq_of_ne he,zero_mul]
    simp
  rw [← hp (K.transpose *ᵥ (K *ᵥ v)), ← hp v]
  change dotProduct u (K.transpose *ᵥ (K *ᵥ v)) = dotProduct u v
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]; exact shade_pair ..
lemma upside (z : ι→G.El) : colorwise z * (colorwise z).transpose = 1 := mul_eq_one_comm.mp (inverse_up z)
end Rotation

namespace Coat
open Rotation
variable (X : Coat T F)

def rinse (z : Site c→G.El) : Coat T F := { X with V := gauge z X.V }

lemma retains (z : Site c→G.El) (h : X.manifest) : (X.rinse z).manifest := by
  unfold manifest rinse; rw [RG.gauge_flags]; exact h

lemma lenses (z : Site c→G.El) (v : Directions G f) :
    X.lens (spinRow S z v) = spinRow S z (X.lens v) := by
  funext i; unfold lens spinRow; by_cases he : X.Hot i <;> simp [he]
lemma contract_step (z : Site c→G.El) (h : P.Funds S T) :
    (X.rinse z).form * colorwise (z ∘ atEdge S) = colorwise (z ∘ root S) * X.form := by
  obtain ⟨K,C,H,-⟩ := h.feeds
  refine Matrix.ext_iff_mulVec.mpr ?_; intro v
  let W := spinRow S z (erect G v)
  have he : colorwise (z ∘ atEdge S) *ᵥ v=stand W := shade_act ..
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, he,shade_act]
  have hh : X.form *ᵥ v=stand (fun p => scale • X.motion (erect G v) p) := by
    funext p; exact (X.charged_for H (erect G v) p).symm
  rw [hh]; unfold shade; rw [rises]; funext i
  rw [← (X.rinse z).charged_for H]; unfold motion stand
  let a := i.1
  change scale* (if X.selected i.1.1 (spot S i.1.2) then orientedRow T X.R i.1.1 i.1.2 (gauge z X.V) (X.lens W) else 0) i.2 =
    G.adjoint (z (root S i.1)) (scale • (_:G.Color)) i.2
  split
  next he => unfold W; rw [X.lenses,oriented_under T H, map_smul]; rfl
  next hz => simp

lemma sleepy_commute (z : Site c→G.El) : X.sleepy * colorwise (z ∘ atEdge S) = colorwise (z ∘ atEdge S)*X.sleepy := by
  ext i j; rw [sleepy,diagonal_mul,mul_diagonal]
  by_cases he : i.1=j.1
  · rw [he]; ring
  rw [off (z ∘ atEdge S) i j he,mul_zero,zero_mul]

lemma rinse_invar (z : Site c→G.El) (h : P.Funds S T) :
    (X.rinse z).plate * colorwise (z ∘ atEdge S) = colorwise (z ∘ atEdge S) * X.plate := by
  let a := colorwise (z ∘ atEdge S); let b := colorwise (z ∘ root S)
  let W := (X.rinse z).form
  have hy : W*a=b*X.form := X.contract_step z h
  have he : aᵀ*Wᵀ=X.form.transpose*bᵀ := by rw [← transpose_mul,hy,transpose_mul]
  have ht : Wᵀ*b=a * X.form.transpose := by
    rw [← Matrix.one_mul (Wᵀ), show (1:Matrix ..)=a*a.transpose from (upside _).symm, Matrix.mul_assoc a a.transpose W.transpose, he, Matrix.mul_assoc a, Matrix.mul_assoc X.form.transpose,show b.transpose*b=1 from inverse_up _, Matrix.mul_one]
  change (Wᵀ*W+X.sleepy)*a = a*(X.form.transpose * X.form+X.sleepy)
  rw [add_mul,mul_add,Matrix.mul_assoc Wᵀ,hy, ← Matrix.mul_assoc Wᵀ b,ht, Matrix.mul_assoc a,X.sleepy_commute z]
end Coat
end YM.ConnectedActivityE6
