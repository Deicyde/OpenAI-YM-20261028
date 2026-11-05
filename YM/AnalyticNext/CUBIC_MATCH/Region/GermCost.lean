import YM.AnalyticNext.CUBIC_MATCH.Region.Expressions
import YM.AnalyticNext.CUBIC_MATCH.Terms.Products
import YM.Next.BOUNDARY.Coordinates
import YM.Next.EXTRACTION.Tails
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Post


set_option warningAsError false

/-!
# Compose representations on rays

Only first and second terms needed to read the cost of norm-square price.
Use actual group matrix auxiliaries, calibrate with `colorScale`. Formal
kernel maps not commitments about the clipped functions/circles of analyticity.
Pay coefficient expressions pointwise (no arbitrary rates for substituted
larger period maps).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice RG Wilson Precision Exterior Tree Tensor Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {k : ℕ} {ι μ : Type*} {c : μ → Side}
  {θ C B D H : ℝ}

/-- Pointwise path, with no assertions at finite radius. -/
abbrev GermRead (G : Gauge) (c : μ → Side) (E : Type*) := SiteRead G c (ℝ → E)
section norm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def makesTerm (f : GermRead G c E) (k : ℕ) : SiteRead G c E := fun p x a => term k (f p x a)

lemma positive_nil {g : E} (h : 0<k) : term k (fun _ : ℝ => g)=0 := by
  unfold term iteratedDeriv; rw [iteratedFDeriv_const_of_ne h.ne']; simp

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Bilinear map for the second coefficient (without factor 2). -/
def sec (f : E → F) (e : E) : E →L[ℝ] E →L[ℝ] F := ((2:ℕ).factorial:ℝ)⁻¹ • fderiv ℝ (fderiv ℝ f) e

lemma second_line (f : E → F) (e x : E) : diagonal (coeff f 2 e) x=sec f e x x := by
  unfold sec diagonal coeff; simp only [smul_apply, iteratedFDeriv_two_apply]



end norm

namespace LocalRep

lemma coin {f : SiteRead G c G.Color} (h : LocalRep c k θ C f) :
    LocalRep c k θ (G.colorScale*C) (fun p x a => G.colorMat (f p x a)) :=
  h.linear_bound G.colorMat.toContinuousLinearMap G.colorScale_pos.le fun x => (G.colorMat_norm x).le
lemma tint {f : SiteRead G c G.Mat} (h : LocalRep c k θ C f) :
    LocalRep c k θ (G.colorScale⁻¹*C) (fun p x a => G.projectColor (f p x a)) :=
  h.linear_bound G.projectColor.toContinuousLinearMap (inv_nonneg.mpr G.colorScale_pos.le) fun x =>
    (G.project_norm x).trans_eq (div_eq_inv_mul ..)


/-- Frobenius. -/
def mirror (G : Gauge) : G.Mat →L[ℝ] G.Mat := (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).toContinuousLinearMap
lemma mirror_price {f : SiteRead G c G.Mat} (h : LocalRep c k θ C f) : LocalRep c k θ C (fun p x a => star (f p x a)) := by
  have hh (x : G.Mat) : ‖mirror G x‖ ≤ 1*‖x‖ := by rw [one_mul,show mirror G x=star x from rfl,norm_star]
  have he := h.linear_bound (mirror G) zero_le_one hh; rw [one_mul] at he; exact he
end LocalRep

lemma smoothed_star {f : ℝ → G.Mat} (h : ContDiffAt ℝ ω f 0) : ContDiffAt ℝ ω (fun t => star (f t)) 0 :=
  (LocalRep.mirror G).contDiff.contDiffAt.comp _ h
lemma term_star {f : ℝ → G.Mat} (h : ContDiffAt ℝ ω f 0) : term k (fun t => star (f t))=star (term k f) :=
    term_linear (LocalRep.mirror G) (h.of_le le_top)
lemma expRead {f : SiteRead G c G.Color} (h : LocalRep c 1 θ C f) :
    let F (p) (x : Site (c p)) (a : Dir G (c p)) (t : ℝ) := G.mat (G.lieExp (t • f p x a))
    LocalRep c 1 θ (G.colorScale*C) (makesTerm F 1) ∧
      LocalRep c 2 θ (‖sec (fun u => G.mat (G.lieExp u)) 0‖*C*C) (makesTerm F 2) := by
  intro F
  let L := fun u => G.mat (G.lieExp u)
  constructor
  · refine h.coin.fits fun p x a => ?_
    let z := f p x a
    have he : HasFDerivAt L (G.colorMat.toContinuousLinearMap) ((0:ℝ)•z) := by rw [zero_smul]; exact G.expDiff_zero
    have ht : HasDerivAt (fun t : ℝ => t • z) z 0 := by simpa using! (hasDerivAt_id' (0 : ℝ)).smul_const z
    unfold makesTerm; rw [term_one]; exact (he.comp_hasDerivAt 0 ht).deriv.symm
  refine (h.bilinear h (sec L 0)).fits fun p x a => ?_
  have ht := term_ray (f:=L) (k:=2) (G.exp_jet.contDiffAt.of_le le_top) (f p x a); rw [second_line] at ht; exact ht.symm

lemma term_mul_one {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] {f g : ℝ → R}
    (h : ContDiffAt ℝ ω f 0) (hp : ContDiffAt ℝ ω g 0) (hx : f 0=1) (hy : g 0=1) :
    term 1 (fun t => f t*g t)=term 1 f+term 1 g ∧ term 2 (fun t => f t*g t)=term 2 f + term 1 f*term 1 g + term 2 g := by
  rw [term_mul 1 h hp,term_mul_two h hp]
  simp only [Finset.sum_range_succ,Finset.range_zero, Finset.sum_empty,zero_add,term_zero,tsub_zero,hx,hy,
    one_mul, Nat.sub_self,term_one,mul_one]; constructor <;> abel

section package
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- Two terms of a matrix path whose zeroth term is 1. Useful in frame germs. -/
structure RayReceipt (c : μ → Side) (η C D : ℝ) (f : GermRead G c R) : Prop where
  smooth (p : μ) (x a) : ContDiffAt ℝ ω (f p x a) 0
  initial (p : μ) (x a) : f p x a 0=1
  first : LocalRep c 1 η C (makesTerm f 1)
  second : LocalRep c 2 η D (makesTerm f 2)

variable {f g : GermRead G c R}
omit [CompleteSpace R] in
lemma RayReceipt.raisePrice (h : RayReceipt c θ C D f) (hb : C≤B) (he : D≤H) : RayReceipt c θ B H f :=
  ⟨h.smooth,h.initial,h.first.raisePrice hb,h.second.raisePrice he⟩
omit [CompleteSpace R] in
lemma RayReceipt.fits (h : RayReceipt c θ C D f) (he : ∀ p x a, ContDiffAt ℝ ω (g p x a) 0)
    (hp : ∀ p x a, f p x a=ᶠ[𝓝 0] g p x a) : RayReceipt c θ C D g :=
  ⟨he,fun p x a => (hp p x a).symm.eq_of_nhds.trans (h.initial ..),h.first.fits (fun p x a => term_congr (hp p x a)),
    h.second.fits (fun p x a => term_congr (hp p x a))⟩
lemma RayReceipt.mul (h : RayReceipt c θ C D f) (g' : RayReceipt c θ B H g) : RayReceipt c θ (C+B) (D+C*B+H)
    (fun p x a t => f p x a t*g p x a t) := by
  have he p x a := term_mul_one (h.smooth p x a) (g'.smooth p x a) (h.initial p x a) (g'.initial p x a)
  exact ⟨fun p x a => (h.smooth ..).mul (g'.smooth ..),fun p x a => by rw [h.initial,g'.initial,mul_one],
    (h.first.plus g'.first).fits (fun p x a => (he p x a).1.symm),
    ((h.second.plus (h.first.ring_mul g'.first)).plus g'.second).fits (fun p x a => (he p x a).2.symm)⟩
lemma RayReceipt.back {U : GermRead G c G.Mat} (h : RayReceipt c θ C D U) : RayReceipt c θ C D
    (fun p x a t => star (U p x a t)) := by
  exact ⟨fun p x a => smoothed_star (h.smooth ..),fun p x a => by rw [h.initial,star_one],
    h.first.mirror_price.fits (fun p x a => (term_star (h.smooth ..)).symm), h.second.mirror_price.fits (fun p x a => (term_star (h.smooth ..)).symm)⟩

lemma receiptExp {f : SiteRead G c G.Color} (h : LocalRep c 1 θ C f) : RayReceipt c θ (G.colorScale*C)
    (‖sec (fun u => G.mat (G.lieExp u)) 0‖*C*C) (fun p x a t => G.mat (G.lieExp (t • f p x a))) :=
  ⟨fun p x a => G.exp_jet.contDiffAt.comp (f:=fun t : ℝ => t • f p x a) 0 (by fun_prop),
    fun p x a => by rw [zero_smul,G.mat_lieExp_zero,G.mat_one], (expRead h).1,(expRead h).2⟩
end package

section pricing
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]








end pricing
end YM.CubicMatch
