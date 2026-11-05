import YM.Next.SCHEDULE.Melt
import YM.UVNext.PRICED_KERNELS.Degree


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# One-plaquette Wilson deficit

Real coordinates, careful factor-of-two and matrix Frobenius normalization.
For .delta top, the only nontrivial unmasked correction through quartic order
at the last layer can be derived from this local Taylor deficit, an invariant
tensor in *curvature* coordinates. No single-trace formula in abstract Lie
brackets substituted. Uses authoritative energy comparison (`price_limit`, plog
& adjoint library) on G. Analytic germs, all of degrees 0--4. No new hypotheses
from period nor L, nor even simple used here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice RG RG.Supply Wilson Precision Exterior Gauge Work.F03
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
attribute [local instance] Gauge.frobInner

variable (G : Gauge)
-- k chart is not necessarily inverse on the closure (indeed k = 0
-- possibly even away from 1). Use only at graded positive jets.
def view (x : G.Color) := G.curvature (G.lieExp x)
def term (x : G.Color) := (‖x‖:ℝ)^2/2
def missing (x : G.Color) := G.price (G.lieExp x) - term G (view G x)
def polish (c : ℝ) : G.Color [×4]→L[ℝ] ℝ := c • fourth (missing G)

lemma expFlip (b : G.Color) : G.lieExp (-b)=(G.lieExp b)⁻¹ := by
  apply G.mat_injective
  simp only [G.mat_lieExp, G.mat_inv, map_neg,NormedSpace.star_exp,G.colorMat_skew]
lemma expUnder (u : G.El) (b : G.Color) : G.lieExp (G.adjoint u b)=u*(G.lieExp b)*u⁻¹ := by
  apply G.mat_injective
  simp; exact G.exp_conjugate u (G.colorMat b)

lemma view_cont : ContDiff ℝ ω (view G) := by
  unfold view Gauge.curvature; simp_rw [G.mat_inv]
  refine G.projectColor.toContinuousLinearMap.contDiff.comp ((G.exp_jet.sub ?_).const_smul (1/2:ℝ))
  exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp G.exp_jet
lemma term_cont : ContDiff ℝ ω (term G) :=
  ContDiff.div_const (contDiff_id.norm_sq ℝ) _
lemma missing_cont : ContDiff ℝ ω (missing G) := by
  apply contDiff_iff_contDiffAt.mpr
  suffices hg : ContDiff ℝ ω (fun a => ‖G.mat (G.lieExp a) - 1‖^2 / G.colorScale^2 /2) by
    have hh (x : G.Color) : G.price (G.lieExp x)= ‖G.mat (G.lieExp x) - 1‖^2 / G.colorScale^2 /2 := by
      rw [← div_pow]; change _ = G.chord _ ^ 2/2; rw [G.chord_price]; ring
    intro y; unfold missing; simp_rw [hh]; exact hg.contDiffAt.sub ((term_cont G).contDiffAt.comp _ (view_cont G).contDiffAt)
  exact ((((G.exp_jet.sub (contDiff_const (c:=1))).norm_sq ℝ).div_const _).div_const _) 

lemma expRay (x : G.Color) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • x))) (G.colorMat x) 0 := by
  have ht : HasDerivAt (fun t : ℝ => t • x) x 0 := by simpa using (hasDerivAt_id' (0:ℝ)).smul_const x
  exact (show HasFDerivAt (fun a => G.mat (G.lieExp a)) G.colorMat.toContinuousLinearMap ((0:ℝ) • x) by rw [zero_smul]; exact G.expDiff_zero).comp_hasDerivAt 0 ht
lemma view_zero : view G 0=0 := by simp [view]
lemma view_one : UpTo 1 (id : G.Color → G.Color) (view G) := by
  have h := (view_cont G).contDiffAt (x:=0)
  refine ⟨contDiffAt_id, h, fun j hj => ?_⟩
  ext1 v
  interval_cases j
  · rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply,view_zero]; rfl
  rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,fderiv_id]
  let x := v 0
  have ht : HasDerivAt (fun t : ℝ => t • x) x 0 := by simpa using (hasDerivAt_id' (0:ℝ)).smul_const x
  have hg : DifferentiableAt ℝ (view G) ((0:ℝ) • x) := by rw [zero_smul]; exact h.differentiableAt (by simp)
  exact (curvature_of_hasDerivAt (expRay G x)).unique (by simpa using! (hg.hasFDerivAt.comp_hasDerivAt 0 ht)) -- composition unfolds

lemma target_parity (x : G.Color) : missing G (-x)=missing G x := by
  simp [missing,view,term,expFlip]
lemma target_fixed (u : G.El) (x : G.Color) : missing G (G.adjoint u x)=missing G x := by
  simp [missing,expUnder,view,G.curvature_conjugate,term]

lemma derivative_symm {g : G.Color →L[ℝ] G.Color} (he : missing G ∘ g=missing G) (j : ℕ) (v : Fin j → G.Color) :
    iteratedFDeriv ℝ j (missing G) 0 (fun i => g (v i)) = iteratedFDeriv ℝ j (missing G) 0 v := by
  have hh := g.iteratedFDeriv_comp_right (missing_cont G) 0 (i:=j) le_top
  rw [g.map_zero,he] at hh
  exact DFunLike.congr_fun hh.symm v
lemma polish_symm (u : G.El) (c : ℝ) (v : Fin 4 → G.Color) : polish G c (fun i => G.adjoint u (v i))=polish G c v := by
  have hh := derivative_symm G (g:=(G.adjoint u).toContinuousLinearMap)
    (funext fun x => target_fixed G u x) 4 v
  unfold polish fourth; simp only [smul_apply]; rw [← hh]; rfl
lemma missing_odd (v : Fin 3 → G.Color) : iteratedFDeriv ℝ 3 (missing G) 0 v=0 := by
  let g := (-1:ℝ) • ContinuousLinearMap.id ℝ G.Color
  have he : ∀ x : G.Color, g x = -x := by intro x; simp [g]
  have hh := derivative_symm G (g:=g) (funext fun x => by simp [he,target_parity]) 3 v
  let P := iteratedFDeriv ℝ 3 (missing G) 0
  change (P fun i => (-1:ℝ) • v i)=P v at hh
  rw [P.map_smul_univ (fun _ => (-1:ℝ)) v] at hh
  norm_num [smul_eq_mul] at hh; linarith

lemma missing_lower (j : ℕ) (hj : j < 4) : iteratedFDeriv ℝ j (missing G) 0=0 := by
  have hd (x : G.Color) : Tendsto (fun t : ℝ => missing G (t • x) / t^2) (𝓝[≠] 0) (𝓝 0) := by
    have hm := price_limit (V:=fun t => G.lieExp (t • x)) (by simp) (expRay G x)
    have hv : HasDerivAt (fun t : ℝ => view G (t • x)) x 0 := curvature_of_hasDerivAt (expRay G x)
    have hc : Tendsto (fun t : ℝ => t⁻¹ • view G (t • x)) (𝓝[≠] 0) (𝓝 x) := by
      simpa [view_zero] using (hasDerivAt_iff_tendsto_slope_zero.mp hv)
    have ha : Tendsto (fun t : ℝ => missing G (t • x) / t^2) (𝓝[≠] 0) (𝓝 (‖x‖^2/2-‖x‖^2/2)) :=
      (hm.sub ((hc.norm.pow 2).div_const 2)).congr' (Eventually.of_forall fun t => by
        unfold missing term
        rw [norm_smul,Real.norm_eq_abs,mul_pow, sq_abs, inv_pow]; ring)
    simpa using ha
  obtain ⟨h₁,h₂,h₃⟩ := hessian_of_limit (Q:=fun _ _ => 0) ((missing_cont G).contDiffAt.of_le le_top) (by simpa using hd) (by simp) (by simp)
  ext1 v
  interval_cases j
  · exact h₁
  · rw [iteratedFDeriv_one_apply,h₂]; rfl
  · rw [show v=![v 0,v 1] from funext fun i => by fin_cases i <;> rfl,h₃]; rfl
  exact missing_odd ..

/-- At the chosen top, adding the same polynomial but in *path curvature*
coordinates is valid through degree four. Restore the Wilson normalization
on actual links via G's local plog later, not claiming the polynomial is
exactly the deficit outside log chart (or even inside it). -/
lemma unpolished (c : ℝ) :
    UpTo 4 (c • missing G) ((homog (polish G c)) ∘ view G) := by
  have he := (fourth_restores (missing_cont G).contDiffAt (missing_lower G)).weight c
  have hx : (homog (polish G c)) = c • (homog (fourth (missing G))) := by
    ext x; unfold homog polish; rw [smul_apply]; rfl
  refine he.trans ?_
  have H : UpTo 4 (homog (polish G c) ∘ id) (homog (polish G c) ∘ view G) := UpTo.valuation_comp (contDiff_homog _).contDiffAt
    (homog_lower _) (view_one G) rfl (view_zero G)
  rw [comp_id,hx] at H; rw [hx]; exact H
section field
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] {E F : A → ℝ} {T U : A → ℝ} {n : ℕ}
lemma UpTo.germ (h : UpTo n E F) (hx : E=ᶠ[𝓝 0] T) (hu : F=ᶠ[𝓝 0] U) : UpTo n T U := by
  refine ⟨h.left.congr_of_eventuallyEq hx.symm,h.right.congr_of_eventuallyEq hu.symm,fun j hj => ?_⟩
  rw [← (hx.iteratedFDeriv ℝ j).self_of_nhds, ← (hu.iteratedFDeriv ℝ j).self_of_nhds,h.jets j hj]

variable (p : A → G.El) (h : ContDiffAt ℝ ω (fun a => G.mat (p a)) 0) (he : p 0=1) (c : ℝ)
include h he
lemma apply_polish :
    let E (a:A) := c * (G.price (p a) - ‖G.curvature (p a)‖^2/2)
    UpTo 4 E (fun a => homog (polish G c) (G.curvature (p a))) := by
  intro E
  have hv : Tendsto p (𝓝 0) (𝓝 1) := by
    have hx : Topology.IsEmbedding G.mat := (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding
    rw [hx.tendsto_nhds_iff,← he]; exact h.continuousAt
  have hk := hv.eventually G.plog_right
  have hz : G.mat (p 0)=1 := he ▸ G.mat_one
  let f (x : A) := G.plog (G.mat (p x))
  have hd : ContDiffAt ℝ ω f 0 := (show ContDiffAt ℝ ω G.plog (G.mat (p 0)) by rw [hz]; exact G.plog_diff).comp (f:=fun x => G.mat (p x)) (0:A) h
  have hZ : f 0=0 := by unfold f; rw [hz]; exact G.plog_one
  refine ((unpolished G c).comp hd hZ).germ ?_ ?_ <;>
    filter_upwards [hk] with i hi
  · show c * (G.price (G.lieExp (f i))-_)=_; unfold f view; rw [hi]; rfl
  change homog (polish G c) (G.curvature (G.lieExp (G.plog (G.mat (p i)))))=_; rw [hi]

lemma price_jet (d : ℝ) (hd : 0 ≤ 1-d) :
    let c := 1-d
    UpTo 4 (fun a => G.price (p a)) (fun a => d * G.price (p a)+
      ‖Real.sqrt c • G.curvature (p a)‖^2/2 + homog (polish G c) (G.curvature (p a))) := by
  intro c
  let K x := G.curvature (p x); let P x := G.price (p x)
  let L x := d * P x + ‖Real.sqrt c • K x‖^2/2
  let T x := c * (P x-‖K x‖^2/2)
  have hP : ContDiffAt ℝ ω P 0 := price_smooth h -- Type universe X Type!
  have hK : ContDiffAt ℝ ω K 0 := by
    simp_rw [K,Gauge.curvature, G.mat_inv]
    refine G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp _ ((h.sub ?_).const_smul _)
    exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ h
  have hL : ContDiffAt ℝ ω L 0 := (contDiffAt_const.mul hP).add (((hK.const_smul (Real.sqrt c)).norm_sq ℝ).div_const _)
  have hh := (UpTo.refl hL 4).add (apply_polish G p h he c)
  have he : P=L+T := by
    funext x
    unfold L T P K
    simp only [Pi.add_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (show 0 ≤ c from hd)]
    unfold c; ring
  change UpTo 4 P _; rw (occs := .pos [1]) [he]
  exact hh
end field
end YM.UVNext.PricedKernels
