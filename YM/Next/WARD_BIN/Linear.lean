import YM.Next.WARD_BIN.Energy
import YM.Work.G02
import YM.Work.G03




/-!
# Detect the divergence of curvature jets by positively oriented links

Everything here is independent of any physical limit. Work on the lattice cover.
Finite sampling at positive edges, including transport back to the base 0;
`sample` uses the actual Lie gradient expression `euler`, not a prescribed finite difference.
Show (in agreement with the linear term at ) it reads a difference of
plaquette nets with a minus sign at leading order. Shrinking a test grid then extracts
top homogeneous degree, so finite **linear combinations** of these samples implement
prescribed divergence through that degree. No differentiability assertion about the
rounding procedure or face masks. No limit related to cutoffs `N,p` here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Lattice Wilson RG Labels Source Source.Drops Bid MeasureTheory Filter Set
open Work.G03
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {k d : ℕ}

/-- One definite transporter to the starting vertex. Later charged as full stencil. -/
def toBond (e : Edge Cover) (U : CoverConfig G) := travel U 0 (route 0 e.1 1)

/-- Transported test of Euler. -/
def sample (e : Edge Cover) (U : CoverConfig G) : G.Color := G.adjoint (toBond e U) (euler U e)

lemma sample_gauge (e : Edge Cover) (U : CoverConfig G) (t : Cover → G.El) :
    sample e (Lattice.gauge t U) = G.adjoint (t 0) (sample e U) := by
  unfold sample toBond; rw [euler_gauge, travel_gauge, route_end, ← G.adjoint_mul,
    inv_mul_cancel_right, G.adjoint_mul]

/-- Linearization uses radial links before engineering truncation along
`scaleJet`, here simply differentiating in ordinary radial *inputs*. -/
def linearSample (H : Hol G) (e : Edge Cover) : Snap G d →L[ℝ] G.Color :=
  fderiv ℝ (fun J => sample e (H.links d (expand d J) 1)) 0

private theorem linkSum_wheel (A : Snap G d) (x : Cover) (i j : Axis) :
    Exterior.linkSum (access A) x (oriented (posDir i) (posDir j)) +
      Exterior.linkSum (access A) x (oriented (posDir i) (negDir j)) =
    ∑ k ∈ Finset.range (d-1),
      (net (expand d A k) j i (castPos (x-step j)) 1 - net (expand d A k) j i (castPos x) 1) := by
  let Y := access A
  have hz : Exterior.linkSum Y x (oriented (posDir i) (posDir j)) =
      - Exterior.linkSum Y x (square j i) := by
    change Exterior.linkSum _ _ (square i j) = _
    rw [square_sum, square_sum]; abel
  have he : Exterior.linkSum Y x (oriented (posDir i) (negDir j)) =
      Exterior.linkSum Y (x-step j) (square j i) := by
    rw [square_sum]; unfold oriented
    have h₁ : x+step i - step j = x-step j + step i := by abel
    simp only [Exterior.linkSum, posDir, negDir,Step.used,Step.vec,Step.rev,
      Bool.not_false,Bool.not_true, Bool.false_eq_true, ↓reduceIte, add_zero, h₁,
      sub_add_cancel, ← sub_eq_add_neg]
    simp only [add_sub_cancel_right]; abel
  have hs (x : Cover) (i j : Axis) : Exterior.linkSum Y x (square i j) =
      ∑ k ∈ Finset.range (d-1), net (expand d A k) i j (castPos x) 1 := by
    unfold Y; rw [square_sum]; simp_rw [edge_sum,castPos_step, net, partial_eq_diff,
      Finset.sum_sub_distrib]; abel
  change Exterior.linkSum Y _ _ + Exterior.linkSum Y _ _ = _
  rw [he,hz,hs,hs]; rw [Finset.sum_sub_distrib]; abel

-- pull the differentiated wheel back to the base with the chosen transport.
private def spun (e : Edge Cover) (a : Step) (U : CoverConfig G) :=
  toBond e U * wheel e a U * (toBond e U)⁻¹

private lemma spun_germ (H : Hol G) (e : Edge Cover) (a : Step) :
    AnalyticAt ℝ (fun J : Snap G d => G.curvature (spun e a (H.links d (expand d J) 1))) 0 ∧
    ∀ J : Snap G d, HasDerivAt (fun t : ℝ => G.curvature
      (spun e a (H.links d (expand d (t • J)) 1)))
      (Exterior.linkSum (access J) e.1 (oriented (posDir e.2) a)) 0 := by
  let U := fun J : Snap G d => H.links d (expand d J) 1
  let T := fun J : Snap G d => G.mat (toBond e (U J))
  let W := fun J : Snap G d => G.mat (wheel e a (U J))
  let N := fun J : Snap G d => T J * W J * star (T J)
  have hT : AnalyticAt ℝ T 0 := (Work.G02.walkGerm H d _ _).1
  have hW : AnalyticAt ℝ W 0 := (Work.G02.walkGerm H d _ _).1
  let I : G.Mat →L[ℝ] G.Mat := ContinuousLinearMap.id ℝ G.Mat
  let S := (starL' ℝ (A := G.Mat)).toContinuousLinearMap
  let L := G.projectColor.toContinuousLinearMap.comp ((1/2 : ℝ) • (I - S))
  have hN : AnalyticAt ℝ N 0 := (hT.mul hW).mul ((S.analyticAt _).comp hT)
  have hg (J : Snap G d) : G.curvature (spun e a (U J)) = L (N J) := rfl
  change AnalyticAt ℝ (fun J => G.curvature (spun e a (U J))) 0 ∧ _
  constructor
  · simp_rw [hg]; exact (L.analyticAt _).comp hN
  intro A
  let y := Exterior.linkSum (access A) e.1 (oriented (posDir e.2) a)
  let z := Exterior.linkSum (access A) (0:Cover) (route 0 e.1 1)
  have hu : U 0 = 1 := funext fun i => (Work.G02.linkGerm H d i).2.1
  have hT : HasDerivAt (fun t : ℝ => T (t • A)) (G.colorMat z) 0 :=
    (Work.G02.walkGerm H d _ _).2 A
  have hY : HasDerivAt (fun t : ℝ => N (t • A)) (G.colorMat y) 0 := by
    have hW : HasDerivAt (fun t : ℝ => W (t • A)) (G.colorMat y) 0 :=
      (Work.G02.walkGerm H d _ _).2 A
    apply ((hT.mul hW).mul hT.star).congr_deriv
    simp only [G.colorMat_skew,Pi.mul_apply,zero_smul]
    rw [show T 0 = 1 by dsimp only [T]; rw [hu]; simp [toBond,Pressure.one],
      show W 0 = 1 by dsimp only [W]; rw [hu]; simp [wheel,Pressure.one]]
    simp only [one_mul,star_one,mul_one]; abel
  change HasDerivAt (fun t : ℝ => G.curvature (spun e a (U (t • A)))) _ 0
  simp_rw [hg]; refine (L.hasFDerivAt.comp_hasDerivAt 0 hY).congr_deriv ?_
  change G.projectColor ((1/2 : ℝ) • (G.colorMat y-star (G.colorMat y))) = y
  rw [G.colorMat_skew, sub_neg_eq_add, ← two_smul ℝ, smul_smul, div_mul_cancel₀ _ two_ne_zero,
    one_smul,G.project_colorMat]

private lemma sample_parts (e : Edge Cover) (U : CoverConfig G) : sample e U =
    ∑ i : Axis with i ≠ e.2, (G.curvature (spun e (posDir i) U)+
      G.curvature (spun e (negDir i) U)) := by
  unfold sample euler; simp only [spun,map_sum,map_add,G.curvature_conjugate]

/-- The sample itself is analytic in truncated radial data. -/
lemma sample_germ (H : Hol G) (d : ℕ) (e : Edge Cover) :
    AnalyticAt ℝ (fun J : Snap G d => sample e (H.links d (expand d J) 1)) 0 := by
  simp_rw [sample_parts]
  exact Finset.analyticAt_fun_sum _ fun j _ => (spun_germ H e (posDir j)).1.add
    (spun_germ H e (negDir j)).1

private lemma tangent {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (x : F) :
    HasDerivAt (fun t : ℝ => t • x) x 0 := by simpa using! (hasDerivAt_id' (0 : ℝ)).smul_const x

lemma sample_net (H : Hol G) (x : Cover) (i : Axis) (A : Snap G d) : linearSample H (x,i) A =
    ∑ m ∈ Finset.range (d-1), ∑ j : Axis with j≠i, (net (expand d A m) j i (castPos (x-step j)) 1 -
      net (expand d A m) j i (castPos x) 1) := by
  let F := fun t : ℝ => H.links d (expand d (t • A)) 1
  apply (show HasDerivAt (fun t : ℝ => sample (x,i) (F t)) (linearSample H (x,i) A) 0 from
    (sample_germ H d (x,i)).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0
      (tangent A)
      (by simp)).unique
  simp_rw [sample_parts]; rw [Finset.sum_comm]
  refine HasDerivAt.fun_sum fun j _ => ?_
  rw [← linkSum_wheel]; exact ((spun_germ H (x,i) (posDir j)).2 A).add
    ((spun_germ H (x,i) (negDir j)).2 A)

end YM.WardBin
