import YM.Next.BOUNDARY.Parallel
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.GridCost
import YM.Next.SCHEDULE.Post
import YM.Push.CUTOFF_PROJECTORS.Along



/-!
# Finite positive-link energy gradient

The staple formula with the exact Wilson normalization in the Campaign type.
Use **positive links** as variables. Don't need to assume the torus is large
here; differentiate with multiplicity. The sign on the linearized divergence
leg later will come from this convention (plaquette axis order, left
increments); no β included in this G-field.
-/

set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice Wilson Push.CutoffProjectors RG
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace

namespace Trace
attribute [local instance] Gauge.frobInner
variable {G : Gauge}

lemma skew_pair (c : G.Color) (B : G.Mat) :
    (G.colorMat c * star B).trace.re = - (G.colorMat c * B).trace.re := by
  have he := real_inner_comm B (G.colorMat c)
  change (G.colorMat c * star B).trace.re = (B * star (G.colorMat c)).trace.re at he
  simpa [G.colorMat_skew, Matrix.trace_mul_comm B] using he

lemma variation (c : G.Color) (u : G.El) :
    -(G.colorMat c * G.mat u).trace.re / G.repDim = inner ℝ c (G.curvature u) := by
  let X : G.Mat := (1/2 : ℝ) • (G.mat u - G.mat u⁻¹)
  have he := Submodule.starProjection_inner_eq_zero X _ (G.colorMat_mem c)
  rw [real_inner_comm, inner_sub_right, sub_eq_zero, ← G.colorMat_project] at he
  change inner ℝ _ X = inner ℝ (G.colorIso c) (G.colorIso (G.curvature u)) at he
  rw [G.inner_frob_color] at he
  have hn : 0 < (G.repDim : ℝ) := by exact_mod_cast G.dimPos
  rw [div_eq_iff hn.ne', mul_comm, ← he]; unfold X; rw [real_inner_smul_right, inner_sub_right]
  change _ = _ * ((G.colorMat c * star (G.mat u)).trace.re - (G.colorMat c * star (G.mat u⁻¹)).trace.re)
  rw [skew_pair (G:=G) c, G.mat_inv, star_star]
  ring
end Trace

variable {R : Type*} [AddCommGroup R] [One R] {G : Gauge}

lemma face_word (U : Links R G.El) (x : Four R) (q : PlaqAxes) :
    let i := q.val.1; let j := q.val.2
    faceValue U (x,q) = U (x,i)*U (x+step i,j)*(U (x+step j,i))⁻¹*(U (x,j))⁻¹ := by
  dsimp only
  simp only [faceValue,square,travel,Step.pos_read,Step.neg_read,Step.vec_pos,Step.vec_neg,mul_one,mul_assoc]
  rw [show x+step q.val.1+step q.val.2-step q.val.1=x+step q.val.2 by abel,
    show x+step q.val.1+step q.val.2+-step q.val.1-step q.val.2=x by abel]

/-- The plaquette loops transported to the point of insertion at the *positive* link base. -/
def cornerB (U : Links R G.El) (x : Four R) (q : PlaqAxes) :=
    let a := U (x,q.val.1)
    a⁻¹ * faceValue U (x,q) * a

def cornerC (U : Links R G.El) (x : Four R) (q : PlaqAxes) :=
    let a := U (x,q.val.2)
    a⁻¹ * faceValue U (x,q) * a

section Price4
omit [AddCommGroup R] [One R]
lemma four_price {A B C D : ℝ → G.El} {a b c d : G.Color}
    (ha : HasDerivAt (fun t => G.mat (A t)) (G.colorMat a * G.mat (A 0)) (0:ℝ))
    (hb : HasDerivAt (fun t => G.mat (B t)) (G.colorMat b * G.mat (B 0)) (0:ℝ))
    (hc : HasDerivAt (fun t => G.mat (C t)) (G.colorMat c * G.mat (C 0)) (0:ℝ))
    (hd : HasDerivAt (fun t => G.mat (D t)) (G.colorMat d * G.mat (D 0)) (0:ℝ)) :
    let Y := A 0*B 0*(C 0)⁻¹*(D 0)⁻¹
    HasDerivAt (fun t => G.price (A t*B t*(C t)⁻¹*(D t)⁻¹))
      (inner ℝ a (G.curvature Y) + inner ℝ b (G.curvature ((A 0)⁻¹*Y*A 0)) -
       inner ℝ c (G.curvature ((D 0)⁻¹*Y*D 0)) - inner ℝ d (G.curvature Y)) (0:ℝ) := by
  let L : G.Mat →L[ℝ] ℝ := Complex.reCLM.comp (Matrix.traceLinearMap _ ℝ ℂ).toContinuousLinearMap
  have H := (((ha.mul hb).mul hc.star).mul hd.star)
  have T := HasDerivAt.const_sub 1 ((L.hasFDerivAt.comp_hasDerivAt (0:ℝ) H).div_const (G.repDim : ℝ))
  simp only [Gauge.price, G.mat_mul, G.mat_inv]
  apply T.congr_deriv
  let α := G.mat (A 0); let γ := star (G.mat (C 0)); let η := star (G.mat (D 0)); let τ := G.mat (B 0)
  have ec : star (G.colorMat c * G.mat (C 0)) = - (γ * G.colorMat c) := by rw [star_mul,G.colorMat_skew,mul_neg]
  have ed : star (G.colorMat d * G.mat (D 0)) = - (η * G.colorMat d) := by rw [star_mul,G.colorMat_skew,mul_neg]
  let ea := G.colorMat a; let eb := G.colorMat b; let eg := G.colorMat c; let eh := G.colorMat d
  let Y := A 0*B 0*(C 0)⁻¹*(D 0)⁻¹
  have hY : G.mat Y = α*τ*γ*η := by simp [Y,α,τ,γ,η]
  have hb' : G.mat ((A 0)⁻¹*Y*A 0)=τ*γ*η*α := by simp [Y,τ,γ,η,α,mul_assoc]
  have hc' : G.mat ((D 0)⁻¹*Y*D 0)=η*α*τ*γ := by simp [Y,η,α,τ,γ,mul_assoc]
  rw [← Trace.variation (G:=G) a Y, ← Trace.variation (G:=G) b _, ← Trace.variation (G:=G) c _, ← Trace.variation (G:=G) d _,
    hb',hc',hY]
  simp only [ec,ed, Pi.mul_apply]
  change -(( (( (ea*α*τ+α*(eb*τ))*γ+α*τ*(-(γ*eg)))*η + α*τ*γ*(-(η*eh)) ).trace.re) / _) = _
  have tr (X Y : G.Mat) := Matrix.trace_mul_comm X Y
  simp only [add_mul,mul_neg, neg_mul, Matrix.trace_add,Matrix.trace_neg,Complex.add_re,Complex.neg_re]
  have hb'' : (α * (eb * τ) * γ * η).trace = (eb*(τ*γ*η*α)).trace := by
    rw [mul_assoc,mul_assoc,tr α]; simp only [mul_assoc]
  have hc'' : (α * τ * (γ * eg) * η).trace = (eg*(η*α*τ*γ)).trace := by
    conv_lhs => rw [← mul_assoc (α*τ),mul_assoc,tr _ (eg*η)]
    simp only [mul_assoc]
  have hd'' : (α*τ*γ*(η*eh)).trace=(eh*(α*τ*γ*η)).trace := by rw [← mul_assoc,tr]
  rw [hb'', hc'', hd'']; simp only [mul_assoc]; unfold ea eb eg eh; ring
end Price4

/-- Gradient contributions to the edge at x, reindex lower face base by incidence. -/
def staple (U : Links R G.El) (ν : Axis) (x : Four R) (q : PlaqAxes) : G.Color :=
    (if q.val.1=ν then G.curvature (faceValue U (x,q)) - G.curvature (cornerC U (x-step q.val.2) q) else 0) +
    (if q.val.2=ν then G.curvature (cornerB U (x-step q.val.1) q) - G.curvature (faceValue U (x,q)) else 0)

def gradient (U : Links R G.El) (x : Four R) (ν : Axis) := ∑ q : PlaqAxes, staple U ν x q

variable {n : Side}

def oneEdge (e : Edge (Site n)) (v : G.Color) : Directions G n := Pi.single e v

lemma link_step (U : Config G n) (A : Directions G n) (e : Edge (Site n)) :
    HasDerivAt (fun t : ℝ => G.mat (increment U (t • A) e)) (G.colorMat (A e) * G.mat (U e)) 0 := by
  simp only [increment, G.mat_mul, Pi.smul_apply, G.mat_lieExp, map_smul]
  simpa using! ((hasDerivAt_exp_smul_const (G.colorMat (A e)) (0:ℝ)).mul_const (G.mat (U e)))

lemma price_step (U : Config G n) (A : Directions G n) (p : Face (Per n)) :
    let x := p.1; let q := p.2; let i := q.val.1; let j := q.val.2
    HasDerivAt (fun t : ℝ => G.price (faceValue (increment U (t • A)) p))
      (inner ℝ (A (x,i)) (G.curvature (faceValue U p)) + inner ℝ (A (x+step i,j)) (G.curvature (cornerB U x q)) -
       inner ℝ (A (x+step j,i)) (G.curvature (cornerC U x q)) - inner ℝ (A (x,j)) (G.curvature (faceValue U p))) 0 := by
  rcases p with ⟨x,q⟩
  simp_rw [cornerB,cornerC,face_word]
  refine four_price (a:=A (x,q.val.1)) (b:=A (x+step q.val.1,q.val.2)) (c:=A (x+step q.val.2,q.val.1)) (d:=A (x,q.val.2)) ?_ ?_ ?_ ?_ |>.congr_deriv ?_
  · simpa only [zero_smul,Work.G07.at_zero_increment] using link_step U A (x,q.val.1)
  · simpa only [zero_smul,Work.G07.at_zero_increment] using link_step U A (x+step q.val.1,q.val.2)
  · simpa only [zero_smul,Work.G07.at_zero_increment] using link_step U A (x+step q.val.2,q.val.1)
  · simpa only [zero_smul,Work.G07.at_zero_increment] using link_step U A (x,q.val.2)
  simp only [zero_smul,Work.G07.at_zero_increment]

private lemma find_site (y b : Site n) (ν i : Axis) (c : G.Color) (Y : Site n → G.Color) :
    ∑ x, inner ℝ (oneEdge (y,ν) c (x+b,i)) (Y x) =
      if i=ν then inner ℝ c (Y (y-b)) else 0 := by
  by_cases h : i=ν
  · subst i
    have he (x : Site n) : inner ℝ (oneEdge (y,ν) c (x+b,ν)) (Y x) = if x=y-b then inner ℝ c (Y x) else 0 := by
      have : x+b=y ↔ x=y-b := eq_sub_iff_add_eq.symm
      unfold oneEdge; rw [Pi.single_apply]; by_cases hh : x=y-b <;> simp [Prod.ext_iff,this,hh]
    simp_rw [he]
    simp
  simp_rw [oneEdge, Pi.single_apply]
  simp [Prod.ext_iff,h]

lemma energy_step (U : Config G n) (x : Site n) (ν : Axis) (c : G.Color) :
    HasDerivAt (fun t : ℝ => energy (increment U (t • oneEdge (x,ν) c)))
      (inner ℝ c (gradient U x ν)) 0 := by
  change HasDerivAt (fun t : ℝ => ∑ p, (fun u : ℝ => G.price (faceValue (increment U (u • oneEdge (x,ν) c)) p)) t) _ _
  apply (HasDerivAt.fun_sum (sums U x ν c)).congr_deriv
  simp only [Fintype.sum_prod_type, gradient, inner_sum]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  let i := q.val.1; let j := q.val.2
  have he a : ∑ y : Site n, inner ℝ (oneEdge (x,ν) c (y,a)) (G.curvature (faceValue U (y,q))) =
      if a=ν then inner ℝ c (G.curvature (faceValue U (x,q))) else 0 := by
    simpa using find_site x 0 ν a c (fun y => G.curvature (faceValue U (y,q)))
  rw [he,he,find_site x (step i) ν j c (fun y => G.curvature (cornerB U y q)),
      find_site x (step j) ν i c (fun y => G.curvature (cornerC U y q))]
  unfold staple
  split_ifs <;> simp_all [inner_sub_right,i,j]; abel
where sums (V : Config G n) (X : Site n) (a : Axis) (d : G.Color) : ∀ p : Face (Per n), p ∈ Finset.univ →
        HasDerivAt (fun t : ℝ => G.price (faceValue (increment V (t • oneEdge (X,a) d)) p))
          (inner ℝ (oneEdge (X,a) d (p.1,p.2.val.1)) (G.curvature (faceValue V p)) +
           inner ℝ (oneEdge (X,a) d (p.1+step p.2.val.1,p.2.val.2)) (G.curvature (cornerB V p.1 p.2)) -
           inner ℝ (oneEdge (X,a) d (p.1+step p.2.val.2,p.2.val.1)) (G.curvature (cornerC V p.1 p.2)) -
           inner ℝ (oneEdge (X,a) d (p.1,p.2.val.2)) (G.curvature (faceValue V p))) 0 :=
        fun _ _ => price_step ..

abbrev colors (G : Gauge) := EuclideanSpace.basisFun G.ColorIndex ℝ

theorem packet_energy (U : Config G n) (e : Edge (Site n)) (j : G.ColorIndex) :
    Packet.derivative energy e j U = inner ℝ (colors G j) (gradient U e.1 e.2) := (energy_step ..).deriv

/-- Unwrap energy readings at sample links. -/
@[simp] theorem cornerB_at (U : Config G n) (o : Site n) (x : Cover) (q : PlaqAxes) :
    cornerB (expandAt o U) x q = cornerB U (wrap n x+o) q := by
  simp only [cornerB, faceValue, travel_at]; rfl

@[simp] theorem cornerC_at (U : Config G n) (o : Site n) (x : Cover) (q : PlaqAxes) :
    cornerC (expandAt o U) x q = cornerC U (wrap n x+o) q := by
  simp only [cornerC, faceValue, travel_at]; rfl

lemma gradient_at (U : Config G n) (o : Site n) (x : Cover) (ν : Axis) :
    gradient (expandAt o U) x ν = gradient U (wrap n x+o) ν := by
  simp [gradient,staple,faceValue,travel_at,sub_add_eq_add_sub]

@[simp] lemma cornerB_gauge (U : Links R G.El) (t : Four R → G.El) (x : Four R) (q : PlaqAxes) :
    cornerB (gauge t U) x q = t (x+step q.val.1) * cornerB U x q * (t (x+step q.val.1))⁻¹ := by
  unfold cornerB; rw [face_gauge]; unfold Lattice.gauge; dsimp
  group

@[simp] lemma cornerC_gauge (U : Links R G.El) (t : Four R → G.El) (x : Four R) (q : PlaqAxes) :
    cornerC (gauge t U) x q = t (x+step q.val.2) * cornerC U x q * (t (x+step q.val.2))⁻¹ := by
  -- rewrite gauge on face before unfolding component
  unfold cornerC
  rw [face_gauge]
  unfold Lattice.gauge
  dsimp
  group

lemma gradient_gauge (U : Links R G.El) (t : Four R → G.El) (x : Four R) (ν : Axis) :
    gradient (gauge t U) x ν = G.adjoint (t x) (gradient U x ν) := by
  unfold gradient
  rw [_root_.map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [staple,face_gauge,cornerB_gauge,cornerC_gauge,sub_add_cancel,G.curvature_conjugate]
  split_ifs <;> simp

end YM.ProjectorNext.Calibration
