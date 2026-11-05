import YM.Push.FREE_RESOLVENT.Affine
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.LocalJet


/-!
Actual at V(B) with exact B (can also use B=0, or local axial chart
extensions if separately certified on the required entries), stencils
not reselected. Fcl colors are physical normalized. Noise requires care:

* SectorChange uses EACH oriented bond response of curvature of the
  predictor *multiplied by the inverse of the predictor at this field*.
  FR uses a projection on MATRICES at that same normalization after
  turning the whole predictor. It's the same skew-projection on these
  functions (prove). Reverse leg Q tangent paid *using Q*, not a
  V-based inversion.
* FR uses `fderiv` of one Pi of all those noise coordinates; Sector
  uses individual fderivs. Lean defaults fderiv to zero in failure
  cases: equating these without joint differentiability would be
  spurious. Deliver also a row-first matrix variant valid on arbitrary
  fields in these coordinates, and a genuine JOINT-differentiable
  coupon near zero for comparisons with FR, not on all coarse fields.
  Can request coincidence on more general permitted sets but must pay
  that input (or restrict columns).

No path power or cutoff estimates here beyond PathData.Bounds on this
SAME T.up. Uses `shots` dependency and Authorized work implicitly for
licenses, but do not bound likelihoods with this agreement.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Bid Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Oriented 
open Next SectorChange SectorChange.Rows SectorChange.Gaussian 
open FreeResolvent
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {x : ℝ}

namespace Assembly
-- do in a local Frob context
section skew
attribute [local instance] Gauge.frobInner
lemma starProjection_test (G : Gauge) (A : G.Mat) : G.projectColor (star A) = -G.projectColor A := by
  suffices h : G.lie.starProjection (star A) = -G.lie.starProjection A from
    G.colorMat_injective (by rw [G.colorMat_project,map_neg,G.colorMat_project,h])
  let B := star A+A
  have he (u : G.Mat) (hu : u ∈ G.lie) : inner ℝ u B=0 := by
    have hs : star u= -u := G.generates_skew hu
    change (u * star B).trace.re=0
    rw [show star B=B from (by unfold B; simp [add_comm])]
    have hr : ((u * B).trace).re = ((B * u).trace).re := congr_arg _ (Matrix.trace_mul_comm u B)
    have hx (b : G.Mat) : b.trace.re = (star b).trace.re := by
      rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]; rfl
    have ht : (u * B).trace.re = -(u * B).trace.re := by
      nth_rw 1 [hx,star_mul,hs,show star B=B from (by unfold B; simp [add_comm]),mul_neg, Matrix.trace_neg,Complex.neg_re, ← Matrix.trace_mul_comm u B]
    linarith
  let C := G.lie.starProjection B
  have hmem (v) : G.lie.starProjection v ∈ G.lie := G.lie.orthogonalProjectionOnto v |>.property
  have hCC : inner ℝ C C = 0 := by
    suffices inner ℝ C C = inner ℝ C B by rw [this]; exact he C (hmem _)
    nth_rw 2 [show C=G.lie.starProjection B from rfl]
    rw [← Submodule.inner_starProjection_left_eq_right,G.lie.starProjection_eq_self_iff.mpr (hmem _)]
  have hC : C=0 := inner_self_eq_zero.mp hCC
  unfold C B at hC; rw [map_add] at hC
  exact eq_neg_of_add_eq_zero_left hC
lemma curvature_pay (u : G.El) : G.curvature u=G.projectColor (G.mat u) := by
  unfold Gauge.curvature
  rw [map_smul,map_sub,G.mat_inv,starProjection_test]; module
end skew

/-- B is the FR background in coarse physical counting colors. -/
abbrev Coarse (G : Gauge) (c : Side) := FreeResolvent.Vec G c 1
abbrev Warm (G : Gauge) (n : Side) := FreeResolvent.Vec G n 1

def enroll (B : Coarse G n) : Config G n := Precision.represent (Affine.decode B)



/-! One direct E row (matrix representation on all fine and receiving
slots). fresh will insert later. Use SectorChange even off a smooth
branch; this gives FR-compatible *row-first* convention instead of
silently pretending entirety of duct is differentiable on all fields.
-/
section
variable (S : StepData c f) (B : Coarse G c) (s : Signed) (k : S.Choices)
def actual (v : Warm G f) : Directions G f := Exterior.collect G (Affine.decode v)

def actualCount (G : Gauge) (f : Side) : Warm G f ≃L[ℝ] Directions G f := (LinearEquiv.toContinuousLinearEquiv {
  toFun := actual
  invFun := fun a => FreeResolvent.flatten (SectorChange.Flat.labels a)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  left_inv := by
    intro v; funext x; rcases x with ⟨i,b,j⟩
    change v (i,coord (axisEquiv.symm b),j) = _
    rw [show coord (axisEquiv.symm b)=b from axisEquiv.apply_symm_apply _]
  right_inv := SectorChange.Flat.collected })

def oldFace (e : Cell f) (v : Warm G f) := plaquetteJet S (enroll B) s e (actual v)
def oldNoise (e : Bond c) (v : Warm G f) := blockJet (enroll B) k s e (actual v)
def individualMap : Warm G f →ₗ[ℝ] Warm G c := LinearMap.pi (fun i =>
  ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i.2.2).toLinearMap.comp
    ((blockJet (enroll B) k s (Affine.which (i.1,i.2.1))).toLinearMap.comp (actualCount G f).toLinearMap)))

def individual : Matrix (Affine.raw G c) (Affine.raw G f) ℝ := LinearMap.toMatrix' (individualMap S B s k)

lemma individual_read (v : Warm G f) (e : Bond c) :
    (Affine.decode (individual S B s k *ᵥ v)) (pole e) = oldNoise S B s k e v := by
  rw [individual,LinearMap.toMatrix'_mulVec]
  ext i
  change (blockJet (enroll B) k s (Affine.which (e.1,coord e.2)) _) _ = _
  rw [show Affine.which (e.1,coord e.2)=e from (by unfold Affine.which; rw [show axisEquiv.symm (coord e.2)=e.2 from axisEquiv.symm_apply_apply _])]; rfl

/-- On an analytic branch (or any actual differentiable germ).
Independent of group projection comparison, always smooth here. -/
lemma respond (v : Warm G f) (p : Cell f) :
    Affine.decode (Affine.response S s B *ᵥ v) (p.1,plaquette p.2) = oldFace S B s p v := by
  let U := pull s 0 (replica S.ratio (enroll B))
  have ht := YM.Push.side (fun a => G.curvature (faceValue (facade S s (enroll B) a) p))
    (((SectorChange.Motion.plaquette_turn (S:=S) s (enroll B) p (LocalJet.face_smooth U p).contDiffAt).1).differentiableAt (by simp)) (actual v)
  have hh := (Affine.plain G f 2).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (Affine.face_path S s B v)
  have hy := hasDerivAt_pi.mp hh (p.1,plaquette p.2)
  apply HasDerivAt.unique (f:=fun t : ℝ => G.curvature (faceValue (facade S s (enroll B) (t • actual v)) p)) (x:=0) _ ht
  change HasDerivAt _ ((Affine.plain G f 2) _ _) 0
  convert! hy using 1
  funext t; ext i
  change _ = G.curvature (faceValue (Affine.rays S s (B,t • v)) (p.1,plaqEquiv.symm (plaquette p.2))) i
  rw [show plaqEquiv.symm (plaquette p.2)=p.2 from plaqEquiv.symm_apply_apply _,Prod.mk.eta]
  have hx : Affine.rays S s (B,t • v)=facade S s (enroll B) (t • actual v) := rfl
  rw [hx]

/-- Nondefault choices inserted on the same arguments (incl negative
orientation rule), then the exact curvature normalization. Hold regardless
of smoothness. -/
lemma same_value (h : S.patch.Branches S.kernel G) (v : Warm G f) (i : Affine.raw G c) :
    Affine.gaugeQ S s k (B,v) i = G.curvature (predictorTurn (enroll B) k s (Affine.which (i.1,i.2.1)) (actual v)) i.2.2 := by
  let j := Affine.which (i.1,i.2.1); let V := enroll B
  have he w : predictGroup (enroll B) k s j (actual w)=pull s 0 (S.prediction (Affine.unwrapped S (B,w)) k) j := by
    unfold predictGroup facade
    rw [(carry s h k _).2]; rfl
  unfold Affine.gaugeQ; rw [predictorTurn,he,show (0:Directions G f)=actual (0:Warm G f) from rfl,he,Affine.white,curvature_pay]; rfl

/-- A tempting hypothesis would be only that each selected expression
reading a change after acting on a contains a valid fderiv. That is *not*
what FR uses; give the exact joint premise (paid below near zero, also when
all entries are simultaneously in a genuine permitted neighborhood).
-/
theorem collective (h : S.patch.Branches S.kernel G) (H : DifferentiableAt ℝ (fun v : Warm G f => Affine.gaugeQ S s k (B,v)) 0) :
    Affine.duct S s k B=individual S B s k := by
  rw [Affine.duct, individual]
  apply congr_arg; apply LinearMap.ext; intro v; funext i
  let j := Affine.which (i.1,i.2.1)
  let L (y : Directions G f) := G.curvature (predictorTurn (enroll B) k s j y)
  let T : Warm G c →L[ℝ] G.Color := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Pressure.Bond c => G.Color) j).comp (actualCount G c).toContinuousLinearMap
  let V0 := fun v : Warm G f => Affine.gaugeQ S s k (B,v)
  have H0 : L=(fun w => T (V0 ((actualCount G f).symm w))) := by
    funext w; ext a
    change L w a=V0 ((actualCount G f).symm w) (j.1,coord j.2,a)
    unfold V0; rw [same_value S B s k h]
    have hx : Affine.which (j.1,coord j.2)=j := by
      unfold Affine.which; rw [show axisEquiv.symm (coord j.2)=j.2 from axisEquiv.symm_apply_apply _]
    have hh : actual ((actualCount G f).symm w) = w := (actualCount G f).apply_symm_apply _
    change _ = G.curvature (predictorTurn (enroll B) k s (Affine.which (j.1,coord j.2)) _) a
    rw [hx,hh]
  have hl : DifferentiableAt ℝ L 0 := by
    rw [H0]
    have hh : DifferentiableAt ℝ V0 ((actualCount G f).symm 0) := by simpa only [map_zero] using H
    exact T.differentiableAt.comp _ (hh.comp _ (actualCount G f).symm.differentiableAt)
  let U : G.Color →L[ℝ] ℝ := PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i.2.2
  let X := fun v : Warm G f => (actualCount G f) v
  have hf : HasFDerivAt (fun a => U (L ((actualCount G f) a)))
      (U.comp ((fderiv ℝ L 0).comp (actualCount G f).toContinuousLinearMap)) 0 := by
    refine U.hasFDerivAt.comp _ (HasFDerivAt.comp _ (show HasFDerivAt L _ ((actualCount G f) 0) from ?_) (actualCount G f).hasFDerivAt)
    rw [map_zero]; exact hl.hasFDerivAt
  have ht := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Affine.raw G c => ℝ) i).hasFDerivAt.comp 0 H.hasFDerivAt
  have hy : (fun y : Warm G f => V0 y i)=(fun a => U (L ((actualCount G f) a))) := funext fun a => same_value S B s k h a i
  rw [← hy] at hf
  exact congr_arg (fun F : Warm G f →L[ℝ] ℝ => F v) (ht.unique hf)

/-- Supply the joint premise on a neighborhood of zero for all k,s
(FR fundamental use; B-axis variable but linearization over *fine* v
at each such B). -/
theorem near_collective (S : StepData c f) (h : S.patch.Branches S.kernel G) :
    ∀ᶠ B : Coarse G c in 𝓝 0, ∀ (k : S.Choices) (s : Signed), Affine.duct S s k B=individual S B s k := by
  have ht : Tendsto (fun B : Coarse G c => (B,(0:Warm G f))) (𝓝 0) (𝓝 0) := (continuous_id.prodMk (continuous_const (y:=(0:Warm G f)))).continuousAt.tendsto
  have hz (k s) : ∀ᶠ B : Coarse G c in 𝓝 0, DifferentiableAt ℝ (fun v : Warm G f => Affine.gaugeQ S s k (B,v)) 0 := by
    filter_upwards [ht.eventually ((Affine.duct_smooth (G:=G) h s k).eventually (by simp))] with B he
    exact (he.comp (f:=fun v : Warm G f => (B,v)) 0 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  simp_rw [← eventually_all] at hz
  filter_upwards [hz] with B H k s
  exact collective S B s k h (H k s)
end
end Assembly
end YM.AnalyticBridge.LocalGaussianLaws
