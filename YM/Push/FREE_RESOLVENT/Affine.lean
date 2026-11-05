import YM.Push.FREE_RESOLVENT.Flat
import YM.Push.FREE_RESOLVENT.JetWindows
import YM.Work.F02
import YM.Work.F03.Flat


/-!
# A second use of the free inverse: jets of the actual affine precisions

Explicitly define the *no-hole* affine rows of  etc. All tree gauges,
output log fields B, rotation channels and shared prediction choices
specified. Tree projection acts by restricting columns of the full
A right here (not by deleting any plaquette rows at cut or across windows).
These definitions price the **Gram matrices** only, not the F0 or any
physical selection/seed depending on V. Later use the inverse jet arithmetic
from them at zero (flat); not perturbed gaps on arbitrary large fields.
This is separate from the stationary *unmasked action Hessian*: comparison
is of their flat free matrices, not agreement at nonzero field.

Lengths in `Admit` include the actual lifted walk/history (slot length; path
cut before summing to any matrix entry). No dependence on one particular value
of `clip.linear` or `relaxation`. Compute Gram with direct & κ and group
channel weights exactly once. No random resampling when evaluating the germ,
nor covariance assertion on raw paths. Account for both endpoints when
negative orientation used. In particular noise is in its real channel
basis; first use derivative of WHOLE predictor on the oriented edge, not
taking a V adjoint in place of the predictor's. Sign in E row square inherited
from its minus on noise (store positive Q derivative here; multiply by its
transpose, so unchanged). Inputs at fine links are actual relative fields
without a sign-tangent approximation at nonlinear background. All directions
pinned to physical color convention at every differentiation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid TestD Filter
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {n c f : Side} {S : StepData c f} {r : ℕ}

namespace Affine

def decode (v : Vec G n r) : fieldDir G n r := fun b => WithLp.toLp 2 (fun i => component v i b)
lemma decode_flat (x : fieldDir G n r) : decode (flatten x)=x := rfl
lemma flat_decode (v : Vec G n r) : flatten (decode v)=v := rfl

def plain (G : Gauge) (n : Side) (r : ℕ) : Vec G n r ≃L[ℝ] fieldDir G n r := LinearEquiv.toContinuousLinearEquiv ({
  toFun := decode
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := flatten
  left_inv := flat_decode
  right_inv := decode_flat } : Vec G n r ≃ₗ[ℝ] fieldDir G n r)

abbrev pair (G : Gauge) (c f : Side) := Vec G c 1 × Vec G f 1
abbrev raw (G : Gauge) (f : Side) := Slot G f 1
abbrev tile (G : Gauge) (f : Side) := Slot G f 2

def backdrop (S : StepData c f) (B : Vec G c 1) := replica S.ratio (represent (decode B))
def unwrapped (S : StepData c f) (p : pair G c f) := increment (backdrop S p.1) (collect _ (decode p.2))
def rays (S : StepData c f) (s : Signed) (B : pair G c f) := pull s 0 (unwrapped S B)
def shone (S : StepData c f) (s : Signed) (B : Vec G c 1) := pull s 0 (backdrop S B)

def faces (S : StepData c f) (s : Signed) (p : pair G c f) : Vec G f 2 := fun e =>
  G.curvature (faceValue (rays S s p) (e.1,plaqEquiv.symm e.2.1)) e.2.2

/-- d_V response in channel rows; actual relative U increment. -/
def response (S : StepData c f) (s : Signed) (B : Vec G c 1) := LinearMap.toMatrix'
  (fderiv ℝ (fun a => faces S s (B,a)) 0).toLinearMap

def which (q : Body 1 c) : Edge (Site c) := (q.1,axisEquiv.symm q.2)

/-- Right Lie tangent EXPRESSED on group matrices via actual group path
`Q(e^a Vbar) Q(Vbar)⁻¹`, Vbar held. -/
def castNoise (S : StepData c f) (s : Signed) (k : S.Choices) (e : Edge (Site c)) (p : pair G c f) :=
  G.mat (pull s 0 (S.prediction (unwrapped S p) k) e *
    ((pull s 0 (S.prediction (backdrop S p.1) k)) e)⁻¹)

def gaugeQ (S : StepData c f) (s : Signed) (k : S.Choices) (p : pair G c f) : Vec G c 1 :=
  fun i => G.projectColor (castNoise S s k (p := p) (which (i.1,i.2.1))) i.2.2

def duct (S : StepData c f) (s : Signed) (k : S.Choices) (B : Vec G c 1) := LinearMap.toMatrix'
  (fderiv ℝ (fun a => gaugeQ S s k (B,a)) 0).toLinearMap

/-- One ℓ^U transported row before coefficient, in physical matrix entries.
The plaquette is indexed at its actual minimal-site in the channel. -/
def element (U : Config G f) (i j : tile G f) (x : RG.Slot) :=
  if (j.1,j.2.1)=(wrap f x.offset+i.1, plaquette x.plaq) then
    G.adjoint (travel U i.1 x.walk) (EuclideanSpace.basisFun G.ColorIndex ℝ j.2.2) i.2.2
  else 0

abbrev Admit := RG.Slot → Bool

def edgework (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f) (q : ℕ) (B : Vec G c 1) :=
  let p := W.row (plaqEquiv.symm i.2.1) q
  if r p.2 then p.1 * element (shone S s B) i j p.2 else 0

def tracks (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (B : Vec G c 1) : Matrix (tile G f) (tile G f) ℝ :=
  of fun i j => ∑' q, edgework S s W r i j q B

def squareQ {ι ν : Type*} [Fintype ι] (A : Matrix ι ν ℝ) := A.transpose*A

def channel (S : StepData c f) (s : Signed) (k : S.Choices) (p : Clip) (W : PathData G) (r : Admit) (B : Vec G c 1) :=
  p.direct • squareQ (response S s B) + squareQ (tracks S s W r B * response S s B) +
    S.kernel.penalty • squareQ (duct S s k B)

def block (S : StepData c f) (k : S.Choices) (p : Clip) (W : PathData G) (r : Admit) (B : Vec G c 1) :=
  (Fintype.card Signed : ℝ)⁻¹ • (∑ s, channel S s k p W r B)

def primary (S : StepData c f) (T : Forest S.ratio) (k : S.Choices) (p : Clip) (W : PathData G) (r : Admit) (B : Vec G c 1) :=
  (block S k p W r B).submatrix (plant T) (plant T)

section differentiable

@[simp] lemma white (B : Vec G c 1) : unwrapped S (B,0)=backdrop S B := by
  funext i; change G.lieExp 0 * _ = _; rw [G.mat_lieExp_zero,one_mul]
@[simp] lemma back_flat (S : StepData c f) (G : Gauge) : backdrop S (0 : Vec G c 1)=1 := by
  unfold backdrop; rw [show decode _=0 from rfl,Precision.link_one,Precision.replica_one]
@[simp] lemma back_recover (t : ℝ) (a : Vec G f 1) : unwrapped S (0,t • a)=represent (t • decode a) := by
  unfold unwrapped; rw [back_flat]; rfl

lemma background_smooth (S : StepData c f) (e : Edge (Site f)) :
    ContDiff ℝ ω (fun B : Vec G c 1 => G.mat (backdrop S B e)) := by
  unfold backdrop replica; split
  · exact contDiff_const
  exact (Work.F03.represent_smooth (G:=G) _).comp (f:=plain G c 1) (plain G c 1).contDiff

lemma active_smooth (e : Edge (Site f)) : ContDiff ℝ ω (fun b : pair G c f => G.mat (unwrapped S b e)) := by
  simp_rw [unwrapped, increment, collect,G.mat_mul]
  apply ContDiff.mul
  · exact G.exp_jet.comp ((contDiff_apply ℝ G.Color (e.1,coord e.2)).comp (f:=fun x : pair G c f => plain G f 1 x.2)
      ((plain G f 1).contDiff.comp contDiff_snd))
  exact (background_smooth S e).comp (f:=Prod.fst) contDiff_fst

lemma rays_smooth (s : Signed) (e : Edge (Site f)) : ContDiff ℝ ω (fun b : pair G c f => G.mat (rays S s b e)) := by
  unfold rays Lattice.pull Step.read; split
  · simp_rw [G.mat_inv]
    exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (active_smooth _)
  exact active_smooth _

lemma face_smooth (s : Signed) : ContDiff ℝ ω (faces S s (G:=G)) := by
  apply contDiff_pi.mpr; intro e
  simp only [faces, Gauge.curvature,G.mat_inv]
  have he : ContDiff ℝ ω (fun b : pair G c f => G.mat (faceValue (rays S s b) (e.1,plaqEquiv.symm e.2.1))) := by
    rw [contDiff_iff_contDiffAt]; intro b
    change ContDiffAt ℝ ω (fun b => G.mat (travel (rays S s b) _ _)) b
    simp_rw [← Work.F02.stringMat_physical]
    exact ((Work.F02.stringMat_contDiff _ _).restrict_scalars ℝ).contDiffAt.comp b (Work.F02.physical_contDiffAt fun i => (rays_smooth s i).contDiffAt)
  refine (PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) e.2.2).contDiff.comp ?_
  exact G.projectColor.toContinuousLinearMap.contDiff.comp ((he.sub ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp he)).const_smul (1/2:ℝ))

/-- π→ Color slot row tangent matrix on the actual background. -/
lemma face_path (S : StepData c f) (s : Signed) (B : Vec G c 1) (a : Vec G f 1) :
    HasDerivAt (fun v : ℝ => faces S s (B,v • a)) (response S s B *ᵥ a) 0 := by
  rw [response,LinearMap.toMatrix'_mulVec]
  exact Push.side (fun z => faces S s (B,z)) (((face_smooth s).contDiffAt.comp (f:=fun w => (B,w)) 0
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)) a

lemma scope (hb : S.patch.Branches S.kernel G) (k : S.Choices) (e : Edge (Site c)) :
    ContDiffAt ℝ ω (fun b : pair G c f => G.mat (S.prediction (unwrapped S b) k e)) 0 := by
  let L (b : pair G c f) : Dir G f := fun i => G.plog (G.mat (unwrapped S b (i.1,axisEquiv.symm i.2)))
  have hz : unwrapped S (0 : pair G c f)=1 := (white _).trans (back_flat ..)
  have he : L 0 = 0 := funext fun i => by simp [L,hz]
  have hh : ∀ i : Edge (Site f), ∀ᶠ x : pair G c f in 𝓝 0, G.lieExp (G.plog (G.mat (unwrapped S x i)))=unwrapped S x i := by
    intro i
    refine Filter.Tendsto.eventually ?_ G.plog_right
    have ht : ContinuousAt (fun x => unwrapped S x i) (0 : pair G c f) :=
      (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (active_smooth i).continuous.continuousAt.tendsto
    convert! ht.tendsto; rw [hz]; rfl
  apply ContDiffAt.congr_of_eventuallyEq (f:=fun b => G.mat (S.prediction (represent (L b)) k e))
  · apply ContDiffAt.comp (g:=fun y : Dir G f => G.mat (S.prediction (represent y) k e))
    · rw [he]; exact Push.prediction_cont S hb e k
    apply contDiffAt_pi.mpr; intro i
    have he : ContDiffAt ℝ ω G.plog (G.mat (unwrapped S (0:pair G c f) (i.1,axisEquiv.symm i.2))) := by
      rw [hz]; exact G.plog_diff
    exact he.comp (f:=fun b => G.mat (unwrapped S b (i.1,axisEquiv.symm i.2))) (0:pair G c f) (active_smooth _).contDiffAt
  filter_upwards [eventually_all.mpr hh] with x hx
  rw [show represent (L x)=unwrapped S x from funext fun i => by rw [Work.F03.represent_link]; unfold L; rw [←coord_map, axisEquiv.symm_apply_apply]; exact hx i]

lemma scope_out (hb : S.patch.Branches S.kernel G) (s : Signed) (k : S.Choices) (e : Edge (Site c)) :
    ContDiffAt ℝ ω (fun b : pair G c f => G.mat ((pull s 0 (S.prediction (unwrapped S b) k)) e)) 0 := by
  unfold pull Step.read; split
  · simp_rw [G.mat_inv]; exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (scope hb k _)
  exact scope hb k _
lemma cast_smooth (hb : S.patch.Branches S.kernel G) (s : Signed) (k : S.Choices) (e : Edge (Site c)) :
    ContDiffAt ℝ ω (castNoise (G:=G) S s k e) 0 := by
  let F := fun b : pair G c f => G.mat ((pull s 0 (S.prediction (unwrapped S b) k)) e)
  have he : ContDiffAt ℝ ω F 0 := scope_out hb s k e
  have hh : ContDiffAt ℝ ω (fun b : pair G c f => F (b.1,0)) 0 := he.comp (f:=fun b => (b.1,0)) (0:pair G c f) (contDiffAt_fst.prodMk contDiffAt_const)
  rw [show castNoise (G:=G) S s k e = fun b => F b * star (F (b.1,0)) by funext b; simp [castNoise,F]]
  exact he.mul ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ hh)

lemma duct_smooth (hb : S.patch.Branches S.kernel G) (s : Signed) (k : S.Choices) :
    ContDiffAt ℝ ω (gaugeQ (G:=G) S s k) 0 := by
  apply contDiffAt_pi.mpr; intro i
  refine (PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i.2.2).contDiff.contDiffAt.comp _ ?_
  exact G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp _ (cast_smooth hb s k _)

/-- Lifted derivative in the actual color convention near zero equals
right Lie tangent, not its Frobenius projection away. `U = exp^a Vbar`.
Use *any* direction in active slots (in full basis here). -/
lemma duct_path (hb : S.patch.Branches S.kernel G) (s : Signed) (k : S.Choices) :
    ∀ᶠ B : Vec G c 1 in 𝓝 0, ∀ b : Body 1 c, ∀ a : Vec G f 1,
    HasDerivAt (fun v : ℝ => castNoise S s k (which b) (B,v • a)) (G.colorMat (decode (duct S s k B *ᵥ a) b)) 0 := by
  have he : Tendsto (fun B : Vec G c 1 => (B,(0:Vec G f 1))) (𝓝 0) (𝓝 0) := (continuous_id.prodMk (continuous_const (y:=(0:Vec G f 1)))).continuousAt.tendsto
  have hh (e : Edge (Site c)) := he.eventually ((cast_smooth hb s k e).eventually (by simp))
  filter_upwards [he.eventually ((duct_smooth hb s k).eventually (by simp)), eventually_all.mpr hh] with B hB hX
  intro b a
  rw [duct,LinearMap.toMatrix'_mulVec]
  let F (y : Vec G f 1) := castNoise S s k (which b) (B,y)
  let X := fderiv ℝ F 0 a
  have h : HasDerivAt (fun v : ℝ => F (v • a)) X 0 := Push.side F (((hX _).comp (f:=fun y => (B,y)) 0
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)) a
  have hx : X ∈ G.lie := G.tangent_generates (f:=fun v : ℝ => F (v • a)) h (by simp [F,castNoise]) (fun t => ⟨_, rfl⟩)
  have H : HasDerivAt (fun v : ℝ => gaugeQ S s k (B,v • a)) (fderiv ℝ (fun y => gaugeQ S s k (B,y)) 0 a) 0 := Push.side (fun y => gaugeQ S s k (B,y))
    ((hB.comp (f:=fun y => (B,y)) 0 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)) a
  have hl : (plain G c 1) (fderiv ℝ (fun y => gaugeQ S s k (B,y)) 0 a) b = G.projectColor X := by
    apply HasDerivAt.unique (f:=fun v : ℝ => G.projectColor (F (v • a))) (x:=0)
    · exact hasDerivAt_pi.mp ((plain G c 1).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt _ H) b
    exact G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt _ h
  change HasDerivAt _ (G.colorMat ((plain G c 1) (fderiv ℝ (fun y => gaugeQ S s k (B,y)) 0 a) b)) _; erw [hl, G.colorMat_project_self hx]; exact h
end differentiable
end Affine
end YM.FreeResolvent
