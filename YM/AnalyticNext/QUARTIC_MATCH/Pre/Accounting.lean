import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.AnalyticNext.QUARTIC_MATCH.Submersion
import YM.Bid.Drops
import YM.Org.Theatre
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06

/-!
# Buying a centered stationary representative with exact tangent

Linear, *B-dependent* local joint gauge penalty. No nonlinear change to the
answer: kills via exact gauge identity, then F04/F05 on the actual slice. All
finite. The Hessian mapping estimates needed pre-L are separate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Pre
open Filter Function Matrix Work.F04 Topology
open scoped Topology ContDiff BigOperators InnerProductSpace
section supplement
variable {X Y Z I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup I] [InnerProductSpace ℝ I]

/-- Enter a prescribed linear horizontal response into the norm penalty. -/
def glance (q : Y→L[ℝ] I) (b : X→L[ℝ] Y) := q ∘L (ContinuousLinearMap.snd ℝ X Y - b ∘L ContinuousLinearMap.fst ℝ X Y)

def soft (f : X × Y→ℝ) (P : X × Y→L[ℝ] I) (z : X × Y) := f z + (1/2:ℝ)*‖P z‖^2

lemma soft_smooth (f : X × Y→ℝ) (P : X × Y→L[ℝ] I) (x : X × Y) (h : ContDiffAt ℝ ω f x) : ContDiffAt ℝ ω (soft f P) x :=
    h.add (contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp _ P.contDiff.contDiffAt))
lemma dollar (f : X × Y→ℝ) (P : X × Y→L[ℝ] I) (x : X × Y) (h : ContDiffAt ℝ ω f x) (w : X × Y) :
    fderiv ℝ (soft f P) x w = fderiv ℝ f x w + inner ℝ (P x) (P w) := by
  have ht : HasFDerivAt (soft f P) _ x :=
    ((h.differentiableAt (by simp)).hasFDerivAt).add ((P.hasFDerivAt (x:=x)).norm_sq.const_mul (1/2:ℝ))
  rw [ht.fderiv]; simp
lemma soft_pair (f : X × Y→ℝ) (P : X × Y→L[ℝ] I) (x : X × Y) (h : ContDiffAt ℝ ω f x) (u v : X × Y) :
    D2 (soft f P) x u v=D2 f x u v + inner ℝ (P u) (P v) := by
  let L : (X × Y)→L[ℝ] ℝ := ((innerSL ℝ) (P v)) ∘L P
  have hg : HasFDerivAt (fun x => fderiv ℝ f x v) _ x := ((h.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)).clm_apply (differentiableAt_const v) |>.hasFDerivAt
  have hk : HasFDerivAt (fun x => fderiv ℝ (soft f P) x v) _ x := (hg.add L.hasFDerivAt).congr_of_eventuallyEq
    ((h.eventually (by simp)).mono fun y (hy : ContDiffAt ℝ ω f y) => (dollar _ _ y hy v).trans (congr_arg (fderiv ℝ f y v + ·) (real_inner_comm ..)))
  change Analysis.D u (fderiv ℝ (soft f P)) x v = _
  rw [← D_left (((soft_smooth f P _ h).fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)), Analysis.D, hk.fderiv, _root_.add_apply]
  have he := D_left (u:=u) ((h.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)) v
  change Analysis.D u (fun y => fderiv ℝ f y v) x+inner ℝ (P v) (P u) = _; rw [he,real_inner_comm]; rfl

lemma can_spend [FiniteDimensional ℝ Z] [FiniteDimensional ℝ I]
    [CompleteSpace I] (U : (X × Y) × Z→Y) (h : ContDiffAt ℝ ω U 0) (q : Y→L[ℝ] I) (b : X→L[ℝ] Y)
    (hp : Surjective (q ∘L vMap U 0)) (hU : ∀ᶠ w in 𝓝 (0:X × Y), U (w,0)=w.2)
    (f : X × Y→ℝ) (hf : ContDiffAt ℝ ω f 0) (he : ∀ᶠ z in 𝓝 0,f (z.1.1,U z)=f z.1) :
    ∀ᶠ z in 𝓝 0, vert (soft f (glance q b)) z=0 → (glance q b z=0 ∧ vert f z=0) := by
  let A := X × Y
  let W := q ∘L vMap U 0
  obtain ⟨T, ht⟩ := LinearMap.exists_rightInverse_of_surjective (f:=W.toLinearMap) (LinearMap.range_eq_top.mpr hp)
  let V := T.toContinuousLinearMap
  let N (x : A) := (q ∘L vMap U (x,0)) ∘L V
  have hN : N 0 = 1 := by apply ContinuousLinearMap.ext; intro u; exact DFunLike.congr_fun ht u
  have hs : ContinuousAt N 0 := (((show ContinuousAt (fun _ : A => q) 0 from continuousAt_const).clm_comp
    ((((h.fderiv_right (m:=ω) (by simp)).continuousAt).comp (f:=fun x : A => (x, (0:Z))) (continuousAt_id.prodMk continuousAt_const)).clm_comp continuousAt_const)).clm_comp continuousAt_const)
  have hw := hs (Units.isOpen.mem_nhds (show IsUnit (N 0) by rw [hN]; exact isUnit_one))
  have hx : ∀ᶠ z in 𝓝 (0:X × Y), vert f (z.1,U (z,0)) ∘L vMap U (z,0)=0 := by
    let g : (X × Y) × Z→ℝ := f ∘ Prod.fst
    have hy : ((0:X),U ((0:X × Y),0)) = 0 := Prod.ext rfl (show U ((0:X × Y),0)=(0:X × Y).2 from (show _ from mem_of_mem_nhds (s:={w : X × Y | U (w,0)=w.2}) hU))
    have hh := vert_pull (P:=g) (Q:=f) (L:=Prod.fst) h contDiffAt_fst (show g =ᶠ[𝓝 0] _ from he.mono fun x hx => hx.symm)
      (show ContDiffAt ℝ ω f ((0:X),U ((0:X × Y),0)) from hy.symm ▸ hf)
    filter_upwards [(show Tendsto (fun x : X × Y => (x,(0:Z))) (𝓝 0) (𝓝 0) from
      (continuous_id.prodMk continuous_const).tendsto _).eventually hh,hf.eventually (by simp)] with z hz ht
    rw [← (show vert g (z,0)=_ from hz)]; ext v
    change fderiv ℝ (f ∘ Prod.fst) (z,(0:Z)) (0,v)=0
    rw [((ht.differentiableAt (by simp)).hasFDerivAt.comp (z,(0:Z)) hasFDerivAt_fst).fderiv]; exact map_zero (fderiv ℝ f z)
  let P := glance q b
  have hP (y : Y) : P (0,y)=q y := by
    change q ((ContinuousLinearMap.snd ℝ X Y - b ∘L ContinuousLinearMap.fst ℝ X Y) (0,y))=_
    simp
  filter_upwards [hx,hU,hf.eventually (by simp),hw] with x hh hy hF hw hz
  change IsUnit (N x) at hw
  have hm (u : Y) : vert f x u + inner ℝ (P x) (q u)=0 := by
    have hv := DFunLike.congr_fun hz u
    change fderiv ℝ (soft f P) x (0,u)=0 at hv
    rw [dollar f P x hF, hP] at hv; exact hv
  let u := hw.unit.inv (P x)
  have hu : N x u = P x := DFunLike.congr_fun (show N x * hw.unit.inv = 1 from (congr_arg (· * hw.unit.inv) hw.unit_spec).symm.trans hw.unit.val_inv) _
  let v := V u
  have he : vert f x (vMap U (x,0) v) = 0 := by rw [hy, Prod.eta] at hh; exact DFunLike.congr_fun hh v
  have he' : P x=0 := inner_self_eq_zero.mp
    (show inner ℝ (P x) (P x)=0 from by
      have h := hm (vMap U (x,0) v); rw [he, zero_add, show q (vMap U (x,0) v)=_ from hu] at h; exact h)
  refine ⟨he',ContinuousLinearMap.ext fun u => ?_⟩
  have h := hm u; rw [he',inner_zero_left, add_zero] at h; exact h

lemma draws [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ I]
    [CompleteSpace I] (U : (X × Y) × Z→Y) (h : ContDiffAt ℝ ω U 0) (q : Y→L[ℝ] I) (b : X→L[ℝ] Y)
    (hp : Surjective (q ∘L vMap U 0)) (hU : ∀ᶠ w in 𝓝 (0:X × Y), U (w,0)=w.2)
    (f : X × Y→ℝ) (hf : ContDiffAt ℝ ω f 0) (he : ∀ᶠ z in 𝓝 0,f (z.1.1,U z)=f z.1)
    (hz : vert f 0=0) (hb : ∀ (u : X) (v : Y), D2 f 0 (u,b u) (0,v)=0)
    (H : ∀ v : Y, v≠0 → 0 < D2 f 0 (0,v) (0,v)+inner ℝ (q v) (q v)) :
    ∃ d : X→Y,d 0=0 ∧ OnShell f d 0 ∧ fderiv ℝ d 0=b ∧ ∀ (u w : X), q (D2 d 0 u w)=0 := by
  let P := glance q b
  let F := soft f P
  have hF := soft_smooth f P 0 hf
  have hD : vert F 0 = 0 := by
    apply ContinuousLinearMap.ext; intro u
    change fderiv ℝ (soft f P) 0 (0,u)=0; rw [dollar _ _ 0 hf,map_zero,inner_zero_left,add_zero]
    exact DFunLike.congr_fun hz u
  let E := vMap (vert F) 0
  have hP (y : Y) : P (0,y)=q y := by
    change q ((ContinuousLinearMap.snd ℝ X Y - b ∘L ContinuousLinearMap.fst ℝ X Y) (0,y))=_
    simp
  have hr : E.IsInvertible := by
    apply form_invertible; apply (injective_iff_map_eq_zero _).2
    intro v hv; by_contra H0
    have ht := DFunLike.congr_fun hv v
    change fderiv ℝ (vert F) 0 (0,v) v=0 at ht
    rw [vert_rate F 0 hF, D2_jet,soft_pair f P 0 hf,hP] at ht
    exact (H v H0).ne' ht
  have hT := vert_smooth F 0 hF
  let d := hT.implicitFunction (by simp) hr
  have hd : d 0=0 := hT.implicitFunction_apply_self (by simp) hr
  have hv : arc d 0=0 := Prod.ext rfl hd
  have ha : OnShell F d 0 := {
    station := (show ∀ᶠ x : X in 𝓝 0,vert F (arc d x)=vert F 0 from
      hT.eventually_apply_implicitFunction (by simp) hr).mono fun _ he => he.trans hD
    path := hT.contDiffAt_implicitFunction (by simp) hr
    action := hv.symm ▸ hF }
  have ht := ha.arc_smooth.continuousAt.tendsto; rw [hv] at ht
  have hs := ha.station.mp (ht.eventually (can_spend U h q b hp hU f hf he))
  refine ⟨d,hd,⟨hs.mono fun _ h => h.2,ha.path,hv.symm ▸ hf⟩,?_,?_⟩
  · apply ContinuousLinearMap.ext; intro u; apply hr.injective
    ext v
    change fderiv ℝ (vert F) 0 (0,fderiv ℝ d 0 u) v=fderiv ℝ (vert F) 0 (0,b u) v
    have hh := ha.flat u v; rw [hv,← D2_jet,← vert_rate F 0 hF] at hh
    have he' : fderiv ℝ (vert F) 0 (u,b u) v=0 := by
      rw [vert_rate F 0 hF,D2_jet, soft_pair f P 0 hf, hb ]
      simp [P,glance]
    have hw (y : Y) : fderiv ℝ (vert F) 0 (u,y) v=fderiv ℝ (vert F) 0 (u,0) v+fderiv ℝ (vert F) 0 (0,y) v := by
      rw [← _root_.add_apply,← map_add]; simp
    change fderiv ℝ (vert F) 0 (u,fderiv ℝ d 0 u) v=0 at hh; rw [hw] at hh he'; linarith
  intro u w
  have hb' : q ∘ d =ᶠ[𝓝 0] ⇑(q ∘L b) := by
    filter_upwards [hs] with z hz
    have he := hz.1; simp only [glance,ContinuousLinearMap.comp_apply,_root_.sub_apply,
      map_sub,sub_eq_zero] at he
    exact he
  rw [← D2_jet]; change q.compContinuousMultilinearMap (iteratedFDeriv ℝ 2 d 0) ![u,w] = 0
  rw [← ContinuousLinearMap.iteratedFDeriv_comp_left q ha.path le_top, (hb'.iteratedFDeriv ℝ 2).eq_of_nhds,D2_jet]
  unfold D2; rw [show fderiv ℝ ⇑(q ∘L b) = fun _ => q ∘L b from funext fun _ => (q ∘L b).fderiv]; simp
end supplement

end YM.AnalyticNext.QuarticMatch.Pre
