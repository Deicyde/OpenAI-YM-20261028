import YM.AnalyticNext.QUARTIC_MATCH.Exchange

/-!
# Comparing critical germs on a product with redundant vertical variables

Genuine neighborhoods, not just raywise critical points; use also when enlarging periods.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch
open Filter Function Work.F04 Topology
open scoped Topology BigOperators ContDiff

variable {X Y Z E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev vMap (p : X × Z → Y) (z : X × Z) :=
    fderiv ℝ p z ∘L ContinuousLinearMap.inr ℝ X Z

theorem upright_apply {L : X → Y} {p : X × Z → E} {x : X} {z : Z} (hp : DifferentiableAt ℝ p (x,z))
    (hL : DifferentiableAt ℝ L x) (u : Z) :
    fderiv ℝ (fun a : X × Z => (L a.1,p a)) (x,z) (0,u) = (0,vMap p (x,z) u) := by
  change (fderiv ℝ (fun a : X × Z => ((L ∘ Prod.fst) a, p a)) (x,z)) (0,u) = _
  rw [(((hL.hasFDerivAt.comp (x,z) hasFDerivAt_fst)).prodMk hp.hasFDerivAt).fderiv]
  exact Prod.ext (map_zero (fderiv ℝ L x)) rfl

/-- If a fiber map has a smooth section germ, its vertical derivative stays
surjective. Only need the section at the base value of `x`. -/
theorem vMap_surjective [CompleteSpace Y] {p : X × Z → Y}
    (hp : ContDiffAt ℝ ω p 0) {T : Y → Z} (hs : DifferentiableAt ℝ T 0) (hT : T 0=0)
    (he : (fun y => p (0,T y)) =ᶠ[𝓝 0] id) :
    ∀ᶠ z in 𝓝 0, Surjective (vMap p z) := by
  let L := fderiv ℝ T 0
  let N (z : X × Z) := vMap p z ∘L L
  have hz : N 0=1 := by
    let A := fun y => ((0:X),T y)
    have ha : HasFDerivAt A (ContinuousLinearMap.inr ℝ X Z ∘L L) 0 :=
      ((ContinuousLinearMap.inr ℝ X Z).hasFDerivAt).comp 0 hs.hasFDerivAt
    have hA : A 0 = 0 := Prod.ext rfl hT
    have hP := hp.differentiableAt (by simp)
    have hu : HasFDerivAt p (fderiv ℝ p 0) (A 0) := hA.symm ▸ hP.hasFDerivAt
    exact (hu.comp (0:Y) ha).unique ((hasFDerivAt_id (𝕜:=ℝ) (0:Y)).congr_of_eventuallyEq he)
  have hc : ContinuousAt N 0 :=
    (((hp.fderiv_right (m:=ω) (by simp)).continuousAt.clm_comp continuousAt_const).clm_comp continuousAt_const)
  have hi : ∀ᶠ z in 𝓝 0, IsUnit (N z) := hc (Units.isOpen.mem_nhds (show IsUnit (N 0) by rw [hz]; exact isUnit_one))
  filter_upwards [hi] with z ih y
  refine ⟨L (ih.unit.inv y),?_⟩
  change N z (ih.unit.inv y)=y
  exact DFunLike.congr_fun (show N z * ih.unit.inv = 1 from (congr_arg (· * ih.unit.inv) ih.unit_spec).symm.trans ih.unit.val_inv) y

theorem vert_pull {P : X × Y → ℝ} {Q : E × Z → ℝ} {L : X → E} {p : X × Y → Z}
    (hp : ContDiffAt ℝ ω p 0) (hL : ContDiffAt ℝ ω L 0) (he : P =ᶠ[𝓝 0] Q ∘ (fun z => (L z.1,p z)))
    (hQ : ContDiffAt ℝ ω Q (L 0,p 0)) :
    ∀ᶠ w : X × Y in 𝓝 0, vert P w = vert Q (L w.1,p w) ∘L vMap p w := by
  let U (w : X × Y) := (L w.1,p w)
  have hv : ContDiffAt ℝ ω U 0 := (hL.comp (f:=Prod.fst) 0 contDiffAt_fst).prodMk hp
  filter_upwards [he.fderiv (𝕜:=ℝ), hp.eventually (by simp),
    (continuous_fst.tendsto (0:X × Y)).eventually (hL.eventually (by simp)),
    hv.eventually (by simp), hv.continuousAt.tendsto.eventually (hQ.eventually (by simp))]
    with w hw ha hl hb hc
  change fderiv ℝ P w=fderiv ℝ (Q ∘ U) w at hw
  ext v
  change fderiv ℝ P w (0,v)=fderiv ℝ Q _ (0,vMap p w v)
  rw [hw, fderiv_comp w (hc.differentiableAt (by simp)) (hb.differentiableAt (by simp))]
  change fderiv ℝ Q _ (fderiv ℝ U w (0,v))=_
  exact congr_arg (fderiv ℝ Q _) (upright_apply (ha.differentiableAt (by simp))
    (show DifferentiableAt ℝ L w.1 from (show ContDiffAt ℝ ω L w.1 from hl).differentiableAt (by simp)) v)

/-- Lift to a zero-based graph. Equality of actual real values on a neighborhood,
   not a measure or period claim. -/
theorem ascend {P : X × Y → ℝ} {Q : X × Z → ℝ} {p : X × Y → Z}
    {c : X → Y} {b : X → Z} (hP : ContDiffAt ℝ ω P 0) (hb : OnShell Q b 0)
    (h0 : b 0=0) (hp : ContDiffAt ℝ ω p 0) (he : P =ᶠ[𝓝 0] Q ∘ (fun z => (z.1,p z)))
    (hc : c 0=0) (hs : ContDiffAt ℝ ω c 0)
    (hd : p ∘ arc c =ᶠ[𝓝 0] b) :
    OnShell P c 0 ∧ P ∘ arc c =ᶠ[𝓝 0] Q ∘ arc b := by
  have hu : arc c 0 = 0 := Prod.ext rfl hc
  have hz : p 0 = 0 := (congr_arg p hu).symm.trans (hd.self_of_nhds.trans h0)
  have hh := vert_pull (L:=id) hp contDiffAt_id he (show ContDiffAt ℝ ω Q _ from by
    simpa only [arc,hz,h0,id_eq] using hb.action)
  have ht : Tendsto (arc c) (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt (arc c) 0 := continuousAt_id.prodMk hs.continuousAt
    rw [← hu]; exact h
  refine ⟨⟨?_,hs,hu.symm ▸ hP⟩,?_⟩
  · filter_upwards [ht.eventually hh, hd,hb.station] with x hx hg hw
    change p (arc c x) = b x at hg
    change vert Q (x,b x)=0 at hw
    change vert P (arc c x)=_
    rw [hx,hg,show id (arc c x).1=x from rfl,hw,ContinuousLinearMap.zero_comp]
  filter_upwards [ht.eventually he,hd] with x hx hg
  exact hx.trans (congr_arg (fun y => Q (x,y)) hg)

/-- With nonsingular vertical partial derivative of the equation at the
basepoint, ANY nearby root at ANY input agrees with the given graph. -/
theorem near_root [CompleteSpace X] [CompleteSpace Y] {P : X × Y → ℝ}
    {b : X → Y} (hb : OnShell P b 0) (hz : b 0=0)
    (hD : (vMap (vert P) 0).IsInvertible) :
    ∀ᶠ z : X × Y in 𝓝 0, vert P z=0 → z.2=b z.1 := by
  have hp : arc b 0 = 0 := Prod.ext rfl hz
  have hh : vert P 0 = 0 := by
    have hx : vert P (arc b 0)=0 := hb.station.self_of_nhds
    rwa [hp] at hx
  have hg : Tendsto (arc b) (𝓝 0) (𝓝 0) := by
    have h := hb.arc_smooth.continuousAt.tendsto; rwa [hp] at h
  have hP := vert_smooth P 0 (hp ▸ hb.action)
  have he := hP.eventually_apply_eq_iff_implicitFunction (by simp) hD
  have hv := (continuous_fst.tendsto (0:X × Y))
  filter_upwards [he, hv.eventually (hg.eventually he), hv.eventually hb.station] with z h1 h2 h3 hr
  have h4 : vert P (arc b z.1) = 0 := h3
  exact (h1.mp (hr.trans hh.symm)).symm.trans (h2.mp (h4.trans hh.symm))
end YM.AnalyticNext.QuarticMatch
