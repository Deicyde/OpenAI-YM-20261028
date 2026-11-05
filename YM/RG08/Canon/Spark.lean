import YM.RG08.Canon.Saddles
import YM.Next.STATIONARY.Level.SliceGate
/-! # Actual centered aperture argument on a chosen analytic germ
 Local (fixed c). Include additive two loops' constant convention here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {F : Forest S.ratio} {p : Clip} {R : PathData G} {σ K Λ : ℝ} {ρ : fieldDir G c 1 → AxisChart G F}
variable {η:ℝ} (v:Stationary.Link G c) {t:S.Choices} {D : ChartRatio G} {L : fieldDir G c 1 → (AxisChart G F)≃L[ℝ] AxisChart G F}
local notation "U" => AxisChart G F
local notation "X" => (U) × ℝ
local notation "Γ" => fieldDir G c 1
variable (h : Salvo t F R p ρ η L)
local notation "Θ" => incount v ρ L
abbrev lance (_h:Salvo t F R p ρ η L)(x:X) : Config G f := lifting F (represent (colorX v x)) (Θ x)
abbrev scent (D : ChartRatio G) (_h:Salvo t F R p ρ η L)(y:ℝ) := thermal F t p R ρ D (spanL v y)-thermal F t p R ρ D 0
abbrev sublet (D : ChartRatio G) (h:Salvo t F R p ρ η L)(x:X) := Real.exp (scent v D h x.2)*swing (L (colorX v x))* jacobian D (Θ x)
abbrev tinted (D : ChartRatio G) (h:Salvo t F R p ρ η L)(x:X) := sublet v D h x*Real.exp (-loop R (lance v h x))

include h
lemma gleam_color : Army (lance v h) (0:X) ∧ lance v h 0=1 := by
  have ha : ContDiffAt ℝ ω (colorX v (F:=F)) 0:= (spanL_changes v).contDiffAt.comp _ contDiffAt_snd
  have hf : colorX v (0:X)=0:= by simp [colorX,spanL]
  refine ⟨fun i=>?_,?_⟩
  · exact (show ContDiffAt ℝ ω (fun u:Work.F03.ChartVars F G=> G.mat (Work.F03.live F u i)) (colorX v (0:X),Θ 0) from by rw [hf,(insideLive v h).2]; exact Work.F03.live_smooth F i).comp (f:=fun z=> (colorX v z,Θ z)) _ (ha.prodMk (insideLive v h).1)
  unfold lance; rw [hf,(insideLive v h).2, Precision.link_one,lifted,replica_one]

lemma swings : ContDiffAt ℝ ω (fun u=> swing (L u)) 0 := by
  let e:= Module.Free.chooseBasis ℝ (U)
  let Q (k : (U)→L[ℝ] (U)):= LinearMap.toMatrix e e k.toLinearMap
  let i : ((U)→L[ℝ] (U)) →ₗ[ℝ](Matrix _ _ ℝ):= { toFun:=Q, map_add' _ _:= by unfold Q at *; exact map_add (LinearMap.toMatrix e e) _ _, map_smul' a v:= by unfold Q at *; exact map_smul (LinearMap.toMatrix e e) _ _ }
  let M u:= Q (L u).toContinuousLinearMap
  apply (cont_kinDet (H:=M) (i.toContinuousLinearMap.contDiff.contDiffAt.comp _ h.smooth)).congr_of_eventuallyEq
  apply Eventually.of_forall; intro u; exact Eq.symm (LinearMap.det_toMatrix ..)
lemma gleam_ink (hp : R.Bounds p σ K Λ) : ContDiffAt ℝ ω (fun x=> loop R (lance v h x)) 0 := by
  unfold loop Patch.average; refine contDiffAt_const.mul (ContDiffAt.sum (fun i _=>?_))
  refine Work.F02.uncut_contDiffAt (A:=fun x=> pull i 0 (lance v h x)) hp.width hp.two (fun j=> ?_)
  unfold pull Lattice.Step.read; split
  · exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ ((gleam_color v h).1 _)
  exact (gleam_color v h).1 _
lemma gleam_start (hp : R.Bounds p σ K Λ) (hd : LocalRatio D) : ContDiffAt ℝ ω (sublet v D h) 0 := by
  have ha : ContDiffAt ℝ ω (colorX v (F:=F)) 0:= (spanL_changes v).contDiffAt.comp _ contDiffAt_snd
  have hf : colorX v (0:X)=0:= by simp [colorX,spanL]
  have he : ContDiffAt ℝ ω (fun z : X=>scent v D h z.2) 0:= (((hf.symm ▸ born hp h.critical h.ears h.price hd t: ContDiffAt ℝ ω (thermal F t p R ρ D) (colorX v (0:X))).comp _ ha).sub contDiffAt_const)
  have hi : ContDiffAt ℝ ω (fun z : X=>swing (L (colorX v z))) 0 := (show ContDiffAt ℝ ω (fun x=> swing (L x)) (colorX v (0:X)) from hf.symm ▸ swings h).comp _ ha
  exact ((Real.contDiff_exp.contDiffAt.comp _ he).mul hi).mul ((show ContDiffAt ℝ ω (jacobian D) (Θ 0) from by rw [(insideLive v h).2]; exact PertExtension.Chart.Ratio.jacobian_smooth hd).comp _ (insideLive v h).1)
lemma tint_starts (hp : R.Bounds p σ K Λ) (hd : LocalRatio D) : ContDiffAt ℝ ω (tinted v D h) 0:= (gleam_start v h hp hd).mul (Real.contDiff_exp.contDiffAt.comp (f:=fun x=> -loop R (lance v h x)) _ (gleam_ink v h hp).neg)
-- singleton not required to refer to Haar scale in C
lemma tint_lands (hd : LocalRatio D)(hx : loop R (1:Config G f)=0) : ∀ᶠ t':ℝ in 𝓝 0, tinted v D h (0,t')= hatsScale S F D := by
  let H x:= (Precision.hessian F t p R x (ρ x)).det
  have hC := Work.F05.hessian_pos h.price h.ears h.critical t
  have hr : ∀ᶠ z:U in 𝓝 0, jacobian D z=hatsScale S F D * ∏ i,D.J (z i) ∧ 0<∏ i,D.J (z i) := by
    have hQ : ∀ᶠ x:G.Color in 𝓝 0,0<D.J x := by filter_upwards [Metric.ball_mem_nhds (0:G.Color) hd.patch] with i hi using hd.pos i hi
    filter_upwards [eventually_all.mpr (fun i : F.Free=>
      (show ContinuousAt (fun z : F.Free→G.Color=>z i) 0 from (continuous_apply _).continuousAt).eventually hQ)] with z hz -- T?
    refine ⟨?_,prod_pos (fun i _=> hz i)⟩
    unfold hatsScale jacobian; rw [← show (∏ _i:F.Free,D.scale)=_ from (show _=D.scale^Fintype.card F.Free from by simp),← prod_mul_distrib]; exact prod_congr rfl fun i _=> max_eq_left (mul_pos hd.scale (hz _)|>.le)
  have hu : Tendsto ρ (𝓝 0) (𝓝 0):= h.critical.1 ▸ h.critical.2.1.continuousAt.tendsto
  filter_upwards [(spanL_e v).eventually h.honor,(spanL_e v).eventually hC,(spanL_e v).eventually (hu.eventually hr)] with y ⟨hg,hQ,hX⟩ hp ⟨he,hL⟩
  let M:= H 0; let u:=spanL v y; let w:=swing (L u); let a:=∏ i,D.J (ρ u i); let B:=loop R (lance v h (0,y))
  change 0<a at hL; change 0<w at hg; change w^2*H u=M at hQ; change 0<H u at hp
  have hz : Θ (0,y)=ρ u:= by simp [incount,u]
  have hM : thermal F t p R ρ D 0= (1/2)*Real.log M := by unfold thermal; rw [h.critical.1,link_one,lifted,replica_one,hx,zero_add]; unfold M H; rw [h.critical.1]; simp only [Pi.zero_apply,hd.anchored,prod_const_one,Real.log_one,sub_zero]
  have hV : thermal F t p R ρ D u=B+(1/2)*Real.log (H u)- Real.log a:= by unfold thermal B H a; unfold lance; rw [hz]
  have ht : Real.log M= 2*Real.log w+Real.log (H u):= by rw [← hQ,Real.log_mul (by positivity : w^2≠0) hp.ne',Real.log_pow]; norm_num
  have hh : scent v D h y= B+ (-Real.log a+-Real.log w) := by unfold scent; rw [show thermal F t p R ρ D (spanL v y)=_ from hV,hM,ht]; ring
  change Real.exp (scent v D h y)*w*jacobian D (Θ _)*Real.exp (-B)=_
  rw [hh,hz,show jacobian D (ρ u)= hatsScale S F D*a from he,Real.exp_add,Real.exp_add]; simp only [Real.exp_neg,Real.exp_log hg,Real.exp_log hL]; field_simp [Real.exp_ne_zero]
lemma tint_rayEq : ∀ x:U, tinted v D h (x,0)=tinted 0 D h (x,0) ∧ starsP v h (x,0)=starsP 0 h (x,0) := by
  intro x; simp [starsP,tinted,lance,sublet,spanL,scent,incount,colorX]
end YM.RG08.Canon
