import YM.RG08.Quarry.Valet

/-! # Reader template: both node & constant Gauge (nondisconnected assumption-free) -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Quarry
open Filter Function Matrix Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Slate Gallery
open Forms Isles Laurent -- Mix
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {G : Gauge}
abbrev cuff (G:Gauge):= Loc G 1 ⊕ G.ColorIndex
abbrev foil (G:Gauge):= Fin 3×G.ColorIndex
def gaugeIn (d:G.El)(P Q R:G.Color): G.El:= d*(G.lieExp (-Q)*G.lieExp P*G.lieExp R)*d⁻¹
private lemma gauge_height (d:G.El):gaugeIn d 0 0 0=1:=by simp [gaugeIn]
-- Compose with plog on arbitrary space
private lemma composed {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](f:E→G.Mat)(he:f 0=1)(h:Pace f): Pace (G.plog ∘ f):=ContDiffAt.comp 0 (g:=G.plog) (he.symm ▸ G.plog_diff) h
abbrev Trip (G:Gauge):= G.Color × G.Color × G.Color
private def otto (G:Gauge)(z:Trip G):= gaugeIn (1:G.El) z.1 z.2.1 z.2.2
private lemma pMatrix:ContDiff ℝ ω (G.mat ∘ otto G):=by
 let E:= fun u:G.Color=>G.mat (G.lieExp u)
 have hj : ContDiff ℝ ω E:=G.exp_jet
 have he : G.mat ∘ otto G=fun z: Trip G=>E (-z.2.1)*E z.1*E z.2.2:=by funext z;simp only [Function.comp_apply,otto,gaugeIn,one_mul,inv_one,mul_one,Gauge.mat_mul];rfl
 rw [he];exact ((hj.comp contDiff_snd.fst.neg).mul (hj.comp contDiff_fst)).mul (hj.comp contDiff_snd.snd)
private lemma sporeE : Pace (G.plog ∘ G.mat ∘ otto G):=composed (G.mat ∘ otto G) (by change G.mat (gaugeIn 1 0 0 0)=1;rw [gauge_height,G.mat_one]) pMatrix.contDiffAt

-- Log reader in cover type, sign convention chosen opposite gauge to give gradient bolt.
def flourish (d:G.El)(P Q R:G.Color): G.Color:=G.adjoint d (G.plog (G.mat (gaugeIn (1:G.El) P Q R)))
lemma tall (d:G.El): Pace (fun z:G.Color × G.Color × G.Color=>flourish d z.1 z.2.1 z.2.2):=by
 let V:= (G.adjoint d).toContinuousLinearMap
 change Pace (V ∘ (G.plog ∘ G.mat ∘ otto G))
 apply V.contDiff.contDiffAt.comp 0 sporeE
private lemma heg{d:G.El}{x:G.Color}: G.lieExp (G.adjoint d x)=d*G.lieExp x*d⁻¹ := by
  apply G.mat_injective
  rw [G.mat_lieExp,G.mat_mul,G.mat_mul,G.mat_adjoint,G.exp_conjugate,G.mat_lieExp,G.mat_inv]; rfl
lemma colored (d:G.El): ∀ᶠ z:G.Color × G.Color × G.Color in 𝓝 0, G.plog (G.mat (gaugeIn d z.1 z.2.1 z.2.2))=flourish d z.1 z.2.1 z.2.2:=by
 let f(z:G.Color × G.Color × G.Color):= gaugeIn (1:G.El) z.1 z.2.1 z.2.2
 have hg:f 0=1:=gauge_height ..
 have hT:Tendsto f (𝓝 0) (𝓝 1):=by
    rw [←hg]; exact (show Continuous f from ((continuous_const.mul (((G.lieExp_cont.comp continuous_snd.fst.neg).mul (G.lieExp_cont.comp continuous_fst)).mul (G.lieExp_cont.comp continuous_snd.snd)))).mul continuous_const).tendsto 0
 have H : Tendsto (fun z:G.Color×G.Color×G.Color=>flourish d z.1 z.2.1 z.2.2) (𝓝 0) (𝓝 0):=by simpa only [flourish,Prod.fst_zero,Prod.snd_zero,gauge_height,G.mat_one,G.plog_one,map_zero] using! (tall d).continuousAt.tendsto
 filter_upwards [hT.eventually G.plog_right,H.eventually G.plog_left] with z h h'
 have he:G.lieExp (flourish d z.1 z.2.1 z.2.2)=gaugeIn d z.1 z.2.1 z.2.2:=by change G.lieExp (G.adjoint d (G.plog (G.mat (f z))))=_;rw [heg,h]; unfold f gaugeIn; group
 rw [←he];exact h'

-- directional derivative, identify by matching matrix exp along scalar line.
private lemma plume (x:G.Color):HasDerivAt (fun t:ℝ=> t • x) x 0:=by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const x
private lemma plumed (x:G.Color): HasDerivAt (fun t:ℝ=>G.mat (G.lieExp (t • x))) (G.colorMat x) 0:=G.expDiff_zero.comp_hasDerivAt_of_eq (0:ℝ) (plume x) (zero_smul ℝ x).symm
lemma speed (d:G.El)(a b c:G.Color):HasDerivAt (fun t:ℝ=>flourish d (t • a) (t • b) (t • c)) (G.adjoint d (a-b+c)) 0:=by
 let U(t:ℝ):=G.mat (gaugeIn (1:G.El) (t • a) (t • b) (t • c))
 have h : HasDerivAt U (G.colorMat (a-b+c)) 0:=by
    have hr:= ((plumed (-b)).mul (plumed a)).mul (plumed c)
    simp only [Pi.mul_apply,zero_smul,Gauge.mat_lieExp_zero,Gauge.mat_one,mul_one,one_mul] at hr
    have he:U=(fun t=> G.mat (G.lieExp (t • (-b)))* G.mat (G.lieExp (t • a))*G.mat (G.lieExp (t • c))):=by funext t;unfold U gaugeIn;simp only [one_mul,inv_one,mul_one,Gauge.mat_mul,smul_neg]
    unfold U at he -- undo
    rw [show U=_ from he,map_add,map_sub];rw [map_neg] at hr
    rw [sub_eq_add_neg,add_comm (G.colorMat a)];exact hr
 have h1:HasFDerivAt G.plog (fderiv ℝ G.plog 1) 1:=(G.plog_diff.differentiableAt (by simp)).hasFDerivAt
 let x:=a-b+c
 have hx:(fderiv ℝ G.plog 1) (G.colorMat x)=x:=by
    have hp : Tendsto (fun t:ℝ=>t • x) (𝓝 0) (𝓝 0):=by simpa only [zero_smul] using! (plume x).continuousAt.tendsto
    have hf:=hp.eventually G.plog_left
    have hb:=plumed x
    have hc:HasDerivAt (fun t:ℝ=>G.plog (G.mat (G.lieExp (t • x)))) ((fderiv ℝ G.plog 1) (G.colorMat x)) 0:=by
       exact h1.comp_hasDerivAt_of_eq (0:ℝ) hb (by simp)
    have hE:(fun t:ℝ=>G.plog (G.mat (G.lieExp (t • x))))=ᶠ[𝓝 0] (fun t:ℝ=>t • x):=hf
    exact (hc.congr_of_eventuallyEq hE.symm).unique (plume _)
 have ha: HasDerivAt (G.plog ∘ U) x 0:=by
    conv in HasDerivAt _ x _=> rw [← hx] -- may rewrite in first occurrence in U? contains x not defeq reduc
    exact h1.comp_hasDerivAt_of_eq 0 h (by simp [U,gaugeIn])
 exact (G.adjoint d).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) ha
end YM.RG08.Quarry
