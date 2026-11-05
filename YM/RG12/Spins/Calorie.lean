import YM.RG12.Spins.Sym
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Drums
/-! Use angular pricing before division.Do not require physic census match.
 Hold derivative/order restored.This file asks Band prices, supplies exact
 post-accuracy when they hold, under Thermal kernels. Used with independently
 chartered analytic d4 stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Noise
open Function Filter Set Lattice Wilson RG Push.SectorMeasure
open Multi Multi.Vacuum.Jets Multi.Puff WardBin.Lies ProofPorts.CommonComplexProduction.Score
open Pressure PhysicalNext.JointLoad.Heir Next Next.SectorChange AnalyticBridge.LocalGaussian
open Finset MeasureTheory AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussian.Moments
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{C:Gaussian.Table (I × G.ColorIndex)}{χ: Chi}{K u t f a B r₀ w:ℝ}{c d:Side}
local notation "μ" A => Gaussian.cloud A
local notation "Ω" => Prices G I
variable {W : Directions G c→Prop} (σ F:Config G c→ℂ)(F': Config G d→ℝ)(U:Prices G I → Config G c → Config G d)
variable (J:Config G c→Gaussian.Table (I × G.ColorIndex))
lemma quota (a b: Directions G c) (ha:W a)(hb:W b) (h:(J 1).PosDef)(hk:0<K)(hw:0<w)(hu:0<u)(ht:0<t)(hK:Peak (J 1) K)(M N:ℝ)(Vv:ℝ)(n m:ℕ)(hM:0≤M)(hN:0≤N) :
    let Γ:=PhysicalNext.JointLoad.Heir.guard χ G I u w
    let r (z:Ω)(V:Config G c):ℂ:=Carillon.vary 1 J z V; let f (z:Ω) (W:Config G c):= ((F' (U z W)):ℂ)
    let Fnext (z:Ω)(W:Config G c):ℂ:= r z W* (Γ z:ℝ) * (f z W)
    let Z(z:Ω):=leftDerivs (Fnext z) [a,b] 1
    leftDerivs F [a,b] 1=(∫ z,Z z ∂(μ (J 1))) → Integrable Z (μ (J 1)) → Crest 2 σ 1 →σ 1=0 → (∀ j:Directions G c,W j → leftDerivs σ [j] 1=0)→
      (∀ z,Band 2 W 1 (t*M*(powers z^n)) 1 (r z))→(∀ z,z∈tsupport Γ → Crest 2 (f z) 1 ∧ Band 2 W 1 (t*N) (((u*Vv)^2)*(powers z^m)/t^2) (Noise.half (f z) (f (-z)) - σ)) →
    ‖leftDerivs F [a,b] 1-leftDerivs σ [a,b] 1‖ ≤ ‖leftDerivs σ [a,b] 1‖ * (2*Noise.fade w u K*(Fintype.card I:ℝ)*2^Fintype.card G.ColorIndex)+(M+N)^2*(u*Vv)^2 * AnalyticBridge.LocalGaussian.Moments.meter (Fintype.card (I × G.ColorIndex)) 0 K (m+2*n):=by
   intro Γ r v f z he hI hσ he₀ he₁ hr hF
   rw [he]; apply tender (χ:=χ) _ z hI h hK hk hu hw (by positivity) _; intro x
   let g:=Noise.voll r (fun x=>(Γ x:ℂ)) v
   have h': f = g:=by
     funext x W; change r x W* _ * _= _ * (r x W*_); ring
   have ht'(x:Ω):Γ (-x)=Γ x:=even_guard ..
   have h1:r x 1=1:=by change Complex.ofReal (Carillon.vary ..)=1; rw [Carillon.vary_exp h h]; simp [Carillon.value]
   have hΩ:= guard_silent χ (G:=G) (I:=I) hu hw (n:=2)
   have hy := circulationT v σ x M N m n a b ha hb hσ he₀ he₁ (show r (-x) = _ from by funext i; exact congrArg (fun (f:Config G c→ℝ)=>(f i:ℂ)) (even_vary ..)) (ht' x) (hΩ.little _) (fun _=>⟨hr x,h1⟩) (fun H=>⟨(hF x (subset_closure H)).1,(hF (-x) (subset_closure (by change Γ (-x)≠0; rwa [ht']))).1⟩) (fun hp=> (hF x (subset_closure hp)).2) ht hM hN
   change ‖(leftDerivs (f x) [a,b] 1+ leftDerivs (f (-x)) _ _)/2-_‖ ≤ _; rw [h']; exact hy
end YM.RG12.Noise
