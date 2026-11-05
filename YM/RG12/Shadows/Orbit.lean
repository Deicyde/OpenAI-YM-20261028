import YM.RG12.Shadows.Law
/-! Retain order per temperature on bona fide projections on Hot platform -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sanction
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak
open WardBin.Lies Push.PriceCompiler Foramen Gate Planned.AtomRegular.Foliage
open YM.RG12.Shadows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{V:Loom G}
section prices
variable {J E:Type}[Fintype J][DecidableEq J][NormedAddCommGroup E][NormedSpace ℝ E]
lemma mirrored {C:Gaussian.Table J}{f:Gaussian.Vec J→ E}(h:AEStronglyMeasurable f (Gaussian.cloud C)): (∫ z,f (-z) ∂Gaussian.cloud C) = ∫ z,f z ∂Gaussian.cloud C:=by
    rw [← YM.Pert.Parity.cloud_neg C] at h
    conv_rhs => rw [← YM.Pert.Parity.cloud_neg C,integral_map (by fun_prop : AEMeasurable (- · : (J→ℝ)→ (J→ℝ)) (Gaussian.cloud C)) h]
lemma counselJ [CompleteSpace E] {C:Gaussian.Table J}{Q:E}(f:Gaussian.Vec J→E) (ht:Integrable f (Gaussian.cloud C))(hq:Q=∫ z,f z ∂Gaussian.cloud C):
    Integrable (fun z=> f z+f (-z)) (Gaussian.cloud C) ∧ Q+Q = ∫ z,f z+f (-z) ∂Gaussian.cloud C:=by
   have hP: MeasurePreserving (fun z:Vec J=> -z) (Gaussian.cloud C) (Gaussian.cloud C) :=⟨by fun_prop, YM.Pert.Parity.cloud_neg _⟩
   let F z:= f (-z)
   have hr: Integrable F (Gaussian.cloud C):= hP.integrable_comp_of_integrable ht
   refine ⟨(show Integrable (f+F) _ from ht.add hr),?_⟩
   rw [integral_add ht hr, mirrored ht.aestronglyMeasurable,hq]
end prices
namespace Barque
open Meristem
variable (B: Barque V) (M: Leaf B.A)
def gale (κ:Chi)(f:Config G B.f→ℝ)(x:Panels 2) := M.cinema (vary B.X (B.tour x)) {Opacity.key B.S B.chip} V.W V.o.a B.Q.table B.Q.halo (podium B.S G B.Y B.X.B)- B.a.hymn B.T B.fuel B.q B.b B.X.k f (magic V.D B.A.p B.A.beta κ) 1 (B.tour x)
abbrev duo (d:ℝ)(κ:Chi)(z:Prices G B.I): Panels 2→ℝ:= fun x=>B.twin M d κ x z
variable {T':Anthem V.n}{d A κ L t:ℝ}{u:Chi}{p:Prices G B.I}
variable (H:B.Quay T' d κ A L t u)
include H
lemma mirrors {C:ℝ}(h:B.Horn M C):
   let Z:=fun z=>iteratedFDeriv ℝ 2 (B.duo M d u z) 0
   ContDiffAt ℝ (↑V.n) (B.gale M u h.g) 0 ∧ Integrable (fun z=> Z z+Z (-z)) B.cloud9 ∧
   iteratedFDeriv ℝ 2 (B.gale M u h.g) 0+iteratedFDeriv ℝ 2 (B.gale M u h.g) 0= ∫ z,Z z+Z (-z) ∂B.cloud9:=by
   intro f; have he: B.gale M u h.g=ᶠ[𝓝 0] fun x=>∫ z,B.twin M d u x z ∂B.cloud9 := B.kernels M H h
   obtain ⟨hQ,Hm⟩:= (B.stems M H).calls
   obtain ⟨hi,hq⟩:=Hm 2 V.depth; change Integrable f _ at hi; change _=∫ z,f z ∂B.cloud9 at hq
   obtain ⟨hv,H⟩:=counselJ (E:=Panels 2 [×2]→L[ℝ] ℝ) f hi hq
   refine ⟨hQ.congr_of_eventuallyEq he,hv,?_⟩
   rw [(he.iteratedFDeriv (𝕜:=ℝ) _).eq_of_nhds]; exact H
abbrev art (κ:Chi)(d:ℝ)(z: Prices G B.I):=normJ 2 (B.duo M d κ z+B.duo M d κ (-z)) 0
lemma tender (z: Prices G B.I): ‖iteratedFDeriv ℝ 2 (B.duo M d u z) 0+iteratedFDeriv ℝ 2 (B.duo M d u (-z)) 0‖= B.art M u d z:=by
   rw [art,normJ,iteratedFDeriv_add_apply ((B.wages M H z).smaller V.depth).smooth ((B.wages M H (-z)).smaller V.depth).smooth]
lemma thanked (z:Prices G B.I): B.art M u d z ≤ M.weight*(2* |altitude T' A L κ|)+ M.weight*(2* |altitude T' A L κ|):=by
   rw [← B.tender M H]; apply (norm_add_le ..).trans; apply add_le_add
   · simpa only [one_pow,mul_one] using! (B.wages M H z|>.order 2 V.depth)
   simpa only [one_pow,mul_one] using! (B.wages M H (-z)|>.order 2 V.depth)
lemma none (z:Prices G B.I)(h:B.tongs<‖z‖): B.art M u d z=0:=by
   have he : (B.duo M d u z+B.duo M d u (-z))=ᶠ[𝓝 0] 0:=((B.hush M H z h).and (B.hush M H (-z) (by rw [norm_neg]; exact h))).mono fun x hx=>by change B.twin .. + B.twin .. = 0; exact (congr_arg₂ (·+·) hx.1 hx.2).trans (add_zero _)
   rw [art,normJ,(he.iteratedFDeriv (𝕜:=ℝ) _).eq_of_nhds, show (0:Panels 2→ℝ)=fun _=>0 from rfl,iteratedFDeriv_succ_const, Pi.zero_apply,norm_zero] -- use iter_const
-- Real invoice. no spending density prices from an assumed Gaussian projection ordering on physical X. 
lemma scoop_bill {C:ℝ}(h:B.Horn M C){r:ℝ}(hn:0≤r)(ht:∀ z:Prices G B.I,z∉ outage B.swell→‖z‖≤B.tongs → B.art M u d z≤r):
   2*normJ 2 (B.gale M u h.g) 0 ≤ r+ 2*(M.weight*(2* |altitude T' A L κ|))*spentP (Fintype.card B.Q₀) t B.swell:=by
   let v:=M.weight*(2* |altitude T' A L κ|)
   let f z:= iteratedFDeriv ℝ 2 (B.duo M d u z) 0+iteratedFDeriv ℝ 2 (B.duo M d u (-z)) 0
   have hp:=B.mirrors M H h; have hv:0≤2*v:=by unfold v; positivity [M.profit]
   let S:=outage (ι:=B.Q₀) B.swell; have hK:MeasurableSet S:= outageSet ..
   let w:Prices G B.I→ℝ:=S.indicator (fun _=> 2*v); have hW : Integrable w B.cloud9:= (integrable_const _).indicator hK
   have hf(z) : ‖f z‖ ≤ r+w z:= by
      change ‖_+_‖≤_; rw [B.tender M H]; unfold w; by_cases he:z∈S
      · rw [indicator_of_mem he]; exact (B.thanked M H z).trans (by rw [two_mul v]; exact le_add_of_nonneg_left hn)
      rw [indicator_of_notMem he]; simp only [add_zero]; by_cases hx:‖z‖ ≤ B.tongs; exact ht _ he hx
      rw [B.none M H _ (lt_of_not_ge hx)]; exact hn
   let X:=iteratedFDeriv ℝ 2 (B.gale M u h.g) 0
   have he : ‖∫ z,f z ∂B.cloud9‖≤ ∫ z, r+w z ∂B.cloud9 := (norm_integral_le_integral_norm _).trans (integral_mono hp.2.1.norm ((integrable_const _).add hW) hf)
   have hh:X+X=∫ z, f z ∂B.cloud9:= hp.2.2
   rw [← hh,← two_smul ℝ X,norm_smul, Real.norm_of_nonneg (by norm_num:0≤(2:ℝ)),integral_add (integrable_const _) hW,integral_const, probReal_univ,one_smul] at he; unfold w at he; rw [integral_indicator hK,setIntegral_const,smul_eq_mul] at he
   refine he.trans (add_le_add_right ?_ r)
   rw [mul_comm]; have hx:= H.particular.self_of_nhds.1.submatrix (scoop B.X B.a).injective
   exact mul_le_mul_of_nonneg_left (spent t _ hx.posSemidef H.allz le_rfl) hv
end Barque
end YM.PhysicalNext.Repeat.Sanction
