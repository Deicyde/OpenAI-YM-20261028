import YM.FullVolume.Nectar.Vau
import YM.FullVolume.Nectar.LandQ
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function PhysicalNext.Repeat PhysicalNext.Repeat.Luna.Aank Paint Tower Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof MergeProof.Accent Marker Push Push.AbsoluteSums Lattice Wilson Tint GridApprox.Nil
variable {X Y I E L:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E][NormedAddCommGroup L][NormedSpace ℝ L][CompleteSpace L]
variable {v b d:ℝ} {f:X→E}{F:sun→X→E}
-- exchange charts via any maps Config f→  E × Real.T. Used for arbitrary pose rotations.T
lemma Feel.rollup {p:I→ℝ} (Z:I→sun→X→E)(h:∀ i,Feel (Z i) (p i))(he:Summable p) : Feel (fun s U=>∑' i,Z i s U) (∑' i,p i):=by
    choose f hf hp using fun i=> (h i).costs; choose R hR hU using fun i=> (hp i).arrives
    have hp := he.of_nonneg_of_le (fun i=>norm_nonneg (R i)) hR; let v(s:sun):= Beam.read _ s (∑' i,R i); refine ⟨v,fun s U=>?_, ∑' i,R i,(norm_tsum_le_tsum_norm hp).trans (hp.tsum_le_tsum hR he),fun _=>rfl⟩
    let L:= Tint.see E U; have hh (i:I): L (Beam.read _ s (R i))=Z i s U:=by rw [← hU];exact hf ..
    let P:= L.comp (Beam.read _ s); have ha:= P.hasSum hp.of_norm.hasSum; have he : HasSum (fun i=>Z i s U) (L (v s)):= ha.congr_fun (fun i=> (hh i).symm); exact he.tsum_eq.symm
lemma tintTransit (L:E→L[ℝ] L) (g:Y→X)(u:Tint E X) (b:ℝ)(hL:∀ p,‖L p‖ ≤ b * ‖p‖)(hb:0≤b): ∃ v:Tint _ Y, ‖v‖ ≤ b*‖u‖ ∧∀ i,Tint.see _ i v=L (Tint.see E (g i) u):=by
   let p i:=L (Tint.see E (g i) u); have he i:‖p i‖≤ b*‖u‖:=(hL _).trans (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) (Tint.cast u) (g i)) hb)
   let v:Tint _ Y:= Tint.wear ⟨p,memℓp_infty ⟨_,Set.forall_mem_range.mpr he⟩⟩; exact ⟨v, lp.norm_le_of_forall_le (f:=Tint.cast v) (mul_nonneg hb (norm_nonneg _)) he,fun _=>rfl⟩
lemma Feel.transit (p:E→L[ℝ] L)(g:Y→X)(h:Feel F v)(hp:∀ z, ‖p z‖≤b*‖z‖)(hb:0≤b):Feel (fun s x=>p (F s (g x))) (b*v):=by
   obtain ⟨u,hV,h⟩:= h.costs
   choose f hf hF using fun (x:Tint E X)=> tintTransit p g x b hp hb
   have hz(x y): f (x-y)=f x-f y:=by apply Tint.liftEqual; intro i; rw [hF,map_sub,map_sub,map_sub,hF,hF]
   exact ⟨fun t=> f (u t),fun s t=>(hF ..).trans (congr_arg p (hV ..)),PaidBeam.transit f hz hb hf u h⟩
end YM.FullVolume.Nectar
