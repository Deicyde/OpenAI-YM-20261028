import YM.RG12.Shadows.Roads
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
variable {S:Shows V}
namespace Bazaar
variable (H:Bazaar V S) (u:Chi)(M:∀ i,Leaf (S i).A){C:ℕ→ℝ}(F:∀ i,(S i).Horn (M i) (C i)) (hc:RG12.Shadows.Charges H.winter 0 C)(he:RG12.Shadows.Charges H.winter 0 (fun i=>(M i).weight))
include H F he hc
lemma votes {p:ℝ}(hp:-1 < p): ∀ᶠ i:ℕ in atTop, let f:=(S i).gale (M i) u (F i).g; ContDiffAt ℝ (↑V.n) f 0 ∧ normJ 2 f 0 ≤ bStar V S i ^ p:=by
   have hf:= H.handbook' M u he hc F
   obtain ⟨T'⟩:=anthems V.n; obtain ⟨d,e,t,r,U,W,K,hE,hU,hK,hr,ha,hf'⟩:= H.leases T' u
   filter_upwards [hf (r:=2*p) (by linarith),hf',H.pulses.eventually_gt_atTop 0] with i Ht hL Hx f
   rw [Real.rpow_def_of_pos Hx]
   rw [Real.norm_of_nonneg (norm_nonneg _)] at Ht; unfold winter at Ht; change _ ≤ Real.exp ((2*p)*(Real.log (bStar V S i)/2)) at Ht
   rw [show (2*p)*(Real.log (bStar V S i)/2) = Real.log (bStar V S i)*p from by ring] at Ht
   exact ⟨((S i).mirrors _ hL (F i)).1,Ht⟩
end Bazaar
variable (V) (u : Chi)
-- Uniform.Barque admission including arbitrary tube horizon/rep/χ. Precision not claimed summable across stages. No contact or period refinements.
theorem wallet (A C:ℝ){p:ℝ}(hp:-1<p): ∀ᶠ s:ℝ in atTop,∀ (B:Barque V), B.x=s→∀ (M:Leaf B.A),M.weight≤A→∀ F:B.Horn M C,
    ContDiffAt ℝ (↑V.n) (B.gale M u F.g) 0∧ normJ 2 (B.gale M u F.g) 0 ≤ betaF G s V.patch.L ^ p:=by
   classical
   rw [eventually_atTop]; by_contra! h
   choose! s hs B hk M hw F hq using fun i:ℕ=> h (↑i:ℝ)
   let S:= B
   have hx :Tendsto (fun i=> (S i).x) atTop atTop:=by simp_rw [S,hk]; exact tendsto_atTop_mono hs (tendsto_natCast_atTop_atTop)
   let H:Bazaar V S:=⟨hx⟩
   have he : RG12.Shadows.Charges H.winter 0 (fun i=>(M i).weight):= (RG12.Shadows.Charges.frozen A _).move (Eventually.of_forall fun i=> by rw [abs_of_nonneg (M i).profit]; exact hw _)
   have hZ:= H.votes u M (C:=fun _=>C) F (RG12.Shadows.Charges.frozen C H.winter) he hp
   obtain ⟨i,ha,hv⟩:= hZ.exists
   have hf:= hq i ha
   unfold Bazaar.bStar S at hv; rw [hk] at hv; exact lt_irrefl _ (lt_of_lt_of_le hf hv)
end YM.PhysicalNext.Repeat.Sanction
