import YM.RG12.Shadows.Clock
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
namespace Barque
variable (B:Barque V)(d:ℝ)(z:Prices G B.I)
abbrev pole6 (x :Panels 2):= tax6 B.X B.chip B.A B.a d B.A.beta (B.tour x) z
abbrev pole9 (x :Panels 2):= tax9 B.X B.chip B.A B.a B.q B.b d B.A.beta (B.tour x) z
lemma polish6(x:Panels 2):B.pole6 d z x=B.film d z x*Density.replace (B.C6 x) (B.C6 0) (B.swift d z x-z) z:=by
   change _* chalk B.X B.a (B.C6 x) z (_+0)=_; rw [add_zero]; unfold chalk C6; simp only [Function.comp_apply,B.j1]; rfl
lemma polish9(x:Panels 2):B.pole9 d z x=B.film d z x*Density.replace (B.C9 x) (B.C6 0) (B.speed d z x-z) z:=by
   change _* chalk B.X B.a (B.C9 x) z _ =_; unfold chalk C6; simp only [Function.comp_apply,B.j1]; rfl
end Barque
variable {S:Shows V}
namespace Bazaar
variable (H:Bazaar V S)
local notation "B!" i:max=> S i
local notation "η*" => H.winter
variable {d a:ℝ}(h:Canary G d a){z:Water S}(hg:RG12.Shadows.Charges H.winter 0 (H.Flood z))
def track (q:Water S)(d:ℝ): Drift Ibis.Cell (fun _=>Panels 2):=fun i _=>(S i).pole6 d (q i)
def slice (q:Water S)(d:ℝ): Drift Ibis.Cell (fun _=>Panels 2):=fun i _=>(S i).pole9 d (q i)
include H h hg
lemma taxUp : Tilts η* 2 0 true (track z d) (rend (track (-z) d)) (slice z d) (rend (slice (-z) d)):=by
   have hd: RG12.Shadows.Charges H.winter 0 (H.Flood (-z)) := by rwa [H.Flood_neg]
   obtain ⟨HC,H9,H8⟩:= H.binding
   let t (z:Water S)(i:ℕ)(_ : Unit):= (S i).film d (z i)
   have hh: Touch η* 2 0 true (t z) (rend (t (-z))):= by
      refine awakes ((H.flowPulse h hg).mono le_rfl (zero_add 1).le ((zero_add 1).trans_le one_le_two)) ((H.flowPulse h hd).mono le_rfl (zero_add 1).le ((zero_add 1).trans_le one_le_two)) (Eventually.of_forall fun i j=>?_)
      change Barque.film .. = Barque.film ..; rw [Barque.movie,Barque.movie]; simp only [Barque.jets0,leaves h,Finset.prod_const_one]
   let v (A:RG12.Shadows.Trail (fun i=>(S i).Q₀) (fun _=> Panels 2)) (i:ℕ)(x:Panels 2):= A i (-x)
   have hk:= RG12.Shadows.blend HC H9 H.pales.2.2 H.hands0 z (H.grand z hg).2 (Y6:=swift d z) (Y9:=speed d z) (W6:=v (swift d (-z))) (W9:=v (speed d (-z))) (H.centeredG h hg)
       (Eventually.of_forall fun i=>⟨(S i).swift_zero _ h,by change Barque.swift _ _ _ (-0)=_; rw [neg_zero,Barque.swift_zero _ _ h]; rfl⟩) H8
   have hg:= (Tilts.noCast hh).times hk; simp only [zero_add, fit] at hg
   refine hg.same (fun i _ x=> (S i).polish6 ..) (fun i _ x=> (S i).polish6 ..) (fun i _ x=> (S i).polish9 ..) (fun i _ x=> (S i).polish9 ..)
end Bazaar
end YM.PhysicalNext.Repeat.Sanction
