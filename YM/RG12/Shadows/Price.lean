import YM.RG12.Shadows.Husband
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
def swift (y:Panels 2): Prices G B.I:= reading6 B.X (B.tour y) B.a z d B.A.beta
def speed (y:Panels 2): Prices G B.I:= reading9 B.X (B.tour y) B.a z B.q B.b d B.A.beta
lemma swift_zero {d a:ℝ}(h: Canary G d a):B.swift d z 0=z:= by unfold swift; rw [B.j1]; exact fast_zero B.X B.a h B.H.laws.intake.positive z
lemma scone(x:Panels 2)(i:B.Q₀):B.swift d z x i=z i+B.fuel⁻¹*(B.luster i.1 d z x i.2-B.W6 i.1 x i.2):=by
  obtain ⟨p,q⟩:=i
  have he:= to_strip B.X (B.tour x) B.a B.H.laws.intake.positive z d
  let y:=B.swift d z x; have hf:= congrFun he p
  change B.W6 p x+B.fuel • tape y p=Baffle.fawn .. at hf
  unfold Baffle.fawn at hf
  rw [show Baffle.anchor B.X B.a z B.A.beta p=B.gas z p from rfl,B.chi] at hf -- X.chi? B.chi
  change _=B.gas z p+B.luster p d z x at hf
  have hh: B.fuel • tape y p=B.gas z p+(B.luster p d z x-B.W6 p x):= by rw [← add_sub_assoc,← hf]; abel
  have hm:=congr_arg (fun x:G.Color=> x q) hh
  rw [B.gaseous] at hm; change B.fuel*y (p,q)=B.fuel*z (p,q)+(_-_) at hm
  change y (p,q)=_; apply mul_left_cancel₀ B.hot.ne'; rw [mul_add,←mul_assoc,mul_inv_cancel₀ B.hot.ne',one_mul]; exact hm
lemma fit9(x:Panels 2)(i:B.Q₀): B.speed d z x i=B.swift d z x i-B.fuel⁻¹*(B.W9 i.1 x-B.W6 i.1 x) i.2:=by
  unfold speed reading9 distance9; change B.swift _ _ _ _ + B.fuel⁻¹ * (-(B.W9 i.1 x-B.W6 i.1 x) i.2)= _
  ring_nf
end Barque
end YM.PhysicalNext.Repeat.Sanction
