import YM.RG12.Shadows.Ice
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
variable (B:Barque V)
abbrev C6 : Panels 2→Matrix B.Q₀ B.Q₀ ℝ:= lamp6 B.X B.a ∘ B.tour
abbrev C9 : Panels 2→Matrix B.Q₀ B.Q₀ ℝ:= lamp9 B.X B.a ∘ B.tour
abbrev W6(i:B.I) : Panels 2 → G.Color := volume6 B.X B.a i ∘ B.tour
abbrev W9(i:B.I): Panels 2 → G.Color := volume9 B.X B.a B.q 1 B.b i ∘ B.tour
abbrev aim0 (i:B.I) : Panels 2→ Directions G B.c := launch 1 (pole B.X B.a i) (reach B.x) 1 B.U
def helm := Cube.fee V.Lib.Z*B.B.threshold*(1+(reach B.x:ℝ))^B.B.power*(1+(radiusD B.x:ℝ))^B.B.power
local notation "K!"=> B.helm
open Bid Next.Foundations
lemma dome (i:B.I): Tracks (B.aim0 i) 0 V.n (K!):=by
  let r:= (pole B.X B.a i); have hX:=B.ho.rehearsed; have ha:=Cub.posed V.Lib.Z hX.wire (o:=r)
  have he : loom B.B (reach B.x) (Cube.fee V.Lib.Z)*spine B.B.power r B.u ≤ K!:= by
    unfold loom spine r helm; have hHH:=B.B.threshold_pos; have hhz:=Cube.fee_one V.Lib.Z; gcongr; apply Brim.far B.a B.hu (show coverNumber (radiusB B.x) B.Y≤radiusB B.x from B.hc ▸ B.hx)
  exact Malachite.onJourney ha B.U (Cube.fee_one V.Lib.Z) he V.depth B.rail
lemma aim_zero (i:B.I): B.aim0 i 0=0:=by rw [aim0,launch_zero,Cub.blankBirth]
open AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Placement in
-- coordinates along each pole in identity gauge
def C6d(i k:B.Q₀)(x:Panels 2) := Malachite.porch6 B.X B.a (B.aim0 i.1 x) i k
def C9d(i k:B.Q₀)(x:Panels 2) := Malachite.porch9 B.X B.a (B.aim0 i.1 x) i k
lemma nearGauge : ∀ᶠ x in 𝓝 (0:Panels 2), (∀ i:B.I,B.W6 i x= spot6 B.X B.a i (B.aim0 i x) ∧ B.W9 i x = spot9 B.X B.a i (B.aim0 i x)) ∧
    ∀ i j:B.Q₀, B.C6 x i j=B.C6d i j x∧B.C9 x i j=B.C9d i j x:=by
  have hX:=B.ho.rehearsed; have hroom := B.living.sails.room
  have hμ:ShellAccess B.S G B.x V.W B.X.width V.o.γ:=B.width.symm ▸ B.H.laws.data.access
  have h (i:B.I): ∀ᶠ x in 𝓝 (0:Panels 2), AgreeNear id (pole B.X B.a i) (reach B.x) (gauge (1:Site B.c→G.El) (B.tour x)) (increment 1 (B.aim0 i x)):=
    (flowJourney 1 B.U).eventually (Cub.posed V.Lib.Z hX.wire (o:=pole B.X B.a i)).seen
  let g:Site B.c→G.El:= 1
  filter_upwards [eventually_all.mpr h] with x hx
  constructor
  · intro i; have ha:= light6 B.X B.a i hroom hμ B.curtains.outer g _ (hx i); have hb:= light9 B.X B.a i B.q B.ho.bulletin g _ (hx i) B.b (1: Config G B.f)
    change G.adjoint 1 _ = _ at ha hb; rw [G.adjoint_one] at ha hb; exact ⟨ha,hb⟩
  intro k l; obtain ⟨i,j⟩:=k; obtain ⟨i',j'⟩:=l
  have hf (i:B.I) : zone i i (B.a.toned g)=1:= by
    ext k l; unfold Museum.toned; rw [tonewise,poreG]; change G.adjoint 1 _ k=_; rw [G.adjoint_one]; unfold ConnectedActivityE6.dot; by_cases h:k=l
    · subst k; simp [EuclideanSpace.basisFun_apply]
    simp [h,EuclideanSpace.basisFun_apply]
                                                          -- multiline
  let W:= (B.aim0 i x)
  have h6:= ray6 B.X B.a i hroom B.curtains.outer g W (hx i) i'
  have h9:= ray9 B.X B.a i B.ho.bulletin g W (hx i) i'
  rw [hf i',hf i,transpose_one,one_mul,mul_one] at h6 h9
  refine ⟨?_,congr_fun (congr_fun h9 j) j'⟩
  have hv:=congr_fun (congr_fun h6 j') j
  change lamp6 B.X B.a (B.tour x) (i,j) (i',j') = porch6 B.X B.a W (i,j) (i',j')
  rw [←sym6 B.X B.a (B.tour x),←symR B.X B.a W]; exact hv
end Barque
end YM.PhysicalNext.Repeat.Sanction
