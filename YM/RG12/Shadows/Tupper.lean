import YM.RG12.Shadows.Shape
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
abbrev cloud9:=Gaussian.cloud (B.C6 0)
def swell := sliceD G B.S.patch.L V.D B.x
def tongs := Coat.burst G B.S.patch.L B.x*(5*V.o.a*B.X.t+|V.o.cap| *B.X.t)
-- exact comparison uptake condition.
structure Fuel (T:Anthem V.n)(d rM N χ W M t l T' v :ℝ)(κ:Chi):Prop where
  stir:Tentacle M W l v t T' B.X B.a B.q B.b B.U V.n
  sph : ∀ (z:Prices G B.I), ‖z‖ ≤ B.tongs → Score B.X B.chip B.A B.a B.q κ B.b V.D z (incomingE G B.S.patch.L B.x) d V.o.a rM N χ T B.tour 0 -- χ might score price <>tent C!
  stays : 8*V.o.a*B.X.t ≤ d/2
  cover0 : l ≤ B.X.t/2
  snap : 0 ≤ B.swell ∧ B.fuel*(Fintype.card G.ColorIndex:ℝ)*(B.swell+rM)< (V.D.ε*B.A.p.threshold)/8
-- analytic integration prerequisites in both formulas
structure Quay (T:Anthem V.n)(d rM N χ t:ℝ)(κ:Chi): Prop where
  sph : ∀ (z:Prices G B.I), ‖z‖ ≤ B.tongs → Score B.X B.chip B.A B.a B.q κ B.b V.D z (incomingE G B.S.patch.L B.x) d V.o.a rM N χ T B.tour 0
  ranks : Ranks B.X B.chip B.A B.a B.q κ B.b V.D B.tour d V.o.a 0 V.n
  cool : 0< V.o.a*B.X.t
  stays : 8*V.o.a*B.X.t ≤ d/2
  heat : ∃ A:ℝ, Canary G d A ∧∀ᶠ p:Panels 2 in 𝓝 0,Drivable B.X d A (B.tour p)
  particular :∀ᶠ p:Panels 2 in 𝓝 0, (vary B.X (B.tour p)).relating.PosDef∧ (B.C9 p).PosDef
  healthy : ∀ᶠ x in 𝓝 (0:Panels 2),∀ z, veil B.X B.a B.q κ B.b V.D B.A.p d B.A.beta z (B.tour x)≠0→ coin B.X B.chip B.A B.a d B.A.beta V.o.a (B.tour x) z=1∧ B.OpenKey z
  caps : ∀ i,‖volume6 B.X B.a i B.X.V‖ ≤ V.o.cap*B.X.t
  scales : 0≤B.tongs ∧ Baffle.screen V.o.a B.X.t V.o.cap B.fuel ≤ B.tongs
  allz:∀ (v:Prices G B.I),dotProduct v (B.C6 0 *ᵥ v) ≤ t * dotProduct v v
  snap : 0 ≤ B.swell ∧ B.fuel*(Fintype.card G.ColorIndex:ℝ)*(B.swell+rM)< (V.D.ε*B.A.p.threshold)/8
lemma fuelCast {T:Anthem V.n}{κ:Chi}{d e rM N χ v M T' l t W:ℝ}(h:Canary G d e)(F:B.Fuel T d rM N χ W M t l T' v κ):B.Quay T d rM N χ t κ:=by -- W new tent C
   have H:= F.stir; let X:= B.X
   have hm:Mode B.tour (0:Panels 2) V.n M:= by have h:=H.sunny; rw [B.center] at h; exact h
   have he':= H.toward; rw [B.center] at he'
   have he : ∀ᶠ p in 𝓝 (0:Panels 2), (vary X (B.tour p)).relating.PosDef∧ (B.C9 p).PosDef:= he'
   have he₀:= Silica.nearby X h B.j1 hm
   have h₀:= H.area; have h₁:=H.skies; have hx (k):= H.offset k; have ht(k):=H.out k
   -- B center rewrite independent here
   have hv i j : ContDiffAt ℝ (↑V.n) (fun p=> B.C6 p i j) 0:=by
      apply (show Brush V.n W 1 (fun p=> B.C6 p i j) 0 from ?_).smooth -- infer W
      have hx := h₀.liable i j; rw [B.center] at hx; exact hx
   have hw i j: ContDiffAt ℝ (↑V.n) (fun p=> B.C9 p i j) 0:=by
      have hx:= h₁.liable i j; rw [B.center] at hx; exact hx.smooth
   have hh i:Brush V.n T' 1 (fun p:Panels 2=> volume6 B.X B.a i (B.tour p)) 0:=by have hx:=H.out i; rw [B.center] at hx; exact hx
   have hp i:Brush V.n l 1 (offsetRun B.X B.a i B.q B.b (1:Config G B.f) ∘ B.tour) 0:=by have hx:=H.offset i; rw [B.center] at hx; exact hx
   obtain ⟨hC,hC',hG,hΓ⟩:= B.H.laws.data.safety; have hK:=hΓ B.F B.X rfl B.width B.legal
   have hT : 0<X.t:= B.living.sails.room.fiery
   have hl i:‖volume6 B.X B.a i B.X.V‖≤V.o.cap*X.t:=by change ‖voltage _ _‖ ≤ _; rw [show (vary B.X B.X.V)=X from rfl,←Vine.agrees_all _ B.living.sails.room B.legal]; exact hK.1 _
   have hc:0<V.o.a*X.t:= mul_pos V.o.large hT
   refine ⟨F.sph,lighthouse X B.chip B.A _ B.q κ B.b V.D h B.j1 B.H.laws.intake V.o.a he.self_of_nhds.1 he.self_of_nhds.2 hv hw (fun i=> (hh i).smooth) (fun i=> (hp i).smooth) (fun i=> (Silica.chargeMode X _ hm _).smooth),hc,F.stays,⟨e,h,he₀⟩,he,?_,hl,?_,?_,F.snap⟩
   · refine liveIn X B.a h B.H.laws.intake.positive B.ho B.lynx B.curtains B.q κ B.b (B.center.symm ▸ (flowJourney 1 B.U)) ?_ hc (L:=V.o.cap+1/2) ?_ ?_
     · intro i; have hv' : ContDiffAt ℝ (↑V.n) (volume9 X B.a B.q 1 B.b i ∘ B.tour) 0:= ((hp i).gathering (hh i)).smooth.congr_of_eventuallyEq (Eventually.of_forall fun _=> (sub_add_cancel ..).symm) -- mismatch hp/hh Rates both? Brush gathering same growth=1, ok
       have hh:= hv'.continuousAt.tendsto; simpa only [Function.comp_apply,B.j1] using hh
     · intro i; have hg := (hp i).bound; change ‖volume9 X B.a B.q 1 _ i (B.tour 0)-volume6 X B.a i (B.tour 0)‖ ≤l at hg; rw [B.j1] at hg; have ht':=norm_sub_le_norm_sub_add_norm_sub (volume9 X B.a B.q 1 B.b i B.X.V) (volume6 X B.a i B.X.V) 0; rw [sub_zero,sub_zero] at ht'; apply (ht'.trans (add_le_add (hg.trans F.cover0) (hl i))).trans; linarith only
     rw [B.hi_f]; nlinarith only [mul_le_mul_of_nonneg_right V.disk hT.le, mul_le_mul_of_nonneg_right hC' hT.le,hT]
   · have hc': (B.fuel)⁻¹ ≤ burst G B.S.patch.L B.x := burst_h B.H.laws.intake.window.2; have hu0 := (inv_pos.mpr B.hot).le.trans hc'
     have hf := V.o.large; unfold tongs Baffle.screen
     exact ⟨by positivity, by rw [abs_of_pos hC,div_eq_mul_inv,mul_comm _ (5*V.o.a*B.X.t+_)]; exact mul_le_mul_of_nonneg_left hc' (by positivity)⟩ -- hC? cap pos
   intro a; simpa only [C6,Function.comp_apply,B.j1] using! H.horizon a
end Barque
end YM.PhysicalNext.Repeat.Sanction
