import YM.RG12.Shadows.Medal
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
open March Daisy Daisy.Charity Greenbelt Circlet Cub Next.Foundations Planned.PrimaryIntegral295 Labels Bid
-- Given all actors ready prove stencil8 hF. Helm s.K root support geometry.
variable {P:Teller G}{c f:Side}{S:StepData c f}{T:Tube G S}
    {B B':BudgetPoint}{Y:Support c}{K:Support f}{w μ x C':ℝ}{R:Rep G f}{p j n m k:ℕ}{L:Side}{Q:ConnectedActivityE6.Target G P}{o:ConnectedActivityE6.Target.Order G w}
variable {d A t C z r η v b Y' q M:ℝ} {C₀:Libretto G n}
variable (H:Cash w x μ L Q o C T R)(U:Leaf R)(i:ℕ)(hx:U.turn=.logKey i)(D:Record)(κ q':Chi)(ε:ℝ)(hN:Captain H p C' d v t A b r M q m Chi.canonical)(hR:Herd H hN.conduit A M m) (L':Config G f→ℝ)(h':R.p.Regular (R.activities.reg i).support L') (hm:U.ingredient= masked R.p.threshold (R.activities.reg i).support L')
    (hp:Plays C₀ D B R.p P T x)(hB:B.B= radiusB x)(hn:B.order≤p)(hk:coverNumber B.B (plate H i).support≤ B.B)
local notation "qL"=> Chi.canonical
local notation "f!"=> Charity.matin U H (Brim.icon H i) (qL)
local notation "g!"=> fun V:Config G c=> Mercury.groves H i D κ q' ε V L'
open YM.RG12 YM.RG12.Spins
-- one pre-presentation cost G simple? Fd localSection
lemma OvPay (m:ℕ) (l:((Labels.frames G).level m).Index):∃ C:ℝ,0 ≤ C∧ ∀ f o v,‖v‖≤1→Offset.Through 3 (Spins.drawing (localSection G m) (o:Site f) l) v C:= uniform (localSection G m) l
protected def stair (m:ℕ)(l:((Labels.frames G).level m).Index):= Classical.choose (OvPay m l)
include hm hx hp hB hN hR hn hk h'
lemma crown9 {F:ℝ}(hw:U.weight ≤ F){m:ℕ}{a: ((Labels.frames G).level m).Index}(he:(((Labels.frames G).level m).grades a).2=2) {η:ℂ→L[ℝ]ℝ}(hη:‖η‖≤1)(hL:L'=η∘ hills R (d:=m) a)
    (hM:Medal P L C₀ B.power D κ w o Chi.canonical F (Sanction.stair m a) z x) (l k:Directions G c)(hl:B.dirBound (plate H i).site l)(hv:B.dirBound (plate H i).site k)(hP:‖l‖≤canopyW G L B.power x)(hh:‖k‖ ≤ canopyW G L B.power x):
    ‖leftDerivs (f!) [l,k] 1-leftDerivs (g!) [l,k] 1‖ ≤ z:=by
  let X:= (localSection G m); let U₀:= Spins.drawing X (0:Site f) a; let L₀ : Directions G f→ℝ:= η∘ U₀
  have hC:= Classical.choose_spec (OvPay (G:=G) m a)
  have hg:2≤ n:=by have h:= B.order_ge; rw [←hp.rehearsed.test]; omega
  apply stands H U i hx D κ q' ε hN hR L' h' hp hn hg _ rfl
  intro F' a'
  let A : Slab G c 2:= [l,k].get
  have h0 :∀ y:Directions G f,L' (increment 1 y)=R.p.threshold⁻¹^2*L₀ y :=by
     intro y; rw [hL]; change η (Push.Local.presented X (0:Site f) R.p.threshold (Place.copy _ a) (increment 1 y))=_; rw [Spins.draw X (0:Site f) a,he,η.map_smul]; change (R.p.threshold^2)⁻¹*_= _; rw [inv_pow]; rfl
  apply hM c f S T H.laws.data.funds Q μ R C H i U q' ε B hx hw hB rfl hp hk L' L₀ h' hm _ _ h0 A _ _ F' a'
  · intro y hy; have hu:=linear_through η (hC.2 _ (0:Site f) y hy) hη; rw [one_mul] at hu; exact hu
  ·
    have hu:= hC.2 _ (0:Site f) 0 (by simp)
    rw [show fderiv ℝ L₀ 0=(η.comp (fderiv ℝ U₀ 0)) from (η.hasFDerivAt.comp 0 (hu.smooth.differentiableAt (by norm_num)).hasFDerivAt).fderiv,show fderiv ℝ U₀ 0=0 from by
         have hX:=no_low X (0:Site f) a (Next.Foundations.valuation G m) (q:=1) (by rw [he]; norm_num); rw [← norm_eq_zero, ← norm_iteratedFDeriv_one,hX,norm_zero]]
    ext; simp
  · intro j; fin_cases j <;> first| exact hl| exact hv
  intro j; fin_cases j <;> first| exact hP|exact hh
end YM.PhysicalNext.Repeat.Sanction
