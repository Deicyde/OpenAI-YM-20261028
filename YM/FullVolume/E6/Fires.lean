import YM.FullVolume.E6.Convoy
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
variable {T: Tube G S} (X: Coat T F)
def tip : Air f G:= WithLp.toLp 2 (stand (voltage X))
lemma kickback_eq (β:ℝ)(w:Air f G): kickback X β w=(gStep β)⁻¹ • (w-tip X) :=by ext i; rfl
def cups (β:ℝ)(w:Air f G):ℝ := ((gStep β)⁻¹)^Module.finrank ℝ (Air f G) * lens₀ X.relating (kickback X β w)
set_option maxHeartbeats 300000 in
lemma tollway {β:ℝ}(hx:X.relating.PosDef)(hp:0<β)(gR : Air f G→ E)(h: Integrable gR X.dice):
     Integrable (fun w : Air f G=> cups X β w • gR (kickback X β w)) volume ∧ (∫ x', gR x' ∂X.dice)=(∫ w:Air f G,cups X β w • gR (kickback X β w)) :=by
    let e:= fun x=> lens₀ X.relating x; let v:= volume (α:=EuclideanSpace ℝ (Tubular f G)); let g x:= e x • gR x
    have hm : Measurable (fun x=> ENNReal.ofReal (e x)) := ENNReal.measurable_ofReal.comp (bulbB (S:=fun _ : Air f G=> X.relating) (fun _ _=> measurable_const) measurable_id)
    have he : Integrable g v:= by
        rw [dice, magnifies _ hx] at h; have h':= (integrable_withDensity_iff_integrable_smul' hm (ae_of_all _ fun x=> ENNReal.ofReal_lt_top)).1 h
        unfold g e; simpa only [e, ENNReal.toReal_ofReal (fullFuel X.relating _).le ] using h'
    let b:= (gStep β)⁻¹; have hb:0<b:= inv_pos.mpr (inv_pos.mpr (Real.sqrt_pos.mpr hp)); let t' :=b^Module.finrank ℝ (Air f G)
    have ha : 0<t':=pow_pos hb _; let hX(w):= t' • g (b • w); have hh : Integrable hX v:= (he.comp_smul hb.ne').smul _
    let K x:= -tip X+x; have hP : MeasurePreserving K v v:= measurePreserving_add_left _ _
    have hG(w): cups X β w • gR (kickback X β w)=hX (K w):=by
         unfold cups; rw [kickback_eq, mul_smul]; unfold hX K; rw [sub_eq_neg_add]
    simp_rw [hG]; refine ⟨(hP.integrable_comp hh.aestronglyMeasurable).mpr hh,?_⟩; unfold K; rw [integral_add_left_eq_self]
    unfold hX; rw [integral_smul, Measure.integral_comp_smul_of_nonneg _ g b (hR:=hb.le), smul_inv_smul₀ ha.ne', dice, magnifies _ hx, integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun x=> ENNReal.ofReal_lt_top)]; exact integral_congr_ae (ae_of_all _ fun z=> by dsimp only [g,e]; rw [ENNReal.toReal_ofReal (fullFuel _ z).le])
namespace Rotator
lemma suspected {η r q Y:ℝ}(h:Rotator P L η r q Y X): Allow X.relating (along S) (tubularPrice G L)
      (retain η r q) (q⁻¹/2) (1+payE η r q (tubularPrice G L)):=by
    have H:=h.scale
    exact ⟨H.census,Window.twin ..,H.weather.1,half_pos (inv_pos.mpr H.fuel), add_pos_of_pos_of_nonneg zero_lt_one H.disc,
     ((Control.increase (H.mate X.shutter) le_rfl (le_add_of_nonneg_left zero_le_one))).1,H.ground_C X.shutter h.cap⟩
end Rotator
end YM.ConnectedActivityE6.Lim
