import YM.AnalyticNext.QUARTIC_MATCH.Radius.Fruit
import YM.Extra.ITERATION_NO_LOSS.Kernels
import YM.Extra.MULTISOURCE_BOUNDS.Merger
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.Extra.MULTISOURCE_TRAJECTORIES.Trials
import YM.Further.QUANTUM_RATES_PORT.Accounts
import YM.Further.QUANTUM_RATES_PORT.Waves
import YM.Next.MAXWELL.Taxes
import YM.Next.WARD_BIN.LabelEst
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Necklace
import YM.PhysicalNext.GRADED_QUARTIC_RATE.Stamp
import YM.PhysicalNext.SAME_SERVICE_FRESH_DETERMINANT.Orders
import YM.Planned.RECIPE_STARTUP_PORT.Horizon
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Infinite
import YM.Progress.CLASSICAL_KIN_RECURSION.Delta
import YM.Push.ABSOLUTE_SUMS.Gas
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.LOOP_COEFFICIENT.Block.Optimize
import YM.Push.LOOP_COEFFICIENT.Resolution
import YM.Push.RELAY_DIFFERENCE.Attaching
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.RELAY_MARK.Span
import YM.Push.STRESS_FLUX.Low
import YM.Push.STRESS_FLUX.Matching
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free
import YM.UVNext.COUPLING_RESET.Reset

/-!
# Using whitened P in the vacuum calculation

Here & in Weaves use stage-1 proof shapes (Necklace, Discs) extracting just
the results about **vacuum** budget that don't need any claim of the
BodyGrant identity. Need this because the whitened calculation aid won't
in general have that identity on *these weights*. Apply the identity in
Payout/Rendering-style reasoning later on the actual Soft representation.
Perform on THAT Exposure, then whitelist (identified) orientation/path
properties for use here as needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph Thirst Display Display.Docking Display.Sew
     Flux Bid SectorNext.Vacuum Precision Baler
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x τ : ℝ} {L : Lantern G S} {T : Tube G S}
    {P : Teller G} {W V ι κ α β : Type} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] {u : W → Site c} {v : V→Site c} [Fintype ι] [Fintype α]

structure Veins (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (A : Boosted T P x) (hs : 25*radiusB x+30 ≤ R'.p.B) {o ℓ δ Λ η} (hR : R.Lawful o ℓ Λ δ η) (e M N d : ℝ) : Prop where
  cash : Holdings R' p T M N (e+1) d
  voyages s t : Nonempty (Voyage (unmarked R R' p A hs (blink S) hR) s t)
  realistic i A k V z : Sound ((p i).weight A k V z)

section creation
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (A : Boosted T P x) (hs : 25*radiusB x+30 ≤ R'.p.B)
    {o ℓ δ Λ η β s M l k m σ h y w : ℝ} (hR : R.Lawful o ℓ Λ δ η)
    {ν : Config G c→ℝ} {D : Allocation G S x w} {J : ChartRatio G}
    (E : α→ Rim R'.p.threshold G c)
    (he : Veins R R' p A hs hR k M l σ)
local notation "rb" => R'.p
local notation "X0"=> unmarked R R' p A hs (blink S) hR
local notation "G0"=> germ X0 A
local notation "F0"=> gruel X0 A (callsQuiet R R' p A hs hR (blink S))
local notation "H0"=> (fun i=> Sum.inl (scroll G0 i) : Glade c → Lining G (blank c) R'.p.threshold)
local notation "Y0"=> wingspan E (blank c)
local notation "V0" =>courtyard R R' p A hs hR E
local notation "Q"=> germinates R R' p A hs hR E
variable (θ : W→Site f) (u : W→Site c) (hθ : u=S.ratio.parent∘θ)
local notation "X"=> unmarked R R' p A hs hθ hR
local notation "H"=> germ X A
local notation "F"=> gruel X A (callsQuiet R R' p A hs hR hθ)
local notation "G1"=> wingspan E u
local notation "K"=> toRain (toRain F (fun i=> Sum.inl (scroll H i))) (witness G1)
include he
lemma v_genuine : ∀ i A k V y, Sound ((X i).lamp A k V y):=by
  rintro ((i|i)|i) A k V y; exact he.realistic ..; exact vouch _; exact i.elim
lemma v_worth_real (i : Club X) U : Sound (letter X (T:=T) i U):= Sound.money T (fun U' k V y=> Sound.prod _ fun i=> v_genuine R R' p A hs hR he θ u hθ i U' k V y)
lemma v_registrants : Background Q K:= by
  have hz i U: Sound (Value.Lifted.value (F i) U):= by unfold gruel foundering; dsimp only; split; exact v_worth_real R R' p A hs hR he θ u hθ i.val U; exact vouch 0
  have h₀ i:(F i).fires=quiet W:= Across.rises (callsQuiet R R' p A hs hR hθ) i.val.val
  have hW' (i) (U): Sound ((K i).value U):=by
    refine chirping (blanking h₀ (fun _=> rfl)) (fun _=>rfl) (chirping h₀ (fun _=>rfl) hz (fun i U=>?_)) (fun i U=> vouch _) i U
    change Sound (((scroll H _).glow R'.p.threshold).value U); rw [scroll_value]; exact vouch _
  obtain ⟨F',hF⟩:=toeMap R R' p A hs hR E θ u hθ
  have hW i U: Sound ((V0 i).value U):= hF.values i U|>.symm ▸ hW' _ U
  have hx : Background Q V0:= chairMap _ _ hF.quiet hW
  intro i U; refine Eq.trans ?_ (hx i U)
  symm; unfold Value.column; apply Fintype.sum_equiv F'; intro j
  simp_rw [hF.quiet,hF.fresh,true_and]
  have hh:(V0 j).inventory=(K (F' j)).inventory:= by rw [hF.inventory]; ext; simp
  have hv:(V0 j).extent=(K (F' j)).extent:=by rw [hF.extent]; ext; simp
  apply if_congr; rw [hh,hv]; exact hF.values j U; rfl
-- Carves on THIS mark stencil, through subsequent W:H data

def v_carves : Flux.Vac u Q:=⟨_,_,_,F,scroll H,G1,(fun i=> Across.rises (fun _=>callsQuiet ..) i.val.val), (fun _=>rfl),rim_b E u,v_registrants R R' p A hs hR E he θ u hθ⟩
-- Uses voyage(s) to construct Moves
lemma v_travelers (fR : Resin R R' p A hs hR ν E k y) (h : ∀ s i, Nonempty (R'.activities.Moves s i)) : ∀ s i,Nonempty ((Q).activities.Moves s i):=by
  refine transported _ _ (fun s i=> ?_) h
  obtain ⟨U⟩ := he.voyages s i
  obtain ⟨D,hK⟩:= fR.brings s i
  have hV:= U.rebuilt A
  have hx U : flags R'.p.threshold (U : Config G c)=(flags R'.p.threshold (pull s i U)).map (StepData.sendSites s i).toEmbedding:= dispatched ..
  have hW : Holy (U.orientation.exe) (pull s i) (StepData.sendSites s i) G0 G0:=by refine ⟨fun j=> (U.orientation.zone_covers j.val), fun j W=> (Voyage.tribute U A j.val W).symm⟩
  exact ⟨_,(hV.shuttered (hW.locked R'.p hx) hx).shuttered hK hx⟩
end creation
end YM.PhysicalNext.InteractingRank.Soft
