import YM.RemainderComparison.Placement.Pose
/-! # Exact travels. Masks included. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Placement
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus Sienna Fare
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics
open AnalyticBridge VerifiedReset Next.Scheduling Extra.Iteration Song
variable {G : Gauge} {f c F C: Side}{P:Teller G} {q e j k:ℕ}
variable {ι:Type} [Countable ι] {α:Type*}{A:ℝ}
variable (R:Rep G f)(R':Rep G F)
set_option quotPrecheck false
local notation "R_"=> Placement.file R e ι
local notation "Rh"=> Placement.file R' e ι
local notation "p"=> R.p
variable (v:α) (D:ι→ Tile G α q e A) (o o':ι→Site f)(d:ι→Site F)
variable (hp:0 < R.beta) (hg:0<R'.beta)
local notation "W" j:max=> Placement.plants R v D hp j
local notation "M₀" => Placement.plants R v D hp o
local notation "M₁" => Placement.plants R v D hp o'
local notation "M₂"=> Placement.plants R' v D hg d
variable (i:ι)(j:Site f)(π:R.activities.Moves 1 j)
lemma arrived (V Q:Leaf R) (h:V.turn=Q.turn)(ha:V.ingredient=Q.ingredient)(hb:V.weight=Q.weight): V=Q:=by
   cases V; cases Q; congr! -- perf inspect
lemma wings_sig : (M₀ i).wing=Wing.logKey (Placement.sign (o i,i)):= (Placement.planted R v D hp o i).appearance
variable {a:α}
lemma footprint_real : (M₀ i).wing.support (Placement.file R e ι)= neighbors e (o i):=by
    rw [wings_sig]; change ((Placement.file R e ι).activities.reg _).support=_; rw [(Placement.facts R e _).1]; rfl
lemma augments : Injective (fun j:ι=> (M₀ j).wing):= by
    intro i j h; change (M₀ i).wing=(M₀ j).wing at h; simp_rw [Placement.wings_sig] at h; exact congr_arg Prod.snd (Sum.inr_injective ((Placement.numbers ι f).symm.injective (Wing.logKey.inj h)))
lemma arrival (hz: o' i= o i + j) (a:α) : Typeface.brand M₁ a i= Leaf.route (Placement.movement R e ι 1 j π) (Typeface.brand M₀ a i) := by
    have he:= Placement.wings_sig R v D o hp i -- arg order
    have hh:= Placement.wings_sig R v D o' hp i
    let f:= M₀ i
    let u:= M₁ i
    let w:= Placement.movement R e ι 1 j π
    have hp : o' i = affine 1 j (o i):= by rw [hz]; simp [Lattice.affine]
    apply Placement.arrived
    · change u.wing=Wing.labelRoute w f.wing
      change f.wing=_ at he; change u.wing=_ at hh
      rw [hh,he]; change Wing.logKey _=Wing.logKey _; rw [show w.ep _=_ from Placement.shifted R e ι 1 j π (o i,i), hp]; rfl
    · rw [Typeface.photo, Typeface.photo]; change (u.angle a).ingredient= (f.angle a).ingredient∘ pull 1 j
      have h(a) : (u.angle a).ingredient= _:= (Placement.planted R v D ‹_› o' i).inputs a
      rw [h,(Placement.planted R v D ‹_› o i).inputs]; funext U; rw [hp]; dsimp only [Function.comp_apply]; have hx:= Turn.vigor 1 j U R.p.threshold (Turn.circle_wind 1 j (o i) e)
      by_cases hn:Healthy R.p.threshold (neighbors e (o i)) (pull 1 j U)
      · rw [masked_eq _ _ _ _ hn,masked_eq _ _ _ _ (hx.1 hn)]; exact (Tile.translated ..).symm
      rw [masked_ne _ _ _ _ hn,masked_ne _ _ _ _ (mt hx.2 hn)]
    exact (Placement.planted R v D ‹_› o' i).earnings.trans (Placement.planted R v D ‹_› o i).earnings.symm
-- hpull orientation sem. No stake estimation yet.
open Further.PhysicalPeriodLimitF933 Macrame
variable {hc : F.val=f.val*k}(hm:f.val>4)(hn:R.p=R'.p)
set_option quotPrecheck false
local notation "χ"=> Macrame.splitter (divides hc)
local notation "ξ"=> Macrame.normal (divides hc) hc
include hm hn
variable (he:o i= Macrame.splitter (Deck.divides hc) (d i))
include he
lemma filing : (M₀ i).wing.support R_= ((M₂ i).wing.support Rh).image (χ) ∧ ∀ (a:α) (V:Config G f), (Typeface.brand M₀ a i).ingredient V= (Typeface.brand M₂ a i).ingredient ((ξ).links V):=by
    have hp' : neighbors e (o i)=(neighbors e (d i)).image (χ):=by rw [he]; exact Deck.inclined hc e (d i) -- inspect
    refine ⟨?_,fun a V=> ?_⟩
    · rw [Placement.footprint_real,Placement.footprint_real]; exact hp'
    let T : Config G F:= (ξ).links V
    simp_rw [Typeface.photo]; change ((M₀ i).angle a).ingredient V=((M₂ i).angle a).ingredient T
    rw [(Placement.planted R v D hp o i).inputs,(Placement.planted R' v D hg d i).inputs,hn]
    have hV: Healthy R'.p.threshold (neighbors e (d i)) T↔ Healthy R'.p.threshold (neighbors e (o i)) V:=by rw [hp']; exact Deck.vigor hc V hm ..
    by_cases ht:Healthy R'.p.threshold (neighbors e (d i)) T
    · rw [masked_eq _ _ _ _ (hV.1 ht), masked_eq _ _ _ _ ht, he]; unfold Tile.read RG.Atom.unmasked RG.Slot.atSite; rw [(show expandAt (d i) T= _ from (ξ).expansion (d i) V)] -- check
      rfl
    rw [masked_ne _ _ _ _ (mt hV.2 ht),masked_ne _ _ _ _ ht]
end YM.RemainderComparison.Placement
