import YM.RemainderComparison.Valse.Leaves
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Valse
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open PhysicalNext.Repeat Lotus Merge Palette Turn
open Mosaic
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {ι ι' δ : Type} {G : Gauge} {c f : Side} {S : StepData c f} {s : Signed} {b : Site c}
    {F : Forest S.ratio} {P : Teller G} {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
    {W α μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {L : Side}
    {R : Rep G f} (π : R.activities.Moves s (S.ratio.embed b)) (H : Cash W α μ L Q o C T R)
variable (M : ι→Leaf R)(N:ι'→Leaf R)(u : ι≃ι')
variable (B: Turns π M N u)
namespace Turns
local notation "D₁"=> drums π M N u B
include B H
-- Adapt tours. F-order, fixed map. (no changes to Bush).
lemma hikes (h : Parked s b X Y) (hχ : Y.χ=X.χ) (hK : Y.width=X.width) (he : Y.k=Channels.ticket s b X.k)
    (hα : X.x=α) (hw : X.width=o.K) (hx : X.manifest) (hy : Y.manifest) (i : Molecule S) (l : Finset ℕ) (w:Lyric.Drums M S):
    (team M w).tithe Y l W o.a Q.table Q.halo i=(team N (D₁ w)).tithe X (π.kp.finsetCongr l) W o.a Q.table Q.halo (caravan R π i):=by
  let g := (team M w).into Y W o.a Q.table l Q.halo i
  have hp : MeasurePreserving (fun u : F.Slice G× Air f G => (glide s b F u.1, exhale s b X.V S u.2)) ((F.order G).prod X.dice) (((Locations.forest s b F).order G).prod Y.dice) := (forest_toll s b F G).prod (h.preserving H.laws.intake.ready (H.laws.data.localP F X hα hw hx).sails.fullC)
  have hm : Measurable g := (team M w).crystall Y l ((h.x.trans hα).symm ▸ H.laws.intake) (show ShellAccess S G Y.x W Y.width o.γ from (by rw [h.x,hα,hK,hw]; exact H.laws.data.access)) Q.table_exists ..
  unfold Team.tithe; rw [← Pond.reception hp g hm]; apply integral_congr_ae; filter_upwards with p
  obtain ⟨u',z⟩:=p; let X' := X.wrapY u'; let Y':=Y.wrapY (glide s b F u')
  exact reckons π H M N u B (X:=X') (Y:=Y') ⟨⟨h.seeds,h.x,h.v⟩,hχ,hK,he,rfl⟩ z hα hw hx hy l i w
lemma marches (h : Parked s b X Y) (hχ : Y.χ=X.χ) (hK : Y.width=X.width)
    (hα : X.x=α) (hw : X.width=o.K) (hx:X.manifest) (hy:Y.manifest) (i:Molecule S)(l:Finset ℕ)(w:Lyric.Drums M S) :
    (team M w).steep Y l W o.a Q.table Q.halo i=(team N (D₁ w)).steep X (π.kp.finsetCongr l) W o.a Q.table Q.halo (caravan R π i):=by
  unfold Team.steep Pond.likely; apply congr_arg; rw [← Equiv.sum_comp (S.withinChoice s b).symm]; refine sum_congr rfl fun v _=> ?_
  exact hikes π H M N u B (X:=X.taggedL v) (Y:=Y.taggedL ((S.withinChoice s b).symm v)) ⟨h.seeds,h.x,h.v⟩ hχ hK rfl hα hw hx hy i l w
lemma trumpet (hv : Y.V=pull s b X.V) (hx : Y.x=X.x) (hχ : Y.χ=X.χ) (hK : Y.width=X.width) (hα : X.x=α) (hw:X.width=o.K) (p : Molecule S)(w:Lyric.Drums M S) :
    (team M w).bloom Y W o.a Q.table Q.halo p=(team N (D₁ w)).bloom X W o.a Q.table Q.halo (caravan R π p):=by
  unfold Team.bloom; rw [Turn.accounting hv hx R π]; split
  · let Z':= caravan R π p; let A:=planted Y p; let D:=planted X Z'
    have h : Parked s b D A:= by
      refine ⟨?_,hx,hv⟩; unfold A D planted preps; dsimp only
      rw [Turn.mark R π p,hx,hv]; apply congrArg (Stores.mk _ _); ext i; exact (Turn.toured s b ..).trans (Turn.atF s b D.seeds i).symm
    have hl: Matter.own Z'=π.kp.finsetCongr (Matter.own p):= (Turn.given _ _ _).mpr (Turn.chart R π p); rw [show Matter.own (caravan R π p)= _ from hl]; exact marches π H M N u B h hχ hK hα hw (planted_valid ..) (planted_valid ..) _ _ w
  rfl
open PhysicalNext.Repeat.Greenbelt
lemma chance (U:Config G c)(χ:Chi)(p:Molecule S)(w:Lyric.Drums M S) : act M H χ (pull s b U) p w=act N H χ U (caravan R π p) (D₁ w):=by
  apply likely_congr (orbitKey s b S); intro i
  let X:= prism T α χ o.K U (allot i)
  let Y:= prism T α χ o.K (pull s b U) (Locations.forest s b (allot i))
  rw [f_orbit]; exact trumpet π H M N u B (X:=X) (Y:=Y) rfl rfl rfl rfl rfl rfl p w
end Turns
end YM.RemainderComparison.Valse
