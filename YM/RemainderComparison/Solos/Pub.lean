import YM.RemainderComparison.Solos.Font
import YM.RemainderComparison.Typeface.Cards
/-!
# The humane dominator
 Needed only for uniform integrability near equality F.B.Flags. For all other uses
 preserve the real rendered leaves. `weight` is before probe restriction.
 Honors support, gauges and flags. Don't require a cost summable over tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Solos
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {θ ι : Type} {R₀ : θ→Type*} [∀ i, NormedAddCommGroup (R₀ i)] [∀ i,NormedSpace ℝ (R₀ i)]
variable {α:Type*}{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Sleet Serif Typeface
variable (M:ι→Portrait R α) (y:α)
include H
lemma proper (i: Wing) : UsesFinal R.p.threshold (i.support R) (i.qualifies R) ∧ (∀ v U,i.qualifies R (Lattice.gauge v U)= i.qualifies R U) ∧ MeasurableSet {x| i.qualifies R x} :=by
   cases i with
   | logKey i=>
       refine ⟨fun U V hu ht=>?_,fun t U=>?_,(healthy_closed _ _).measurableSet⟩
       · change (Healthy R.p.threshold ((R.activities.reg i).support) U)=_; refine propext ?_; change Healthy _ _ _↔Healthy _ _ _; unfold Healthy; unfold Wing.support at ht; rw [Finset.disjoint_iff_inter_eq_empty,Finset.disjoint_iff_inter_eq_empty,ht]; -- ht?
       change Healthy _ _ _=Healthy _ _ _; simp [Healthy]
   | gasKey i=>
       exact ⟨Work.H03.eligible_reads _ _ (H.laws.intake.cap.labels.forced.reads_test _),fun t V=> propext (Work.H03.eligible_gauge R.p.threshold _ _ _ (H.laws.intake.cap.labels.forced.symtest i t V)),Work.H03.eligible_measurable _ _ (H.laws.intake.cap.labels.forced.meas_test i)⟩

def tart (i:ι):Leaf R where
    turn:=(M i).wing
    ingredient:=fun U=> if (M i).wing.qualifies R U then (M i).weight else 0
    scopedR:=fun U V h hp=> by dsimp only; rw [(proper H _).1 _ _ h hp]
    grant:=fun U hv=> by by_contra! he; simp [he] at hv
    blank:=(brand M y i).blank
    weight:=(M i).weight
    earn:= fun V=> by split; rename_i h; exact le_of_eq (Real.norm_of_nonneg ((brand M y _).profit)); rw [norm_zero]; exact (brand M y i).profit
    glows:=fun t U=> by dsimp only; rw [(proper H _).2.1]
    borel:=Measurable.ite (proper H _|>.2.2) measurable_const measurable_const

lemma agent (z:α)(U:Config G f)(i:ι) : ‖(brand M z i).ingredient U‖ ≤ ‖(tart H M y i).ingredient U‖:=by
    unfold tart; dsimp only; split
    next=> rw [Real.norm_of_nonneg (show 0 ≤ (M i).weight from (brand M z i).profit)]; exact (brand M z i).earn U
    next h=> simp only [not_not.mp (mt ((brand M z i).grant _) h),le_refl]
local notation "RT" z=> brand M z
local notation "DT" => tart H M y
variable (X:Coat T F) -- edit
lemma iconic (i:Drums (brand M y) S) (V: Coat T F) (v : Directions G f) (a:ℝ) (x:α): ‖(team (brand M x) i).paidU V a v‖ ≤ ‖(team (tart H M y) i).paidU V a v‖:=by
    have ht {M : ι→ Leaf R}(i:Drums M S): ‖(team M i).paidU V a v‖=∏ j∈i.val, ‖(M j).paidU V a v‖:= by unfold Team.paidU; rw [norm_prod]; unfold team; dsimp only; rw [prod_image]; exact fun m hm j hj hh=> i.prop hm hj (show sign M S m= sign M S j from by unfold Palette.sign; rw [hh])
    rw [ht,ht]; exact prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> by unfold Leaf.paidU Leaf.fond; rw [norm_mul,norm_mul]; exact mul_le_mul_of_nonneg_right (agent H M y x _ j) (norm_nonneg _))

variable (i:Drums (brand M y) S) (z:α) (I : Finset (Bond f))
lemma balcony (p:Molecule S) (V: Coat T F) (v : Air f G) : ‖(team (brand M z) i).floret V p W a Ñ (Matter.own p) m v‖ ≤ ‖(team (tart H M y) i).floret V p W a Ñ (Matter.own p) m v‖:=by
   unfold Team.floret; rw [Palette.label, Palette.label]; by_cases he:i.reach⊆p
   · rw (config:={transparency:=.default}) [if_pos he] ; rw (config:={transparency:=.default}) [if_pos he]; rw [norm_mul,norm_mul]; exact mul_le_mul_of_nonneg_right (iconic H M y i ..) (norm_nonneg _) -- defeq i type split?
   rw (config:={transparency:=.default}) [if_neg he]; try rw (config:={transparency:=.default}) [if_neg he]
lemma pend (p:Molecule S) (U:Config G c) (v:F.Slice G×Air f G) : ‖(team (brand M z) i).carat I X U r Q.table p W o.a Q.halo v‖ ≤ ‖(team (tart H M y) i).carat I X U r Q.table p W o.a Q.halo v‖:=by
   unfold Team.carat Team.chimes; rw [norm_mul,norm_mul]; exact mul_le_mul_of_nonneg_left (balcony H M y i z p ..) (norm_nonneg _)
end YM.RemainderComparison.Solos
