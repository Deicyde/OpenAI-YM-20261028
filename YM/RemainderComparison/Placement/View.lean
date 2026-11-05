import YM.RemainderComparison.Placement.Travel
/-!
# Local supports at aperture. Movement along fibers.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Placement
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus Sienna Fare
open Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics
open AnalyticBridge VerifiedReset Next.Scheduling Extra.Iteration Song Aria Seedlings BoxOf
variable {G : Gauge} {f c F C L: Side}{P:Teller G} {q e j k N u r:ℕ}
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
variable (i:ι)
variable {X:StepData c f}{T:Tube G X}{S:ConnectedActivityE6.Target G P} {s κ μ Γ β t :ℝ}{K:Target.Order G μ}
set_option quotPrecheck false
local notation "ξ"=> Mint.width S.halo (radiusB β) e
variable (V: Cash μ β t L S K Γ T (Placement.file R e ι))
-- footprint counted from actual root.Margin. Reader needs flag queries.This comes *through H* not directly constructor reset*. Shape Census on S.
lemma skyline : ¬ Sleet.cloudy (Placement.file R e ι) e (Placement.sign (o i,i)):=by
   rw [Sleet.cloudy,(Placement.facts R e _).1]; push Not
   intro x hx; exact (neighbors_mem ..).1 hx
lemma watching : V.supportP ((M₀ i).wing.badge X)⊆ neighbors (Mint.width S.halo (radiusB β) e) (X.ratio.parent (o i)):=by
   rw [wings_sig]; apply (Sleet.key_roof V e (Placement.sign (o i,i)) (Placement.skyline (e:=e) R o i)).trans
   rw [(Placement.facts R e _).1]; exact fun i h=>h
lemma revenue : Flues.candle M₀ v X i⊆ V.supportP ((M₀ i).wing.badge X):=by
   unfold Flues.candle; intro k hk; obtain ⟨y,hy,rfl⟩:= mem_image.mp hk; change X.ratio.parent y ∈ Matter.areas (Placement.file R e ι) T S.halo (radiusB β) ((M₀ i).wing.badge X)
   rw [Wing.badge_area]; exact halo_subset _ _ (mem_image_of_mem _ (mem_union_left _ hy))
lemma locates : X.ratio.parent (o i)∈ Flues.candle M₀ v X i:=by
    refine mem_image_of_mem _ ?_; change o i∈ (M₀ i).wing.support (Placement.file R e ι); rw [footprint_real]; exact (neighbors_mem ..).mpr (by simp)
-- x parent radius in stepped. archaic explicit.
variable (Q:Aria.Score V ι k) (b:Finset ι)(x:Site c)(π:R.activities.Moves 1 (X.ratio.embed x))
local notation "TS"=> Timbre.trumpets V
-- Score.None cannot have warrant.Power. prove ext.RN trees.
omit [Countable ι] in
def silent {R:Rep G f}(H: Cash μ β t L S K Γ T R): Score H PEmpty 0:=by
    refine ⟨fun _=>∅,fun i j _=>le_rfl,⟨fun i=>i.2.elim,fun i _ _=> isEmptyElim i.2⟩,fun _ _ _ h=> ?_⟩
    simp at h
omit [Countable ι] in
lemma quiet_score {R:Rep G f} (H:Cash μ β t L S K Γ T R) : Score.pose H 0 (Placement.silent H)= Timbre.trumpets H:=by
    cases e: Timbre.trumpets H with
    | mk P=> unfold Score.pose; simp_rw [e]; simp [Placement.silent,Score.wake] -- structure ext trouble.A
local notation "F'"=> Placement.movement R e ι 1 (X.ratio.embed x) π
variable (hs:∀ i'∈b,o i'= o' i'+ X.ratio.embed x) (he:∀ i'∈ b,separation (0:Site c) (X.ratio.parent (o' i')) ≤ u)
variable (hr: u+Deck.Mint.width S.halo (radiusB β) e≤r)
include hs he hr
lemma transports : Aria.Travel V M₀ 0 r (Placement.silent V) b M₁ x F' :=by
    refine ⟨fun n=>by unfold Score.wake silent; simp , fun i hi t=> Placement.arrival R v D o' o hp i (X.ratio.embed x) π (hs i hi) t, fun i hi=> ?_⟩
    have hh:= Placement.wings_sig R v D o' hp i; refine ⟨Placement.sign (o' i,i),hh,?_⟩
    have h := Placement.watching R v D o' hp i V; rw [hh] at h
    intro j hj; rw [neighbors_mem]; exact (separation_triangle (0:Site c) (X.ratio.parent (o' i)) j).trans ((add_le_add (he i hi) ((neighbors_mem ..).1 (h hj))).trans hr)
omit hs he hr
end YM.RemainderComparison.Placement
