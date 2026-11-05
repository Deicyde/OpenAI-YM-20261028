import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Gush
import YM.UVNext.COUPLING_RESET.Advance
/-!
# Width request after L

Ret public stencil. Combine Coupler y beta with Sector Pupil on *true* λ. Distinct from permission in Stake (another budget b).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew Pot Push.AbsoluteSums
    AnalyticNext.ConnectedActivity Milk Coffer Grid
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {x y W a e L C u d ε η g b : ℝ} {p q : Pilot G S x} {v : Dyed G S}
structure March (J : ChartRatio G) (P : Teller G) (D : Patch) (W width x : ℝ) : Prop where
  boom : 0 < width*fiery G x D.L
  size : 4*(width*fiery G x D.L)<J.radius
  ride : 2*(width*fiery G x D.L)< firstRadius G
  eligible {c f : Side} (S : StepData c f) (T : Tube G S) : S.patch=D → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
     Boosted T P x ∧ ∀ (L : Lantern G S) (U : Allocation G S x W) (β : ℝ),L.hood=width*fiery G x D.L → 0<β → Coupler T L J U β
lemma enlarge (J : ChartRatio G) (hJ : LocalRatio J) (P : Teller G)
    (Q : Patch) (hB : Q.Branches P.bind G) (W : ℝ) (hw : 0<W) :∃ L : ℝ,0<L∧ ∀ d≥L,∀ᶠ x in atTop, March J P Q W d x:= by
  obtain ⟨L,E,hL,he,H⟩:= sponsored_permit P J hJ Q hB W hw
  refine ⟨L,hL,fun d hf=>?_⟩; have hT : Tendsto (fun x=>d*fiery G x Q.L) atTop (nhds 0):= by simpa [Rates.allowance,Rates.pieces] using! (Rates.slow G Q).const_mul d
  filter_upwards [H,booster Q P hB,hT.eventually (gt_mem_nhds (show 0<J.radius/4 from by have h:=hJ.patch; positivity)),hT.eventually (gt_mem_nhds (show 0<firstRadius G/2 from half_pos (first_pos _)))] with x hx hp h he
  obtain ⟨hg,hk,_,_,H⟩:=hx; have hm : L*fiery G x Q.L ≤ d*fiery G x Q.L:= mul_le_mul_of_nonneg_right hf (temp_nonneg _)
  have hn := hk.trans_le hm; have hi' : 4*(d*fiery G x Q.L)<J.radius:= by change d*fiery G x Q.L < _ at h; linarith only [h]
  have hg' : 2*(d*fiery G x Q.L) < firstRadius G:= by change d*fiery G x Q.L < _ at he; linarith only [he]
  refine ⟨hn,hi',hg',fun {c f} S T hS he ht => ?_⟩
  refine ⟨hp S T hS he ht,fun F U β hf' hβ A k V hh=>?_⟩
  obtain ⟨_,_,hv⟩:= H c f S T hS he ht; have hj:= ((hv _ k.wood k.tag V U F.χ).2 hh β hβ).1
  rw [← Q_endpoint,← mean_endpoint,hf']
  refine ⟨hj.nativePos,hβ,(meanLog_cont _ _ _ _ _ _ _ _ ht hn hg').measurable,?_,hJ,hn,hi'⟩
  intro u hu hb i; obtain ⟨g,ht,h,h'⟩:=hj.core u hu hb i; exact ⟨g,ht.trans hm,h,h'⟩
structure Granite (J : ChartRatio G) (P : Teller G) (D : Patch) (W L ε y : ℝ) : Prop where
  permits : March J P D W L y
  gallery : AnalyticBridge.Annulus1AD.Seen P D.L W L y
  attic {c f : Side} (S : StepData c f) : S.patch=D → DeepDoors P S L W y
  scenic : Beacons P D W ε y
lemma excels (J : ChartRatio G) (hJ : LocalRatio J) (P : Teller G) (Q : Patch) (hQ : Q.Branches P.bind G) (W : ℝ) (hC : Aff.Reserve P C) (hP : Jewels.wedge P C Q.L) (hW : 0<W) (hw : Jewels.Wedge P C W) :
    ∃ L ε : ℝ,0<L ∧ 0<ε ∧ ∀ d≥L,∀ᶠ x in atTop, Granite J P Q W d ε x:= by
  obtain ⟨L,hL,h⟩:= enlarge J hJ P Q hQ W hW
  obtain ⟨u,hu,hv⟩:= AnalyticBridge.Annulus1AD.started W P Q.L hW
  obtain ⟨ε,ht,hE⟩:= torch hC Q hQ hP W hW hw
  obtain ⟨g,hg,hA⟩:= distant_links Q P W hW
  refine ⟨max L (max g u), ε, hL.trans_le (le_max_left ..),ht,fun d hD=>?_⟩
  have hl : g≤d:= (le_trans (le_max_left ..) (le_max_right L (max g u))).trans hD
  filter_upwards [h d ((le_max_left ..).trans hD), hA,hv d ((le_trans (le_max_right ..) (le_max_right L (max g u))).trans hD), hE] with x hx hJ hV he
  refine ⟨hx,hV, fun {c f} S hS F T hT hh A V p Y i h ht=>?_,he⟩
  refine (hJ S T hS hT hh A F V p Y i h ht).trans ?_; rw [hS];exact mul_le_mul_of_nonneg_right hl (temp_nonneg _)

lemma ballot (h : Granite v.ratio P S.patch W L ε x) (hh : Chips v P W x) (ht : 100*(1+radiusB x) ≤ c.val) (hl : noises v u x) (hu : 0<u) (hL : Bid.Larger (G:=G) S) (he : 0≤ ε) (hV : ∃ H K,Aff.Alongside H K v.things) (hM : v.arc=L*fiery G x S.patch.L) :
    Pupil v x W (ε*fiery G x S.patch.L/coupling v.source.beta) u:= by
  refine ⟨div_nonneg (mul_nonneg he hh.lives.le) (coupling_pos hh.beta).le,hu,fun p hp=> ?_,?_⟩
  · rw [← Q_endpoint];exact (hl p hp).taxes
  obtain ⟨H,K,hk⟩:=hV
  have hx : Lift.Booth P S v.things:= by
    -- see Turbine proof
    obtain ⟨i,j,o,p,h₁,h₂⟩:=hk.budgets
    exact ⟨hh.boost.funded,H,K,i,j,o,p,h₁,h₂,hk.inbound,hk.outbound,hk.old,hk.new,hk.together,hk.sails⟩
  intro p i hs hy
  exact putAway v W hh.heated h.scenic (h.attic S rfl) hM.ge hh.boost.funded hh.arc_pos hh.beta hh.lives (le_trans (by decide : 2 ≤ 120) hh.boost.produced.scale) ht hL hk hx p i hs hy
end YM.PhysicalNext.InteractingRank.Pump
