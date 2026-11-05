import YM.MultiNext.VACUUM_STABILITY.Earning.Stage
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Fleet
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Passports

/-! # Close the optional component lookup values from rotated assembly

One color test and one rotation, both Resolve and vote. All support maps
work even for zero terms/on all masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Turn
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {s : Signed} {b : Site c}

section power
variable (U : Config G c) (s b)
lemma vigor {X Y : Support c} (t : ℝ) (he : Y=X.image (affine s b)) : Healthy t X (pull s b U) ↔ Healthy t Y U :=
  assign_guard (StepData.sendSites s b) ((display _ _ _).1 he) (fun _=> toured ..)
lemma all_moves (X : Activities G c) (p : BudgetPoint) (e : X.Moves s b) (i) : X.regularOccurrence p i (pull s b U)=X.regularOccurrence p (e.ep i) U := by
  unfold Activities.regularOccurrence; have hw := vigor s b U p.threshold (e.reg_support i)
  by_cases he : Healthy p.threshold (X.reg i).support (pull s b U)
  · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ (hw.mp he), e.valuesE]
  rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ (mt hw.mpr he)]
lemma validation {n : ℕ} (A : Atom G n) (x : Site c) (p : BudgetPoint) : A.placed p (translate b U) x=A.placed p U (x+b) := by
  rw [← pull_one]; unfold Atom.placed
  have hx : A.unmasked (pull 1 b U) x=A.unmasked U (x+b) := by unfold Atom.unmasked RG.Slot.atSite; simp_rw [expandAt_pull,pull_id,affine,Signed.act_one]; try simp
  have hp := vigor 1 b U p.threshold (show A.footprint (x+b)=(A.footprint x).image (affine 1 b) from pathFo b _ _ rfl _)
  by_cases he : Healthy p.threshold (A.footprint x) (pull 1 b U)
  · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ (hp.mp he)]; exact hx
  rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ (mt hp.mpr he)]
lemma skies {n : ℕ} (T : ℕ→Atom G n) (p : BudgetPoint) (i : Trans c) (r : ℝ) :
    translateValue p T r (pull s b U) i=translateValue p T r U (sky s b i) := by unfold translateValue; rw [Channels.channel_turn,validation]; rfl
lemma eclipsed (T : PathData G) (p : Clip) (R l : ℕ) (v θ : ℝ) (i : Pairs c) : pairValue T p v R l θ (pull s b U) i=pairValue T p v R l θ U (moon s b i) := by
  unfold pairValue; rw [channel_turn]; apply congr_arg
  let b':= offset s b i.1
  let y : Cell c:= (i.2.2.1,i.2.1)
  change pairTail T p R l v y (translate b' (pull (s*i.1) 0 U)) _=pairTail T p R l v (Channels.shift b' _ y) (pull (s*i.1) 0 U) i.2.2.2
  have he (V : Config G c) j : T.ellTerms y j (translate b' V)=T.ellTerms (Channels.shift b' _ y) j V := by unfold PathData.ellTerms RG.Slot.atSite; rw [← pull_one,expandAt_pull,pull_id]; simp [Channels.shift,affine]
  unfold pairTail; exact if_congr (and_congr Iff.rfl (translated_kept b' _ v p y.1)) (by rw [he,he]) rfl
lemma exposure (U : Config G f) (V : Config G c) (T : Tube G S) (x : ℝ) (R : Rep G f) (e : R.activities.Moves s (S.ratio.embed b)) (p : LogLetter c f) :
    expo T x R (pull s (S.ratio.embed b) U) (pull s b V) p=expo T x R U V (rotateStory s b S e.ep p) := by
  rcases p with p|p|p|p|p|p
  · exact congr_arg Neg.neg (all_moves s (S.ratio.embed b) U _ _ e _)
  · exact skies ..
  · exact skies ..
  · exact skies ..
  · exact eclipsed ..
  exact eclipsed ..
end power

def alarm (S : StepData c f) (s : Signed) (b : Site c) : Equiv.Perm (Panic c f) := Equiv.sumCongr
    (Locations.shiftFaces s (S.ratio.embed b)) (Equiv.sumCongr (StepData.sendBonds s b) (Equiv.sumCongr (StepData.sendBonds s b) (Equiv.sumCongr (StepData.sendSites s b) (StepData.sendSites s (S.ratio.embed b)))))
def windWarn (S : StepData c f) (s : Signed) (b : Site c) : Equiv.Perm (WarningAt c f) := Equiv.sumCongr (alarm S s b) (diagram s b S)

def logTurn (S : StepData c f) (s : Signed) (b : Site c) (e : Equiv.Perm ℕ) : Equiv.Perm (LogIndex c f) :=
    Equiv.sumCongr (rotateStory s b S e) (Equiv.sumCongr (rotateMini s b S) (rotationFuel s b S))
lemma logStory (T : Tube G S) (R : Rep G f) (e : R.activities.Moves s (S.ratio.embed b)) (i : LogIndex c f) (l B : ℕ) :
    roadway T R B l (logTurn S s b e.ep i)=(roadway T R B l i).image (affine s b) := by
  rcases i with i|i|i
  · exact space_roll _ _ _ _ e ..
  · exact sleeve_turn ..
  exact kindle_turn ..
lemma guard_map (p : Panic c f) : districts S (alarm S s b p)=(districts S p).image (affine s b) := by
  rcases p with i|i|i|i|i
  · exact Locations.start_map ..
  · exact pointers ..
  · exact pointers ..
  · change {affine s b i}=Finset.image _ {i}; simp
  change {S.ratio.parent (affine s (S.ratio.embed b) i)}=Finset.image _ {S.ratio.parent i}; rw [Locations.parent_map]; simp
lemma alarmStory (p : WarningAt c f) (l B : ℕ) : field_support S B l (windWarn S s b p)=(field_support S B l p).image (affine s b) := by
  rcases p with p|p
  · exact halo_pull _ _ _ _ _ ((display (StepData.sendSites s b) _ _).1 (guard_map (S:=S) p))
  exact town_turn ..

namespace Tuned
variable {F : Forest S.ratio} {P : Teller G} {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
    (h : Tuned s b X Y) {η A' r Q : ℝ} {L : Side} (hx : Port P L η r Q A' X) (hy : Port P L η r Q A' Y)
    (hp : P.Funds S T) {W C : ℝ} (ht : ShellAccess S G X.x W X.width C)
    (p : LogIndex c f) {R : Rep G f} (e : R.activities.Moves s (S.ratio.embed b)) (w : Directions G f)
    {Ñ : ChartRatio G} (hn : LocalRatio Ñ) (a : ℝ) (hu : 0 < a*X.t) (he : 4*a*X.t<Ñ.radius)
include h e
lemma earned_bag (j : ℕ) : Y.bag R a (wheels (S:=S) s b X.V w) j=X.bag R a w (e.kp j) := by
  unfold bag; rw [h.completed,e.valuesK,h.toParked.aligned.2.1]; apply congr_arg; apply h.imposes
  exact h.plazas ((display (StepData.sendSites s b) _ _).1 (enlarged _ _ _ _ _ _ (e.forced_support j)))
lemma earned_inhale (j : LogLetter c f) : Y.inhale R a (wheels (S:=S) s b X.V w) j=X.inhale R a w (rotateStory s b S e.ep j) := by
  unfold inhale; rw [h.completed,h.v,h.x,h.toParked.aligned.2.1,exposure s b _ _ T _ R e]; apply congr_arg
  exact h.imposes _ (h.plazas ((display (StepData.sendSites s b) _ _).1 (space_roll s b _ _ e _ _ j))) w
include hp
lemma heard_winds (p : WarningAt c f) (l : Finset ℕ) (W : ℝ) :
    Y.detect (wheels (S:=S) s b X.V w) W a R l p=X.detect w W a R (e.kp.finsetCongr l) (windWarn S s b p) := by
  have hb : S.patch.Branches S.kernel G:= funds_branch hp
  unfold detect; rcases p with p|p
  · change Y.mayor _ W a R l p=X.mayor _ W a _ _ (alarm S s b p)
    have hh := (display (StepData.sendSites s b) _ _).1 (guard_map (s:=s) (b:=b) (S:=S) p)
    unfold mayor; rw [h.toParked.aligned.2.1,h.seeds]; apply if_congr (show mandatory (Locations.book s b X.seeds) X.B p ↔ mandatory X.seeds X.B (alarm S s b p) from not_congr (assign_guard (StepData.sendSites s b) (Locations.dome_map s b X.seeds (300*X.B)) hh)) rfl
    ·
      rw [h.imposes _ (O:=X.plaza (halo X.B (districts S (alarm S s b p)))) (h.plazas ((display (StepData.sendSites s b) _ _).1 (halo_pull s b _ _ _ hh)))]
      apply congr_arg; apply congr_arg₂ (·-·) _ rfl; unfold rawStorm;  rw [h.completed,h.v,h.χ,h.way,h.toParked.aligned.1]
      rcases p with i|i|i|i|i
      · exact movingMark ..
      · exact barNoise s b X.k (X.input w) hb ..
      · exact portPin s b X.k (X.input w) hb _
      · exact portSite s b X.k (X.input w) hb _
      exact accepts_cost ..
  change Y.aura _ _ p=X.aura _ _ _
  have hh (i) : i∈Y.plaza (Y.seeds.dome (304*Y.B)) ↔ diagram s b S i∈X.plaza (X.seeds.dome (304*X.B)) := by rw [h.seeds,h.toParked.aligned.2.1]; exact h.plazas (Locations.dome_map s b X.seeds _) i
  exact if_congr (and_congr (h.toParked.eligible p) (not_congr (hh p))) (congr_arg (·-1) (h.cone_eq a w p)) rfl
include ht hx hy hn he hu
omit e in
lemma minis (i : Miniature c f) (β : ℝ) : Y.Short (wheels (S:=S) s b X.V w) Ñ β a i=X.Short w Ñ β a (rotateMini s b S i) := by
  have hhM : Y.μ=wheels (S:=S) s b X.V X.μ := congr_arg (erect G) ((h.means hp ht).trans (tapeRev s b X.V X.μ).symm)
  rcases i with p|p|p
  · obtain ⟨q,p⟩:=p
    have hm : Inside (rowSite S (q,p)) Y.seeds (200*Y.B) ↔ Inside (rowSite S (s*q,wind s b S q p)) X.seeds (200*X.B) := by
      unfold Shell.Inside; rw [h.toParked.aligned.2.1,h.seeds,Locations.dome_map,← center_meets]; rfl
    change Y.speck _ _ _ (q,p)=X.speck w β a (s*q,wind s b S q p); unfold speck; rw [if_congr hm rfl rfl]
    dsimp only; split
    next hx=> rfl
    next h' =>
      have hv i : i∈Y.booth (rowSite S (q,p)) ↔ diagram s b S i ∈ X.booth (rowSite S (s*q,wind s b S q p)) := by
        refine h.plazas ((display (StepData.sendSites s b) (Animals.neighbors Y.B (rowSite S (q,p))) _).1 ?_) i; rw [h.toParked.aligned.2.1, show rowSite S (s*q,wind s b S q p)=_ from center_meets (S:=S) s b (q,p)]; exact circle_wind ..
      rw [h.imposes _ (O:=X.booth (rowSite S (s*q,wind s b S q p))) hv, h.light_eq hp ht, hhM,h.ex hp ht]
  · change Y.undercurrent p=X.undercurrent (diagram s b S p); unfold undercurrent; rw [h.seeds,h.toParked.aligned.2.1,h.condensate hp hx hy]; exact if_congr (travels ..) rfl rfl
  change Y.solo _ _ _ p=X.solo _ _ _ (diagram s b S p); unfold Coat.solo; rw [h.gentry_eq a w p hn hu he, h.seeds,h.toParked.aligned.2.1]
  exact if_congr (and_congr (not_congr (h.plazas (Locations.dome_map s b X.seeds _) p)) (h.toParked.eligible p)) rfl rfl

lemma carried (z : Air f G) : Y.farLog R a Ñ (exhale s b X.V S z) p=X.farLog R a Ñ z (logTurn S s b e.ep p) := by
  rcases p with i|i|i
  · change Y.inhale R a (Y.liftA _ _) i=X.inhale _ _ _ _; rw [h.axle hp ht]; exact h.earned_inhale ..
  · change Y.Short (Y.liftA R.beta _) Ñ R.beta a i=X.Short _ _ _ _ _; rw [h.axle hp ht]; exact h.minis hx hy hp ht _ hn a hu he i _
  change Y.fuel _ _ _ _=_; exact h.hired hp ht hx hy ..
end Tuned
end YM.PhysicalNext.Repeat.Turn
