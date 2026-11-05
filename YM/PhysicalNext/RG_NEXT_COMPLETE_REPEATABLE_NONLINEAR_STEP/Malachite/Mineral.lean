import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Dryland
import YM.Extra.ITERATION_NO_LOSS.Local
import YM.Extra.SOURCE_HISTORIES.Retained
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Stone
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Sonata

/-!
# Two pre-forecast predictors and agreement of the RECEIPTS

Projection from common unmasked sound at any b. No blanket identification of
chart records, masks or readings; use only for the bare analytic probe cost.
With Width and curvature unchanged. Exported zero and local fee products.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Malachite
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision
open Push.SectorMeasure.Oriented Scroll Vine
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}

section Receipt
variable (X : Coat T F) (h : P.Funds S T)
-- E6 local formulas with dummies
abbrev gem (u : Directions G c) := dry X (u, (0:Directions G f))
def mine := fun u : Directions G c=> (gem X u).form
def drills := fun u : Directions G c=> (gem X u).kernelA
def stoneC := fun u : Directions G c=> (gem X u).relating
def receipt := fun u : Directions G c=> ConnectedActivityE6.stand (bar (gem X u) 0)
def ore := fun u : Directions G c=> leanB (gem X u)
def source := fun u : Directions G c=> well (gem X u)
def study := fun u : Directions G c=> (well (gem X u)) ∘ tube X
-- V9 match up D row space
abbrev Note := Slots S × G.ColorIndex
def rake := fun u => bareD T X.x F X.k (reader G c u)
def looks := fun u => barePi T X.x F X.k (reader G c u)
def paint := fun u => ink T F X.x X.k (reader G c u)
def page := fun u => pencil T F X.x X.k (reader G c u)

-- `receipt` on ANY b
include h in
lemma pass (i : Mention c f) (u : Directions G c) : strain (gem X u) i.1 i.2 0=Offset.fixedBase T X.x (increment 1 u) X.k i := by
  rw [gem,sprig X _ _ h]
  have he : pull i.1 0 (increment 1 u) = increment 1 ((reachP i.1 G c f) (u,0)).1 := by
    rw [Channel.pull_increment,pull_flat]; rfl
  rw [←he]; unfold Scroll.freely baseStroke entryCost Offset.fixedBase
  obtain ⟨s,a|a⟩ := i
  · simp only [Sum.elim_inl,Offset.fixedF,fixed_facade,Channel.pulls_replica]; rfl
  simp only [Sum.elim_inr,Offset.fixedI,Offset.zNoise,fixed_facade,Channel.pulls_replica]; rfl

include h in
lemma receive (i : Slots S × G.ColorIndex) (u : Directions G c) : paint X u i = if keep X.x (shots S X.x) (bareStores S) F i.1 then receipt X u i else 0 := by
  unfold paint ink receipt; change ((Rows.restrict X.x (shots S X.x) _ F (Offset.fixedBase T X.x (field 1 _) _) i.1) i.2)=_
  unfold Rows.restrict ConnectedActivityE6.stand bar; rw [show field 1 (reader G c u)=increment 1 u from rfl,if_pos (show (gem X u).selected i.1.1 (spot S i.1.2) from X.blank_all _ _),pass X h]
  split
  next hp=> rw [show Coat.scale = Rows.slip from Real.sqrt_inv _]
  rfl

-- adapted E6 Olive (private)
private lemma chalk (S : PathData G) (p : Clip) (R M) (a : Twin c) : plotted S p R M (1: Config G c) a=0 := by
  have he (n : ℕ) : shortenTerm S R M (1:Config G c) a.1 n=0 := by
    unfold shortenTerm; split
    next hv => simp [PathData.ellTerms, Work.F03.atSite_path,faceValue, SliceRows.trivial]
    exact rfl
  unfold plotted; split
  next => simp only [shorten,he,tsum_zero]
  simp [shoot,faceValue, SliceRows.trivial]
include h in
lemma mute : receipt X 0 = 0 := by
  funext i; unfold receipt ConnectedActivityE6.stand bar
  rw [if_pos (show (gem X 0).selected i.1.1 (spot S i.1.2) from X.blank_all _ _), gem,sprig X _ _ h]; simp only [show (reachP i.1.1 G c f (0, (0:Directions G f))).1=0 from Prod.ext_iff.mp ((reachP i.1.1 G c f).map_zero) |>.1]
  change (Coat.scale • Scroll.freely T X.x (increment 1 (0:Directions G c)) _ _) i.2=_
  rw [Work.G07.at_zero_increment]
  suffices H : ∀ s : Signed, ∀ p,Scroll.freely T X.x (1 : Config G c) (choice s X.k) p = 0 by rw [H,smul_zero]; rfl
  intro s p
  unfold Scroll.freely baseStroke entryCost visual; rw [replica_flat]
  have he (u : Twin c) : T.Xn (till X.x) (1 : Config G c) u=0 := chalk ..
  rw [show S.prediction 1 (choice s X.k)=(1:Config G c) from funext fun i=> Push.settled S (funds_branch h) i (choice s X.k)]
  rcases p with i|i
  · simp only [Sum.elim,Tube.Xf,chalk,canopyF,zip,he,map_zero,Finset.sum_const_zero,sub_zero]
  simp only [Sum.elim,canopyI,zip,Tube.Z,he,Pi.one_apply,inv_one,mul_one,G.curvature_unit,smul_zero,map_zero,Finset.sum_const_zero,sub_zero]
include h
lemma unpainted : paint X 0 = 0 := by funext i; rw [receive X h,mute X h]; simp
lemma scores (i : Eye X) (u : Directions G c) : ((mine X 0).transpose*ᵥ receipt X u) (tube X i)= ((rake X 0).transpose *ᵥ paint X u) i := by
  unfold mine gem dry rake bareD profileD; dsimp only; rw [map_zero,field_zero,Work.G07.at_zero_increment]
  rw [← focus_keys X h]; change (X.blank.form.transpose *ᵥ receipt X u) _=_
  unfold Matrix.mulVec dotProduct; refine Finset.sum_congr rfl fun j _=> ?_
  rw [receive X h]; split
  · rfl
  next hz =>
    change X.blank.form j (tube X i)*_=(X.blank.form.submatrix id (tube X)) j i *0
    have he: X.blank.form j (tube X i)=0 := by
      change (X.blank.form.submatrix id (tube X)) j i=0
      rw [focus_keys X h]; unfold Rows.move Rows.selected; dsimp only [of_apply]; change (Rows.restrict _ _ _ _ _ j.1) j.2=0
      rw [Rows.restrict,if_neg hz]; rfl
    rw [he,zero_mul,mul_zero]
lemma vacant : ore X 0=0 := by
  change (mine X 0)ᵀ *ᵥ receipt X 0=0; rw [mute X h,Matrix.mulVec_zero]
lemma bare_page : page X 0=0 := by
  change (rake X 0)ᵀ *ᵥ paint X 0=0; rw [unpainted X h,Matrix.mulVec_zero]
lemma dry_first : source X 0=0 := by
  change -((drills X 0)ᵀ *ᵥ ore X 0)=0; rw [vacant X h,Matrix.mulVec_zero,neg_zero]
lemma clean_study : study X 0=0 := by funext i; change source X 0 (tube X i)=0; rw [dry_first X h]; rfl
lemma cool_chart : forecast T X.x F X.k 0 = 0 := by
  change -(looks X 0)ᵀ *ᵥ page X 0=0; rw [bare_page X h, Matrix.mulVec_zero]
end Receipt
end YM.PhysicalNext.Repeat.Malachite
