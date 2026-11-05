import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Verge
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Homebound
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Wanton


/-!
 Adapted (necessary new cross-Forest support) from accepted E6 Verge.
# Inherited supports. Clump enough for all masks
Only original threshold halos `inspected`, overlap. X on K reads and
eligibility. Finish finite product equality. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio}
variable {x : Site c} {X : Coat T F} {X' : Coat T F'} {a d B l : ℕ} {R : Rep G f} {Z Z' : Support c}
variable {k k' : Finset ℕ} {w v : Air f G}

private lemma pasthalo_ (X : Support n) (p : Ratio c n) (he : enlargement p l B X ⊆ Z) :
    ∀ y ∈ enlargement p 0 B X, Cleanroom Z (l*B) y := by
  intro y hy i hi
  obtain ⟨x,hx,hj⟩ := halo_spec.mp hy
  exact he (halo_spec.mpr ⟨x,hx,(separation_triangle x y i).trans (by rw [zero_mul] at hj; omega)⟩)
private lemma pastturn_ (X : Support n) (p : Ratio c n) (s : Signed) (he : (enlargement p l B X).image (affine s 0) ⊆ Z) :
    ∀ y∈(enlargement p 0 B X).image (affine s 0),Cleanroom Z (l*B) y := by
  intro y hy i hi
  obtain ⟨y,hx,rfl⟩ := mem_image.mp hy; obtain ⟨z,rfl⟩ := (StepData.sendSites s 0).surjective i
  rw [affine0,show StepData.sendSites s (0:Site c) z=s.act z from affine0 s z,separation_signed] at hi
  exact he (mem_image_of_mem _ (pasthalo_ X p (Finset.Subset.refl _) _ hx _ hi))

private lemma pastexp_ (T : Tube G S) (R : Rep G f) (i : LogLetter c f) (he : space T l B R i ⊆ Z) :
    ∀ y ∈ space T 0 B R i,Cleanroom Z (l*B) y := by
  rcases i with i|i|i|i|i|i
  · exact pasthalo_ _ _ he
  all_goals exact pastturn_ _ _ _ he

private lemma oriented_piece_ {U W : Config G f} (s : Signed) (Y : Support f) (h : ∀ i∈Y,
    ∀ j : Bond f, j.1=s.act i → U j=W j) : Agrees Y (pull s 0 U) (pull s 0 W) := by
  intro i he hh
  have hp : U (edge s i)=W (edge s i) := by
    cases hi : s.flip i.2
    · exact h _ he _ (by rw [positive s i hi])
    exact h _ hh _ (by rw [negative s i hi])
  rw [charge,charge,hp]

namespace Clump
variable (H : Clump X X' Z w v k k' R) (p : Room P S T X.x) (hp : 40 ≤ l)
include H p hp

lemma inherits (Y : Support f) (he : enlargement S.ratio l X.B Y ⊆ Z) :
    Agrees Y (X.input (X.liftA R.beta w)) (X'.input (X'.liftA R.beta v)) := by
  intro i hi _
  apply H.quarters p (p:=i) (fun j hj=> he (halo_spec.mpr ⟨_,mem_image_of_mem _ hi,hj.trans (Nat.mul_le_mul_right X.B (by omega))⟩))

lemma turnU (s : Signed) (Y : Support f) (he : (enlargement S.ratio l X.B Y).image (affine s 0) ⊆ Z) :
    Agrees Y (pull s 0 (X.input (X.liftA R.beta w))) (pull s 0 (X'.input (X'.liftA R.beta v))) := by
  apply oriented_piece_
  intro i hi b hb
  have hx : atEdge S b=s.act (S.ratio.parent i) := by unfold atEdge; rw [hb,S.ratio.parent_signed S.patch.odd_side]
  apply H.quarters p; rw [hx,← affine0 s]; intro j hj
  exact pastturn_ Y S.ratio s he _ (mem_image_of_mem _ (halo_subset _ _ (mem_image_of_mem _ hi))) _
    (hj.trans (Nat.mul_le_mul_right _ (by omega)))
lemma turnV (s : Signed) (Y : Support c) (he : (enlargement (atOne _) l X.B Y).image (affine s 0)⊆ Z) :
    Agrees Y (pull s 0 X.V) (pull s 0 X'.V) := by
  have hv := Nat.mul_le_mul_right X.B hp; have hz : 100 ≤ X.B:=p.sight.1
  apply oriented_piece_; intro i hi b hb
  have hh : Cleanroom Z (l*X.B) b.1 := by
    rw [hb,← affine0 s]; apply pastturn_ Y (atOne _) s he _
    apply mem_image_of_mem; rw [← parent_one i]; apply halo_subset; exact mem_image_of_mem _ hi
  exact H.actual b (hh b.1 (by rw [separation_self]; omega)) (hh _ (by have hi:=sep_step b.1 b.2; omega))

lemma province (i : LogLetter c f) (he : space T l X.B R i⊆ Z) (hR : Intake P T X.x R) (a : ℝ) :
    X.inhale R a (X.liftA R.beta w) i=X'.inhale R a (X'.liftA R.beta v) i := by
  let s:= space T 0 X.B R i
  unfold inhale; rw [← H.B,H.enforces p s (fun j hj p hp'=> pastexp_ T R i he j hj p (hp'.trans (Nat.mul_le_mul_right _ (by omega)))),
    ← H.weather];
  refine congrArg₂ (·*·) ?_ rfl
  let u := X.input (X.liftA R.beta w); let y := X'.input (X'.liftA R.beta v)
  have hx d (Z' : ℕ→Atom G d) b (j : Trans f) (he : atomFoot S.ratio l X.B Z' j⊆Z) :
      translateValue R.p Z' b u j=translateValue R.p Z' b y j := congrArg (b * ·) (placed_local (Z' j.2.2) R.p j.2.1 _ _ (H.turnU p hp _ _ he))
  rcases i with i|i|i|i|i|i
  · exact congrArg Neg.neg (valueE R i (hR.cap.labels.regular.smooth i) u y (H.inherits p hp _ he))
  · exact hx _ _ _ i he
  · exact hx _ _ _ i he
  · exact hx _ _ _ i he
  · have hh t (hi : R.p.threshold * Real.exp ((t:ℕ)/R.clip.relaxation)<2) : t+2 ≤ X.B := by
      rw [hR.received.2,hR.received.3] at hi; exact le_trans (p.laneU t hi) (Nat.div_le_self ..)
    exact congrArg ((-orientation*R.beta)*·) (Raw.pair_local _ _ (till X.x) 1 _ _ _ X.B hh
      (pull i.1 0 u) (pull i.1 0 y) (H.turnU p hp _ _ he))
  have hh t (hi : Pressure.temp X.x * Real.exp ((t:ℕ)/T.low.relaxation)<2) : t+2 ≤ X.B := (p.laneV t hi).trans (Nat.div_le_self ..)
  exact congrArg (-(-orientation * R.beta)*·) (Raw.pair_local _ _ _ _ _ _ _ X.B hh _ _ (H.turnV p hp _ _ he))

lemma baggage (a : ℝ) (i : ℕ) (he : forcedFoot S.ratio l X.B R i⊆Z) (hR : Intake P T X.x R) :
    X.bag R a (X.liftA R.beta w) i=X'.bag R a (X'.liftA R.beta v) i := by
  unfold bag; rw [← H.B,H.enforces p (forcedFoot _ _ _ _ _) (fun j hj p hp'=> pasthalo_ (RG.inspected (R.activities.forced i).support) S.ratio he j hj p
    (hp'.trans (Nat.mul_le_mul_right _ (by omega))))]
  exact congrArg (· * _) (UsesFinal.allReads _ _ _ (hR.cap.labels.forced.reads i) _ _ (H.inherits p hp _ he))

omit hp in
theorem complete (hl : 500≤l) (i : Head S) (he : Mixed.foot S l X.B (footprints T R l X.B) i ⊆ Z)
    (hR : Intake P T X.x R) (a W : ℝ) (Ñ : ChartRatio G) :
    X.vertex R Ñ W a k l w i=X'.vertex R Ñ W a k' l v i := by
  rcases i with i|i|i|i
  · change (if Packets.connected _ l X.B i then _ else _ )=(if Packets.connected _ l X'.B i then _ else _)
    rw [← H.B,H.papyrus p (subset_trans (show i.dome (500*X.B) ⊆ i.dome (l*X.B) from Lattice.Corona.halo_mono
      (Nat.mul_le_mul_right _ hl) (Finset.Subset.refl _)) he)]
  · exact H.baggage p (l:=l) (by omega) a i he hR
  · change Real.exp _-1=Real.exp _-1
    apply congrArg (fun z => Real.exp z-1)
    rcases i with i|i|i
    · exact H.province p (l:=l) (by omega) i he hR a
    · exact H.minuteL p hl _ _ i he
    exact H.fuelL p (L:=l) (i:=i) (by omega) he a
  exact H.warning p l hl i he a W
end Clump
end YM.ConnectedActivityE6
