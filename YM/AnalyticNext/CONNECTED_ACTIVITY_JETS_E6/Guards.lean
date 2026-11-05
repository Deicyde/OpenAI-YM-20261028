import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Alert
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Peak

/-!
# Nonconstant warning terms supported on rare events

Use Gaussian over physical Air/F; when factors co-occur, tail cannot
be paid as independent coin flips. Envelope on full radius. Beta in
SUP test on Intake, eventual capacities. Use |z| coordinates to cluster
without introducing further Marks in actual choice-list.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {η r Q Y β : ℝ} {L : Side}

namespace Coat
variable (X : Coat T F)
lemma watch_turn {o v : Site c} {ξ β : ℝ} {B D} {z : Air f G} (h : X.watch o ξ β B z) (he : separation o v+D≤B) :
    X.watch v ξ β D z := fun i hi => h i <| (separation_triangle _ v _).trans (le_trans (Nat.add_le_add_left hi _) he)

lemma mandatory_far (i : Panic c f) (h : ¬ mandatory X.seeds X.B i) :
    ¬ Inside (focus_alarms S i) X.seeds (300*X.B) := fun hi => h <| Finset.not_disjoint_iff.mpr ⟨_,hi,home_storm ..⟩

private lemma tolling (t v : ℝ) (h : 0≤v) (ht : 0<t) (χ : Chi) (hh : v≤t) : χ.innerShare t v=1 := by
  apply χ.to_one
  have he : v/t≤1 := (div_le_one ht).2 hh
  have hi : 0 ≤ v/t := div_nonneg h ht.le; nlinarith

lemma blowing {R : Rep G f} (hP : Intake P T X.x R) (θ : Rotator P L η r Q Y X) {W ξ a : ℝ} (hW : 0<W)
    (z : Air f G) (ht : ∀ i : Site c, ¬ Inside i X.seeds (30*X.B) → X.watch i ξ R.beta X.B z →
      let U:= X.input (X.liftA R.beta z)
      Tags.siteMass U X.k i=1 ∧ (∀ p : Cell f, S.ratio.parent p.1=i → toll U p < X.t/4) ∧
        ∀ j : Axis, Tags.pinMass U X.k (i,j)=1 ∧ wire (S.prediction U X.k) X.V (i,j) < W*X.t)
    (i : Panic c f) (hh : X.watch (focus_alarms S i) ξ R.beta (2*X.B) z) (l : Finset ℕ) :
    X.mayor (X.liftA R.beta z) W a R l i=0 := by
  unfold mayor; split
  next hp => rfl
  next he =>
    let x := focus_alarms S i; let u := X.liftA R.beta z; let U := X.input u
    have hx := X.mandatory_far i he
    have hv (y : Site c) (hi : separation (focus_alarms S i) y ≤ X.B) := ht y (clear hx (by omega)) (X.watch_turn hh (by omega))
    have h₁ : 100≤X.B := θ.room.sight.1
    have hq : 0<X.t := θ.room.fiery
    suffices hk : X.rawStorm u W X.seeds R l i = 1 by rw [hk,sub_self, mul_zero]
    let p := hv (focus_alarms S i) (by rw [separation_self]; omega)
    dsimp only at p
    rcases i with p'|p'|p'|p'|p'
    · have hp : p'∉X.seeds.costs := fun he => hx (halo_spec.mpr
        ⟨_,mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨p',he,home_storm S (.inl p')⟩)), by rw [separation_self]; omega⟩)
      change (Mask.fine X.seeds X.χ p' X.t U)=1
      unfold Mask.fine; dsimp only; rw [if_neg hp]; exact tolling _ _ (G.chord_nonneg _) (by positivity) _ (p.2.1 p' rfl).le
    · let q : Panic c f := .inr (.inl p')
      have hp : p'∉X.seeds.aisles := fun he => hx (halo_spec.mpr
        ⟨_,mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨p',he,home_storm S q⟩)),by rw [separation_self]; omega⟩)
      change Mask.noise X.seeds X.χ p' X.t W U X.k X.V=1
      unfold Mask.noise; dsimp only; rw [if_neg hp]
      exact tolling _ _ (G.chord_nonneg _) (by positivity) _ (p.2.2 p'.2).2.le
    · exact (p.2.2 p'.2).1
    · exact p.1
    change Contract.charges R l U p'=1
    suffices hr : p'∉ RG.flags R.p.threshold U by simp [Contract.charges,hr]
    rw [hP.received.temp]; intro hr
    obtain ⟨v,ht,he⟩ := (flags_spec ..).mp hr
    have hp : separation x (S.ratio.parent v.1)≤X.B := (Work.E04.parent_separation S.ratio p' v.1).trans (by
      rw [separation_comm]; have he := Work.E01.sep_touched v p' ht; omega)
    have hh : toll U v<X.t/4 := (hv _ hp).2.1 v rfl
    change X.t<toll U v at he; linarith


end Coat
end YM.ConnectedActivityE6
