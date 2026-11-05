import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Jetsam

/-!
# Fixed-label full spatial access. Does not price collars twice.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Borough
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Raw Matter Blaze.Scroll Blaze.Vine Blaze.Polar Blaze.Frond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {x : Site c} {X X' : Coat T F} {l m : ℕ} {k k' : Finset ℕ} {R : Rep G f} {Z : Support c}
variable {w v w' v' : Air f G}
variable (H : Borough X X' Z w v k k' R) (p : Room P S T X.x) (hl : 500 ≤ l) {A : Stores S}
include H p
-- use on plaque
lemma towering (h : A.dome (500*X.B) ⊆ Z) (Ñ : ChartRatio G) (a W : ℝ) :
    let u:= X.liftA R.beta w; let v:=X'.liftA R.beta v
    stock X a R W Ñ u (X.input u) k A=stock X' a R W Ñ v (X'.input v) k' A := by
  intro b b'; let U:=X.input b; let V:=X'.input b'
  have hp x d (ht : d≤400*X.B) (hh: Inside x A d) : Cleanroom Z (50*X.B) x := fun _ hi=> h (touch_extend hh (by omega))
  have he s i (he:i∈posted (turnStore s A) (200*X.B)) := H.cornice p (s,i) (fun j hj=>hp (rowSite S (s,i)) (200*X.B)
    (by omega) ((rotates_dome ..).mp (mem_filter.mp he).2) j (hj.trans (by omega)))
  have hK : chalky X b U A=chalky X' b' V A ∧ crispy X A=crispy X' A := by
    unfold chalky crispy; rw [← H.B]; constructor <;> apply congr_arg averaged <;> funext s <;> apply Finset.sum_congr rfl <;> intro i hi
    · exact (he _ _ hi).2 false
    exact (he _ _ hi).1
  have hB : 100≤X.B := p.sight.1
  have hY i (hi : i∈visit A (200*X.B)) : Cleanroom Z (50*X.B) (atEdge S i) := hp _ _ (by exact (show 200*X.B+1≤400*X.B by omega))
    (lives_in i A (mem_filter.mp hi).2)
  let Y := A.dome (304*X.B)
  have hX i (hi : i∈X.plaza Y) : Cleanroom Z (30*X.B) (atEdge S i) := by
    obtain ⟨x,hx,hk⟩:= Finset.not_disjoint_iff.mp (mem_filter.mp hi).2.2
    apply fans (hp x _ (by exact (show 304*X.B ≤ 400*X.B by omega)) hx); have hh:= stride i hk; unfold distAt at hh; omega
  have hu x (hx : x∈ Y) : Cleanroom Z (30*X.B) x := fun _ h=>hp x _ (by exact (show 304*X.B ≤ 400*X.B by omega)) hx _ (h.trans (by omega))
  have hO : plumeLog X a R Ñ b U A=plumeLog X' a R Ñ b' V A := by
    unfold plumeLog pens; rw [hK.1,hK.2,← H.B,← H.passes p Y hu,
      Finset.sum_congr rfl (fun i (hi:i∈visit A (200*X.B))=> H.boxes p i (fun _ hj=>hY i hi _ (hj.trans (by omega)))),
      Finset.sum_congr rfl (g:=X'.gentry Ñ a b') (fun i (hi:i∈ X.plaza Y)=> H.vale p (fun _ hj=> hX i hi _ (hj.trans (by omega))) _ _)]
  have hc : A.place ⊆ X.seeds.place ↔ A.place ⊆ X'.seeds.place := by
    have hp i (hi : i∈ A.place) := H.places i (h (halo_subset _ _ hi)); exact ⟨fun he i hi=> (hp i hi).1 (he hi),fun he i hi=> (hp i hi).2 (he hi)⟩
  have hv (i : Panic c f) (hi : mandatory A X.B i) : X.rawStorm b W A R k i=X'.rawStorm b' W A R k' i := by
    obtain ⟨x,hk,hv⟩ := Finset.not_disjoint_iff.mp hi
    have hr := hp x (300*X.B) (by omega) hk
    apply H.ushers p A A i _ W (fans hr ?_)
    · rcases i with i|i|i
      · exact Iff.rfl
      · exact Iff.rfl
      exact True.intro
    rw [separation_comm]; have he:= alarm_base S i x hv; omega
  have hm (t:ℝ) : t*Contract.order R k (vias S A (300*X.B)) U*tickets A (300*X.B) U X.k*profiles A X.χ (300*X.B) X.x W U X.k X.V =
      t*Contract.order R k' (vias S A (300*X'.B)) V*tickets A (300*X'.B) V X'.k*profiles A X'.χ (300*X'.B) X'.x W V X'.k X'.V := by
    have h:= X.forceds A R k W b
    have hx:=X'.forceds A R k' W b'; dsimp only at h hx
    rw [mul_assoc] at h hx; rw [mul_assoc,mul_assoc,← h,mul_assoc,mul_assoc,← hx,← H.B]
    apply congrArg (t*·); apply Finset.prod_congr rfl; intro i hi; split
    next he=> exact hv i he
    next _ => rfl
  unfold stock; simp_rw [hc]; split
  next hx => rw [hO, hm _,← H.B,H.enforces p _ hu]
  next _ => rfl

include hl
lemma commuteRoad (h : Intake P T X.x R) (a : ℝ) (Ñ : ChartRatio G) {i : LogIndex c f} (K : Borough X X' Z w' v' k k' R)
    (he : roadway T R X.B l i⊆ Z) :
    let u:=X.liftA R.beta w; let u':=X'.liftA R.beta v
    logMoment X a R Ñ u (X.input u) w' i=logMoment X' a R Ñ u' (X'.input u') v' i := by
  intro u u'; rcases i with i|i|i
  · exact H.regime p hl a h he
  · exact H.season p hl Ñ a he
  exact H.centres p hl a i K he
lemma preserve (h : Intake P T X.x R) (a W : ℝ) (Ñ : ChartRatio G) {i : Head S} (K : Borough X X' Z w' v' k k' R)
    (he : areas R T l X.B i⊆ Z) :
    let u:= X.liftA R.beta w; let u':= X'.liftA R.beta v
    ember X a R W Ñ u (X.input u) w' k l i=ember X' a R W Ñ u' (X'.input u') v' k' l i := by
  intro u u'
  rcases i with i|i|i|i
  · unfold ember; simp only [Sum.elim]; rw [← H.B]; split
    next hz=> exact H.towering p (by exact Subset.trans (Lattice.Corona.halo_mono (Nat.mul_le_mul_right X.B hl) (Subset.refl i.place)) he) Ñ a W
    next h => rfl
  · exact H.baggage p (l:=l) (by omega) _ _ he h
  · exact congrArg (fun y:ℝ=> Real.exp y-1) (H.commuteRoad p hl h a Ñ K he)
  cases i
  next val => exact H.mayorL p l hl _ he a W
  next val => exact H.warning p l hl (Sum.inr _) he a W
lemma flops (h : Intake P T X.x R) (a W : ℝ) (Ñ : ChartRatio G) {i : Molecule S} (he : ground R T l X.B i⊆ Z) :
    floating X a R W Ñ w k l i=floating X' a R W Ñ v k' l i := by
  unfold floating; apply Finset.prod_congr rfl; intro j hj
  have hk:= (H.rooms p R.beta).preserve p hl h a W Ñ (i:=j) H (Subset.trans (subset_biUnion_of_mem (areas R T l X.B) hj) he)
  dsimp only at hk; rwa [X.oldysis h.positive, X'.oldysis h.positive] at hk
end YM.ConnectedActivityE6.Borough
