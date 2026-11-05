import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cincture

/-!
# Extension of the unforced integrands. Unmasked on the *coarse* level

Do not call for forced species or on R.one side without applying masking
at their genuine enlarged output footprints. Also may run outside manifest;
then no energy/progress claim. Use mutable `U` below to eventually substitute
HELD-U while repaying derivatives of gains, profile variance and μ/C.
At eval verifies equality even for discontinuously primal data.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open Pulse Itinerary Raw Scroll Vine Matter
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}

namespace Polar

def twin (T : PathData G) (x : Cell n) (R d : ℕ) (u : Config G n) (i : ℕ×ℕ) := if long T R d x.2 i then
    inner ℝ (T.ellTerms x i.1 u) (T.ellTerms x i.2 u)/2 else 0

def icicle (T : PathData G) (u : Config G n) (R d : ℕ) (cost : ℝ) (p : Pairs n) :=
    cost*twin T (p.2.2.1,p.2.1) R d (pull p.1 0 u) p.2.2.2

def nest (T : Tube G S) (x : ℝ) (V : Config G c) (U : Config G f) (R : Rep G f) : LogLetter c f → ℝ :=
    let b := -Raw.orientation*R.beta; let W:= R.path
    Sum.elim (fun i=> -R.activities.regularOccurrence R.p i U)
    (Sum.elim (translateValue R.p W.cubic b U) (Sum.elim (translateValue R.p W.quartic b U)
    (Sum.elim (translateValue R.p W.loop (-Raw.orientation) U) (Sum.elim (pairValue W R.clip R.p.threshold (till x) 1 b U)
      (icicle T.down V (till x) S.patch.L.val (-b))))))

variable (X : Coat T F) (a : ℝ) (R : Rep G f) (W : ℝ) (Ñ : ChartRatio G) (u : Directions G f) (U : Config G f) (z : Air f G) (k : Finset ℕ)

def frost (i : LogLetter c f) := nest T X.x X.V U R i * X.enforce (2*a) u (X.plaza (space T 0 X.B R i))

def sheath (i : ℕ) := R.activities.K i U * X.enforce (2*a) u (X.plaza (forcedFoot S.ratio 0 X.B R i))

def veil : Panic c f → ℝ := Sum.elim (fun p=> Mask.fine X.seeds X.χ p X.t U) (Sum.elim
    (fun p=>Mask.noise X.seeds X.χ p X.t W U X.k X.V) (Sum.elim (pinMass U X.k) (Sum.elim (siteMass U X.k) (Contract.charges R k U))))

def flare (p : Panic c f) := if mandatory X.seeds X.B p then 0 else X.enforce (2*a) u (X.plaza (halo X.B (districts S p)))*
    (veil X R W U k p-1)

def patch (i : Bond f) := if X.Hot i then X.cone (2*a) u i else 1

def major (i : Bond f) := patch X a u i*(∑ j : G.ColorIndex,z (i,j)*shimmer X R.beta (i,j))

def entangled (p : Ledger f 2) := patch X a u p.2.1 * patch X a u (arrive p.2.1 p.2.2)*X.qunique z p

def spins : ChainIndex f→ℝ := let D:=X.shutter
    Sum.elim (fun i=> -(ArmA D X.plate i)/2) (Sum.elim (fun i=> ArmA D X.blank.plate i/2)
    (Sum.elim (fun i=>ArmS D X.plate i/2) (Sum.elim (major X a R u z) (entangled X a u z))))

def rootface (paint : Bool) (s : Signed) (i : Spot c f) := loft T X.x (pull s 0 U) (choice s X.k) (pull s 0 X.V) paint i -
    Vine.costs X u s i

def hover (p : Stream c f) := let i:=rowSite S p
    if Inside i X.seeds (200*X.B) then 0 else -R.beta*Raw.orientation*(X.enforce (2*a) u (X.booth i)*rootface X u U true p.1 p.2+
      Vine.costs X (voltage X) p.1 p.2)

def whelp : Miniature c f→ℝ := Sum.elim (hover X a R u U) (Sum.elim X.undercurrent (X.solo u Ñ a))

def logMoment (h : LogIndex c f) := Sum.elim (frost X a R u U) (Sum.elim (whelp X a R Ñ u U)
    (spins X a R u z)) h

def chalky (A : Stores S) := averaged fun s=> ∑ p∈ posted (turnStore s A) (200*X.B), rootface X u U false s p

def crispy (A : Stores S) := averaged fun s=> ∑ p∈ posted (turnStore s A) (200*X.B), Vine.costs X (voltage X) s p

def plumeLog (A : Stores S) := -R.beta*(chalky X u U A+crispy X A) + (∑ i∈ visit A (200*X.B), X.condensation i) +
    (∑ i∈ X.plaza (A.dome (304*X.B)),X.gentry Ñ a u i)-(X.pens A).card*Real.log (measure_g Ñ R.beta)

def stock (A : Stores S) := if A.place⊆ X.seeds.place ∧ A.flags=∅ then
    let Y:=300*X.B
    Real.exp (plumeLog X a R Ñ u U A)*Contract.order R k (vias S A Y) U*tickets A Y U X.k*
      profiles A X.χ Y X.x W U X.k X.V * X.enforce a u (X.plaza (A.dome (304*X.B))) else 0

def sprinkle : WarningAt c f → ℝ := Sum.elim (flare X a R W u U k) (X.aura u a)

def ember (l : ℕ) : Head S → ℝ := Sum.elim (fun p=> if Packets.connected S l X.B p then stock X a R W Ñ u U k p else 0)
    (Sum.elim (sheath X a R u U) (Sum.elim (fun i=> Real.exp (logMoment X a R Ñ u U z i)-1) (sprinkle X a R W u U k)))

def floating (l : ℕ) (p : Molecule S) := ∏ i∈p,ember X a R W Ñ (worldZ X R.beta z) (X.input (worldZ X R.beta z)) z k l i

variable (p : Room P S T X.x) (hp : X.manifest) {l : ℕ}
include p
lemma albedo (i : LogLetter c f) (h : Healthy (Pressure.temp X.x) (space T l X.B R i) X.V) :
    nest T X.x X.V U R i=expo T X.x R U X.V i := by
  rcases i with i|i|i|i|i|i <;> first | rfl | skip
  let x:=i.2.2.1; let s:=i.1
  suffices he : PathData.kept T.low (Pressure.temp X.x) x (pull s 0 X.V) by
    change _*twin _ _ _ _ _ _ = _ * pairTail _ _ _ _ _ _ _ _; unfold pairTail twin; dsimp [x,s] at he; simp_rw [he,and_true]
  have he : Clean X.V X.x (s.act x) X.B := by
    intro v hv; obtain ⟨u,rfl⟩:= s.actEquiv.surjective v
    change separation (s.act x) (s.act u) ≤ _ at hv
    rw [separation_signed] at hv
    rw [show s.actEquiv u=affine s 0 u from (affine0 ..).symm]
    apply Finset.disjoint_left.mp h; apply mem_image_of_mem
    apply halo_subset
    apply mem_image.mpr; refine ⟨u,mem_union_left _ (halo_spec.mpr ⟨x,mem_singleton_self x,hv⟩),parent_one _⟩
  exact he.turn.kept p x (by rw [separation_self]; change 0+X.B/25≤_; omega)

include hp
lemma cotton (w : Directions G f) (s : Signed) (i : Spot c f) : X.extracted w s i=Vine.costs X w s i := by
  unfold Coat.extracted Vine.costs; simp_rw [warms X p hp]
lemma bunting (i : Spot c f) (s : Signed) (h : Clean X.V X.x (s.act (lead S i)) (X.B/2)) :
    X.light u s i=rootface X u (X.input u) true s i ∧ X.debit u s i=rootface X u (X.input u) false s i := by
  obtain ⟨hh,hb⟩:= Scroll.yields p i h.turn (pull s 0 (X.input u)) (choice s X.k)
  exact ⟨congr_arg₂ (·-·) hh (cotton X p hp u s i),congr_arg₂ (·-·) hb (cotton X p hp u s i)⟩

variable (hl : 500≤l)
include hl
lemma sectorPass (A : Stores S) (h : Healthy (Pressure.temp X.x) (A.dome (l*X.B)) X.V) :
    let U:= X.input u
    chalky X u U A=X.quoteNear A u ∧ plumeLog X a R Ñ u U A=X.steamLog R Ñ a A u ∧ X.Pack R Ñ k W a A u=stock X a R W Ñ u U k A := by
  intro U; have hB := Nat.mul_le_mul_right X.B hl
  have he y d (hd : d≤l*X.B) (hy : Inside y A d) : y∉ RG.flags (Pressure.temp X.x) X.V := Finset.disjoint_left.mp h (Corona.halo_mono hd (Subset.refl A.place) hy)
  have hh : chalky X u U A=X.quoteNear A u := by
    apply congr_arg averaged; funext s; apply sum_congr rfl; intro i hi; let v:=lead S i
    have hf : Inside (s.act v) A (200*X.B) := (rotates_dome ..).mp (mem_filter.mp hi).2
    refine ((bunting X u p hp i s ?_).2).symm; intro y hy; exact he y _ (le_refl _) (touch_extend hf (by unfold v; omega))
  have hx : crispy X A=X.far_bills A := by unfold crispy far_bills; simp_rw [cotton X p hp X.μ, agrees_all X p hp]
  have hv : plumeLog X a R Ñ u U A=X.steamLog R Ñ a A u := by unfold plumeLog steamLog; rw [hh,hx]
  have hq : X.existSeeds A 300 ↔ A.place⊆ X.seeds.place ∧ A.flags=∅ := by
    constructor
    · rintro ⟨hg,hB'⟩; refine ⟨hg,?_⟩; ext i; simp only [notMem_empty,iff_false]; intro hi; have hk : Inside i A (300*X.B) :=
        halo_subset _ A.place (mem_union_right _ hi); exact he _ _ (by omega) hk ((hB' i hk).mp hi)
    rintro ⟨hr,hK⟩; exact ⟨hr,fun i hi=> iff_of_false (by simp [hK]) (he i _ (by omega) hi)⟩
  refine ⟨hh,hv,?_⟩; unfold Pack stock; rw [hq]; split
  next hK => unfold steam; rw [hv]
  next => rfl

lemma miniature (u : Directions G f) (i : Miniature c f) (he : Healthy (Pressure.temp X.x)
    (sleeve S X.B l i) X.V) : X.Short u Ñ R.beta a i=whelp X a R Ñ u (X.input u) i := by
  rcases i with i|i|i
  · change X.speck u R.beta a i = hover X a R u (X.input u) i
    have hB := Nat.mul_le_mul_right X.B hl
    change Healthy _ (Animals.neighbors (l*X.B) (rowSite S i)) X.V at he
    have hk : Clean X.V X.x (i.1.act (lead S i.2)) (X.B/2) := fun j hj=> Finset.disjoint_left.mp he
      ((Animals.neighbors_mem ..).mpr (show separation (rowSite S i) j ≤ l*X.B from hj.trans (by omega)))
    unfold speck hover; dsimp only; rw [(bunting X u p hp i.2 i.1 hk).1, cotton X p hp X.μ,agrees_all X p hp]
  · simp only [Coat.Short,whelp,Sum.elim]
  simp only [Coat.Short,whelp,Sum.elim]
omit hl in
lemma margins (u : Directions G f) (h : X.liftA R.beta z=u) (i : ChainIndex f) :
    X.fuel a R.beta z i=spins X a R u z i := by
  have hh j : X.aperture R.beta z a j=patch X a u j := by unfold aperture patch; rw [h]
  unfold Coat.fuel spins; rcases i with i|i|i|i|i
  · simp only [Sum.elim]
  · simp only [Sum.elim]
  · simp only [Sum.elim]
  · change X.qfirst R.beta z a i=major X a R u z i; unfold major qfirst qlinear; rw [hh i, shines X p hp]
  change X.chain R.beta z a i=entangled X a u z i; unfold entangled Coat.chain; simp_rw [hh]
lemma leisure (z : Air f G) (u : Directions G f) (h : X.liftA R.beta z=u) (i : LogIndex c f) (he : Healthy (Pressure.temp X.x)
    (roadway T R X.B l i) X.V) : X.raiseAir R a Ñ z i=Real.exp (logMoment X a R Ñ u (X.input u) z i)-1 := by
  unfold raiseAir; suffices he : X.farLog R a Ñ z i=logMoment X a R Ñ u (X.input u) z i by rw [he]
  unfold farLog logMoment
  rw [h]; rcases i with i|i|i
  · exact congrArg (· * X.enforce (2*a) u (X.plaza (Raw.space T 0 X.B R i))) (albedo X R (X.input u) p i he).symm
  · exact miniature X a R Ñ p hp hl u i he
  exact margins X a R z p hp u h i
lemma whereBorn (i : Head S) (h : Healthy (Pressure.temp X.x) (areas R T l X.B i) X.V) :
    X.vertex R Ñ W a k l z i=ember X a R W Ñ (worldZ X R.beta z) (X.input (worldZ X R.beta z)) z k l i := by
  let u:=X.liftA R.beta z; suffices he : X.vertex R Ñ W a k l z i=ember X a R W Ñ u (X.input u) z k l i by rw [← shine X p hp]; exact he
  rcases i with i|i|i|i
  · have hp := ((sectorPass X a R W Ñ u k p hp hl i h).2.2); change (if Packets.connected S l X.B i then X.Pack R Ñ k W a i u else 0)=(if Packets.connected S l X.B i then Polar.stock X a R W Ñ u (X.input u) k i else 0); rw [hp]
  · simp only [vertex, Sum.elim, ember]; rfl
  · exact leisure X a R Ñ p hp hl z u rfl i h
  cases i <;> simp only [Coat.vertex,Sum.elim, ember, detect, sprinkle]
  · unfold mayor flare; rfl
  rfl
lemma afterborn (i : Molecule S) (h : Healthy (Pressure.temp X.x) (ground R T l X.B i) X.V) :
    X.term R Ñ W a k l z i=floating X a R W Ñ z k l i := Finset.prod_congr rfl (fun j hj=> whereBorn X a R W Ñ z k p hp hl j
      (Finset.disjoint_of_subset_left (subset_biUnion_of_mem (areas R T l X.B) hj) h))
end Polar
end YM.ConnectedActivityE6.Blaze
