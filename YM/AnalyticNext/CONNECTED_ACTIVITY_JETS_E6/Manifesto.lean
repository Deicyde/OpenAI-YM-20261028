import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.BridgeL
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Fairground
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Matter

/-!
# Standalone species. From and to genuine quantities
Same signs theme. Explicit output-flag predicate only here. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Matter
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {p : Molecule S} {V : Finset (Molecule S)} {b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}

def preps (X : Coat T F) (s : Stores S) : Coat T F := {X with seeds := s}

def planted (X : Coat T F) (p : Molecule S) := preps X {(roster p) with flags:= RG.flags (Pressure.temp X.x) X.V}
def amountP (R : Rep G f) (X : Coat T F) (W a : ℝ) (l : ℕ) (Ñ : ChartRatio G) (p : Molecule S) :=
    (planted X p).levelMean R Ñ W a (own p) l p

def proceedsA (R : Rep G f) (X : Coat T F) (W a : ℝ) (l : ℕ) (Ñ : ChartRatio G) (p : Molecule S) :=
    if standsIn X R l p then amountP R X W a l Ñ p else 0

def ejections (R : Rep G f) (X : Coat T F) (W a : ℝ) (l : ℕ) (Ñ : ChartRatio G) (V : Finset (Molecule S)) :=
    if joints T R l X.B V ∧ covers X V then ∏ i∈ V,proceedsA R X W a l Ñ i else 0

def receiptM (R : Rep G f) (X : Coat T F) (W a : ℝ) (l : ℕ) (Ñ : ChartRatio G) (p : Molecule S) :=
    let Y:= preps X (roster p)
    if Y.approve (own p) R ∧ Layout (roster p) l X.B p.toLeft then Y.levelMean R Ñ W a (own p) l p else 0

theorem planted_valid (X : Coat T F) (s : Molecule S) : (planted X s).manifest := rfl

variable (X : Coat T F)

lemma cap_iff (h : joints T R l X.B V) :
    let p := V.biUnion id
    (preps X (roster p)).approve (own p) R ∧ Layout (roster p) l X.B p.toLeft ↔
      covers X V ∧ ∀ i∈V,standsIn X R l i := by
  intro p; let f:=ground R T l X.B
  have hf : (preps X (roster p)).manifest ↔ covers X V := by unfold manifest covers; dsimp only [preps]; unfold p; rw [totals]
  have he i (hi : i∈V) (hv : covers X V) : RG.flags (Pressure.temp X.x) X.V ∩ f i=(roster i).flags := by
    unfold covers at hv
    rw [← hv]; ext j; constructor
    · intro hp; obtain ⟨hg,hp⟩ := mem_inter.mp hp
      obtain ⟨y,hy,hY⟩ := mem_biUnion.mp hg; by_cases hh : i=y
      · subst y; exact hY
      exact False.elim <| Finset.disjoint_left.mp (h.2 hi hy hh) hp (range_flags y hY)
    exact fun Hj=> mem_inter.mpr ⟨mem_biUnion.mpr ⟨i,hi,Hj⟩, range_flags _ Hj⟩
  refine ⟨fun ⟨ha,hx⟩=> ⟨hf.1 ha.1,fun i hi=> ⟨h.1 _ hi, (Propels.climates h).1 ⟨hx,ha.2⟩ i hi,he i hi (hf.1 ha.1)⟩⟩, fun ⟨hp,hp'⟩ => ?_⟩
  have hz := (Propels.climates h).2 fun i hi=> (hp' i hi).2.1
  exact ⟨⟨hf.2 hp,hz.2⟩,hz.1⟩

private lemma plant_area (h : claimed X R l p) (o : Site c) (hp : o∈ ground R T l X.B p) :
    o∈ (planted X p).seeds.place ↔ o∈(roster p).place := by
  have he := h.2; unfold place; simp only [preps,planted,mem_union]; rw [← he,mem_inter]; simp [hp]

lemma amounts (h : joints T R Q.halo X.B V) (he : covers X V) (hi : p∈V) (hy : standsIn X R Q.halo p)
    (B : Cash W X.x μ L Q o C T R) (hk : X.width=o.K) :
    proceedsA R X W o.a Q.halo Q.table p=(preps X (roster (V.biUnion id))).levelMean R Q.table W o.a (own (V.biUnion id)) Q.halo p := by
  let Y:= planted X p; let A:= V.biUnion id; let Y':=preps X (roster A); let M:= B.unionP
  have hm : Y'.manifest := by unfold manifest Y' preps A; rw [totals]; exact he
  rw [proceedsA,if_pos hy,amountP];
  unfold levelMean; apply congr_arg likely; funext k
  have hl : (V:Set _).PairwiseDisjoint M := h.2
  have hv i (hc : i∈ V) (o) (hx : o∈M p) (hy : o∈ M i) : p=i := by
    by_contra hn; exact Finset.disjoint_left.mp (hl hi hc hn) hx hy
  have hp (x) (hx : x∈ M p) : x∈ (roster p).place ↔ x∈(roster A).place := by
    rw [← Packets.place_reads,← Packets.place_reads]; constructor
    · intro h; obtain ⟨v,hv,h⟩ := mem_biUnion.mp h
      exact mem_biUnion.mpr ⟨v,(star_sizes V _).2 ⟨p,hi,hv⟩,h⟩
    intro h; obtain ⟨j,hj,h⟩ := mem_biUnion.mp h; obtain ⟨i,hi,hb⟩ := (star_sizes V _).1 hj
    refine mem_biUnion.mpr ⟨j,(hv i hi _ hx (claim_zoneA R T _ _ i _ hb h)).symm ▸ hb,h⟩
  refine B.vista p (Y.taggedL k) (Y'.taggedL k) rfl hk (planted_valid X p) hm
    ⟨rfl,rfl,rfl,fun i hi=> (plant_area X hy.2 i hi).trans (hp i hi), fun _ _=>rfl,
      fun _ _=> rfl, fun _ _=>rfl,fun _ _ _=> rfl⟩ ?_
  intro i hj; constructor
  · intro hh; obtain ⟨j,hv,hh⟩ := mem_biUnion.mp hh; exact mem_biUnion.mpr ⟨j,(gloss V _).2 ⟨p,hi,hv⟩,hh⟩
  intro hq; obtain ⟨b,hb,hx⟩ := mem_biUnion.mp hq; obtain ⟨v,hb,hk⟩ := (gloss V _).1 hb
  exact mem_biUnion.mpr ⟨b,(hv v hb _ hj (claim_zoneK R T _ _ v _ hk hx)).symm ▸ hk,hx⟩

lemma alliance (B : Cash W X.x μ L Q o C T R) (hk : X.width=o.K) (V : Finset (Molecule S)) (h : joints T R Q.halo X.B V) :
    ejections R X W o.a Q.halo Q.table V=receiptM R X W o.a Q.halo Q.table (V.biUnion id) := by
  have ht := cap_iff X h; dsimp only at ht
  let p:=V.biUnion id; let X':= preps X (roster p)
  unfold ejections receiptM; simp_rw [ht];
  by_cases hf : covers X V ∧ ∀ i∈V,standsIn X R Q.halo i
  · rw [if_pos hf, if_pos ⟨h,hf.1⟩,B.red_carpet X' rfl hk ((ht.2 hf).1.1) (own p) V (show (V:Set _).PairwiseDisjoint B.unionP from h.2) (unweave h)]
    exact prod_congr rfl fun i hi=> amounts X h hf.1 hi (hf.2 i hi) B hk
  rw [if_neg hf]; split
  next hx =>
    apply prod_eq_zero_iff.mpr
    replace hf := mt (And.intro hx.2) hf; push Not at hf
    obtain ⟨i,hi,hq⟩ := hf; exact ⟨_,hi,if_neg hq⟩
  rfl
lemma fromOne (B : Cash W X.x μ L Q o C T R) (hk : X.width=o.K) (p : Molecule S) :
    ejections R X W o.a Q.halo Q.table (Ac.Parts B.supportP p)=receiptM R X W o.a Q.halo Q.table p := by
  let A := Ac.Parts B.supportP p
  have hg : A.biUnion id=p := Ac.reconstruct ..
  have hp : joints T R Q.halo X.B A := ⟨fun i hi=> (Ac.lives B.supportP p hi).2, Ac.separate ..⟩
  rw [alliance X B hk A hp,hg]
end YM.ConnectedActivityE6.Matter
