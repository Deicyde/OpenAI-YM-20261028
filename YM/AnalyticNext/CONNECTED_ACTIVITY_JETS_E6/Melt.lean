import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Powder
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Towns

/-!
# partitions of restoration. Mercury

One inventory per sector portion. Occurrences repeated stay in one
identity, signs not positivity. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees Multiple Letter OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C δ e : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {j b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W α μ L Q o C T R) (X : Coat T F) (hk : X.x=α) (he : X.width=o.K)
variable (p : Renewed j a δ e H)

/-- Predicate and unmasked version. -/
def states (r : H.Chainbook) := H.inventory r.1.toLeft= RG.flags (Pressure.temp X.x) X.V∩H.library r

def smiles (r : H.Chainbook) := if H.Fresh r ∧ Ac.Spark H.bookFoot r.1 ∧ H.states X r then
    manyW (H.cologne X) r else 0

def erupted (U : Finset H.Chainbook) := U.biUnion (fun r=> H.inventory r.1.toLeft)=RG.flags (Pressure.temp X.x) X.V



lemma arching {r : H.Chainbook} {z : H.ThickP} (hi : z∈r.fst.toLeft) : H.largeAt z ⊆ H.library r :=
    Finset.subset_biUnion_of_mem H.bookFoot (mem_toLeft.mp hi)
lemma shelf (r : H.Chainbook) : H.inventory r.fst.toLeft ⊆ H.library r := by
  intro i hi; obtain ⟨j,hj,hi⟩ := mem_biUnion.mp hi; exact H.arching hj (Matter.range_flags _ hi)

lemma orbiting (U : Finset H.Chainbook) (z : H.ThickP) : z∈ (openRep U).1.toLeft ↔ ∃ r∈U,z∈r.fst.toLeft := by
  simp only [mem_toLeft,openRep,mem_biUnion]
lemma allotment (U : Finset H.Chainbook) : H.erupted X U ↔ H.inventory (openRep U).1.toLeft=
    RG.flags (Pressure.temp X.x) X.V := by
  unfold erupted
  have hh : H.inventory (openRep U).1.toLeft=U.biUnion (fun r=> H.inventory r.1.toLeft) := by
    ext
    simp only [inventory,mem_biUnion,H.orbiting]; grind
  rw [hh]



lemma colonies (U : Finset H.Chainbook) (h : Letter.Valid H.bookFoot U) (hg : H.erupted X U)
    (r : H.Chainbook) (hi : r∈U) : H.states X r := by
  have hv := H.shelf r; ext v; constructor
  · intro he; exact mem_inter.mpr ⟨hg ▸ mem_biUnion.mpr ⟨r,hi,he⟩,hv he⟩
  intro he; obtain ⟨hz,hy⟩ := mem_inter.mp he; rw [← hg] at hz
  obtain ⟨s,hs,hx⟩ := mem_biUnion.mp hz
  by_cases hp : r=s
  · exact hp.symm ▸ hx
  exact False.elim (Finset.disjoint_left.mp (h.disjoint hi hs hp) hy (H.shelf s hx))


include hk he p


end YM.ConnectedActivityE6.Cash
