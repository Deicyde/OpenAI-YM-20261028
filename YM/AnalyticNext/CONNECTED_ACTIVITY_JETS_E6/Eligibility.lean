import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Intake
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Trail

/-!
# Tax of a site: K family inventory and coarse footprints

Original hard-core. Each admissible nonzero has inventories everywhere
under actual B. Outspark may be cheaper (eligible q forbidden away) but
keep remote q as optional letter. Distinct births. Does not turn colors at
these labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows  Window Census Green Mask Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

namespace Contract

def covered (R : Rep G f) (l : Finset ℕ) := l.biUnion fun i => (R.activities.forced i).support

def sealed (R : Rep G f) (l : Finset ℕ) := (l:Set ℕ).Pairwise
      (fun i j => Disjoint (R.activities.forced i).support (R.activities.forced j).support)

def charges (R : Rep G f) (l : Finset ℕ) (U : Config G f) (x : Site f) :=
    if x ∉ covered R l ∧ x ∈ RG.flags R.p.threshold U then (0:ℝ) else 1

def order (R : Rep G f) (l : Finset ℕ) (A : Support f) (U : Config G f) := ∏ i∈A, charges R l U i

lemma ordinary (R : Rep G f) (l : Finset ℕ) (U : Config G f) (x : Site f) : charges R l U x=0 ∨ charges R l U x=1 := by unfold charges; split <;> simp

lemma valid_pay (R : Rep G f) (l : Finset ℕ) (A : Support f) (U : Config G f) : order R l A U ∈ Set.Icc 0 1 := by
  have hx i : charges R l U i∈Set.Icc 0 1 := by rcases ordinary R l U i with h|h <;> simp [h]
  exact ⟨Finset.prod_nonneg (fun i _ => (hx i).1),Finset.prod_le_one (fun i _ => (hx i).1) (fun i _ => (hx i).2)⟩

variable {x W : ℝ} {R : Rep G f} {χ : Chi} {A : Stores S}

lemma release (h : Intake P T x R) (l : Finset ℕ) (U : Config G f) : R.activities.gasOccurrence R.p l U =
    if sealed R l then order R l univ U * ∏ i∈l,R.activities.K i U else 0 := by
  by_cases he : (∏ i∈l,R.activities.K i U)=0
  · unfold Activities.gasOccurrence; simp [he]
  have hf (i : ℕ) (hi : i∈l) := h.cap.labels.forced.permit i U (show R.activities.K i U≠0 from fun hk => he (prod_eq_zero hi hk))
  unfold Activities.gasOccurrence; split_ifs with hA hL hL
  · rw [show order R l univ U=1 from ?_,one_mul]
    apply prod_eq_one; intro p _; unfold charges; apply if_neg
    rintro ⟨hi,hj⟩; apply hi; rw [← hA.2] at hj
    obtain ⟨i,he,ht⟩ := mem_biUnion.mp hj; exact mem_biUnion.mpr ⟨i,he,(R.activities.forced i).inventory_sup ht⟩
  · exact (hL hA.1).elim
  · rw [show order R l univ U=0 from ?_,zero_mul]
    by_contra hn; apply hA; refine ⟨hL,Subset.antisymm ?_ ?_⟩
    · intro y hy; obtain ⟨i,hi,hg⟩ := mem_biUnion.mp hy
      exact (mem_inter.mp (show y ∈ (R.activities.forced i).support ∩ _ from (hf i hi).1.symm ▸ hg)).2
    intro y hy
    have hp : charges R l U y ≠ 0 := fun hi => hn (prod_eq_zero (mem_univ y) hi)
    unfold charges at hp
    by_cases hh : y∈covered R l
    · obtain ⟨i,hi,hk⟩ := mem_biUnion.mp hh
      refine mem_biUnion.mpr ⟨i,hi,(hf i hi).1 ▸ ?_⟩; exact mem_inter.mpr ⟨hk,hy⟩
    rw [if_pos ⟨hh,hy⟩] at hp
    exact (hp rfl).elim
  rfl

/-- Retain this discrete side of eligibility at address enumeration. -/
def incidence (R : Rep G f) (l : Finset ℕ) (A : Stores S) :=
    ∀ i∈l,∀ p∈(R.activities.forced i).inventory, ∃ j∈A.costs,p∈RG.touched j
lemma needs (h : Intake P T x R) (l : Finset ℕ) (D : Allocation G S x W) (U : Config G f) (V : Config G c)
    (k : S.Choices) (hp : D.bill A k U V ≠0) (hh : R.activities.gasOccurrence R.p l U ≠ 0) : incidence R l A := by
  unfold Activities.gasOccurrence at hh; split at hh
  next he =>
    intro i hi p hj
    apply D.flagged hp p; rw [← h.received.3,← he.2]; exact mem_biUnion.mpr ⟨i,hi,hj⟩
  next hk => exact (hh rfl).elim
end Contract
end YM.ConnectedActivityE6
