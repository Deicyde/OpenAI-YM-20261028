import YM.MultiNext.VACUUM_STABILITY.Arrival.Receipt

set_option warningAsError false

/-!
# Actual aggregate test budget for a simultaneous analytic list

Native address/read prices even if several directions arrive at same cell;
no disjointness assumption. The projection-specific layer of pricing in Use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Arrival
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Hits
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {V : Type} {n : Side} {F : Flock V G n} {P : BudgetPoint} {D : V→ Pulse G n}
variable {I J : Type}

/-- The actual pre-merge cost convention at an arriving packet. Anchored here (we get hit after projection) -/
def Locations (P : BudgetPoint) (Y : I→Support n) (u : I→ Site n) (f : I→ℝ) (c : ℝ) := ∀ x : Site n,
    SumBudget (fun i => if u i=x then P.mass (Y i) (f i) else 0) c

namespace Locations
variable {Y : I→Support n} {u : I→Site n} {p : I→ℝ} {c : ℝ}

lemma imposed (h : Locations P Y u p c) (hp : ∀ i,0 ≤ p i) : Summable p := by
  let f x i := if u i=x then P.mass (Y i) (p i) else 0
  have hs : Summable fun i => ∑ x,f x i := summable_sum fun x _ => (h x).2.1
  refine hs.of_nonneg_of_le hp fun i => (P.loMass (Y i) _ (hp i)).trans_eq ?_
  simp [f]

lemma just (h : Locations P Y u p c) (hp : ∀ i, 0≤p i) (i) : p i ≤ c := by
  have hv := Absolute.little (h (u i)) i
  simp only [if_true] at hv; exact (P.loMass _ _ (hp _)).trans hv
end Locations

namespace Flock
variable (F)

abbrev Bulk (V : Type) := V × ℕ

abbrev Augment (s : Flock V G n) : Type :=
    {i : V × Pack n // (s i.1).d i.2 ≠ 0}

def bulkZone (i : Bulk V) := (F i.1).letter i.2
def stimulant (i : Bulk V) : Stamp V (Config G n) := ⟨spike i.1,(F i.1).reg i.2⟩

def hardZone (i : Augment F) := i.val.2
def addition (i : Augment F) : Stamp V (Config G n) := ⟨spike i.val.1,(F i.val.1).d i.val.2⟩

variable {F}

variable [Fintype V]

def stipendE (F : Flock V G n) (z : V→ℂ) (i : Bulk V) := ‖z i.1‖*(F i.1).rate.major i.2
def stipendK (F : Flock V G n) (z : V→ℂ) (i : Augment F) := ‖z i.val.1‖*(F i.val.1).rate.minor i.val.2

private lemma together {f : I × J → ℝ} {k : I → ℝ} {c : ℝ} (h : SumBudget k c)
    (hh : ∀ i, SumBudget (fun j => f (i,j)) (k i)) : SumBudget f c := by
  have hn i : 0≤f i:=(hh i.1).1 _
  have he := Absolute.compare h (fun i => tsum_nonneg (hh i).1) fun i => (hh i).2.2
  have ht : Summable f := (summable_prod_of_nonneg hn).2 ⟨fun i => (hh i).2.1,he.2.1⟩
  exact ⟨hn,ht, ht.tsum_prod.trans_le he.2.2⟩

namespace Attended
variable {o : V → Site n} {k : V → ℝ} {κ η : ℝ} (h : Attended F P D o k κ) (z : V → ℂ) (hz : z∈allot o k η)

include h hz in
lemma issued_bulk : Locations P (bulkZone F) (fun i : Bulk V => o i.1) (stipendE F z) η ∧
    ∀ i : Bulk V, o i.1 ∈ bulkZone F i ∧
      P.Regular (bulkZone F i) (stimulant F i).ink ∧ P.supBounds (o i.1) (bulkZone F i) ((stimulant F i).tell z) (stipendE F z i) := by
  have ha i := h.authorizations i
  constructor
  · intro x; let p i := if o i=x then ‖z i‖*k i else 0
    have hp (i) : 0 ≤ p i := by unfold p; split; exact mul_nonneg (norm_nonneg _) (ha i).ok; exact le_rfl
    have he : SumBudget p η := ⟨hp,(hasSum_fintype _).summable,(tsum_fintype _).trans_le (hz x)⟩
    refine together he fun i => ?_
    unfold p; split; rename_i hi
    · simp only [bulkZone,stipendE,BudgetPoint.mass]; simp_rw [mul_left_comm _ ‖z i‖]
      exact permit_mul (ha i).paint (norm_nonneg _)
    simp [SumBudget]
  intro i; obtain ⟨hj,hH,hf⟩ := (ha i.1).wears i.2
  refine ⟨hj,hH,?_⟩; unfold stimulant stipendE Stamp.tell; rw [Stamp.beat_spike]; exact Next.Foundations.bound_smul _ hf

include h hz in
lemma issued_hard (hc : 0 ≤ κ) : Locations P (fun i => (hardZone F i).zone) (fun i : Augment F => o i.val.1) (stipendK F z) (κ*η) ∧
    ∀ i : Augment F, o i.val.1∈(hardZone F i).zone ∧ Legible P (hardZone F i) (addition F i).ink ∧
       0 ≤ stipendK F z i ∧ ∀ U, ‖(addition F i).tell z U‖ ≤ stipendK F z i := by
  have hF i := h.authorizations i
  constructor
  · intro x; let p j := if o j=x then ‖z j‖*k j else 0
    have hp (i) : 0 ≤ p i := by unfold p; split; exact mul_nonneg (norm_nonneg _) (hF i).ok; exact le_rfl
    have he : SumBudget p η := ⟨hp,(hasSum_fintype _).summable,(tsum_fintype _).trans_le (hz x)⟩
    let g (i : V × Pack n) := if o i.1=x then P.mass i.2.zone (‖z i.1‖*(F i.1).rate.minor i.2) else 0
    have hg : SumBudget g (κ*η) := by
      refine together (permit_mul he hc) fun i => ?_
      unfold p; split; rename_i hi
      · have hb : SumBudget (fun j => P.mass (Pack.zone j) ((F i).rate.minor j)) (κ*k i) :=
          ⟨fun j => mul_nonneg (Real.exp_pos _).le ((hF i).bears j).2.2.1,(hasSum_fintype _).summable,
           (tsum_fintype _).trans_le (hF i).hard⟩
        simp only [g,hi,if_true,BudgetPoint.mass]; rw [mul_left_comm]; simp_rw [mul_left_comm _ ‖z i‖]
        exact permit_mul hb (norm_nonneg _)
      rename_i hn; simp [hn,g,SumBudget]
    exact ⟨fun i => hg.1 _,hg.2.1.subtype _, (Summable.tsum_subtype_le g _ hg.1 hg.2.1).trans hg.2.2⟩
  intro i; obtain ⟨a,b,c,e⟩:=(hF i.val.1).bears i.val.2
  refine ⟨b i.property, a, mul_nonneg (norm_nonneg _) c, fun U => ?_⟩; simp only [addition,Stamp.tells,Stamp.beat_spike,norm_mul]
  exact mul_le_mul_of_nonneg_left (e _) (norm_nonneg _)
end Attended
end Flock

-- transfer from output site budget (independent of repeats) to native anchor charges;
-- embed anchors don't collide except existing repetitions.
lemma extended {c f : Side} [Fintype V] (o : V→Site c) {k : V→ℝ} {η : ℝ} (g : Ratio c f)
    (he : 0 ≤ η) {z : V→ℂ} (hz : z∈allot o k η) : z∈allot (fun i => g.embed (o i)) k η := by
  intro x
  by_cases h : x∈Set.range g.embed
  · obtain ⟨a,rfl⟩:=h
    have hf : Function.Injective g.embed := (show Function.LeftInverse g.parent g.embed from g.embed_parent).injective
    simp_rw [hf.eq_iff]; exact hz a
  have he' i : (if g.embed (o i)=x then ‖z i‖ * k i else 0) = 0 := if_neg (fun hf => h ⟨_,hf⟩)
  simp_rw [he', Finset.sum_const_zero]; exact he
end YM.Multi.Vacuum.Arrival
