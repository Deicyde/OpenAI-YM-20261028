import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Assignment
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Mask

/-!
# Sites per physical volume, anchor spending

Do not use these estimates to replace an exponential of a whole-volume
bill by a hit price. Apply on each FULL halo when its factors are charged.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {ι κ : Type*}

/-- Capture *all* physical copies, including multiple orientations and mask sites. -/
def Census (n : ℕ) [Fintype ι] (p : ι→Site c) : Prop :=
    ∀ Y : Support c,(univ.filter fun x : ι => p x ∈ Y).card ≤ Y.card*n

namespace Census
lemma ordinary : Census 1 (id : Site c → Site c) := by
  intro Y
  rw [show (univ.filter fun x => id x ∈ Y)=Y by ext; simp]
  simp
lemma homeland (S : StepData c f) : Census (S.patch.L.val^4) S.ratio.parent := Footprint.crowd _

section build
variable [Fintype ι] [Fintype κ] {p : ι → Site c} {q : κ → Site c}
variable {m l : ℕ}

lemma withType (k : Type*) [Fintype k] (h : Census m p) :
    Census (m*(Fintype.card k)) (fun x : ι × k => p x.1) := by
  intro Y
  rw [show (univ.filter (fun x : ι × k => p x.1∈Y)) = (univ.filter fun x => p x∈Y) ×ˢ univ by ext; simp]
  rw [card_product,card_univ,← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (h Y)

lemma added (h : Census m p) (he : Census l q) : Census (m+l) (Sum.elim p q) := by
  intro Y
  rw [show (univ.filter (fun x : ι⊕κ => Sum.elim p q x ∈ Y)) =
    (univ.filter fun x : ι => p x ∈ Y).disjSum (univ.filter fun x : κ => q x ∈ Y) from by ext i; cases i <;> simp]
  rw [card_disjSum,Nat.mul_add]; exact Nat.add_le_add (h Y) (he Y)

lemma permute (h : Census m p) (e : Equiv.Perm (Site c)) : Census m (fun x => e (p x)) := by
  intro Y
  have he := h (Y.map e.symm.toEmbedding)
  simpa only [mem_map_equiv,Equiv.symm_symm,card_map] using he

lemma prefix_counts {p : κ → ι → Site c} (h : ∀ x, Census m (p x)) :
    Census (Fintype.card κ*m) (fun x : κ×ι => p x.1 x.2) := by
  intro Y
  let V i := (univ.filter fun x : ι => p i x ∈ Y)
  rw [show univ.filter (fun x : κ×ι => p x.1 x.2∈Y)=univ.biUnion (fun i : κ => {i} ×ˢ V i) by ext x; rcases x with ⟨x,i⟩; simp [V]]
  apply card_biUnion_le.trans
  have he := Finset.sum_le_sum (g := fun _=>Y.card*m) (s:=univ) (fun i _ => h i Y)
  simp only [card_product,card_singleton,one_mul];
  exact he.trans_eq (by rw [sum_const,nsmul_eq_mul, Finset.card_univ]; push_cast; ring)
end build
open Coat

def spots (L : Side) := L.val^4*Fintype.card PlaqAxes + (Fintype.card Axis+ (Fintype.card PlaqAxes+Fintype.card Gain))
lemma anchors (S : StepData c f) : Census (spots S.patch.L) (lead S) := by
  unfold lead spots
  apply added (withType PlaqAxes (homeland S))
  convert added (withType Axis (ordinary (c:=c)))
    (added (withType PlaqAxes (ordinary (c:=c))) (withType Gain (ordinary (c:=c)))) using 1 <;> rfl

lemma perch (S : StepData c f) : Census (S.patch.L.val^4*Fintype.card Axis) (atEdge S) :=
    withType Axis (homeland S)

lemma offset_bound {ι : Type*} [Fintype ι] {m : ℕ} {p : ι→Site c} (h : Census m p) (P : Finset ι)
    (A : Stores S) (d : ℕ) (ht : ∀ i∈P, Inside (p i) A d) :
    P.card ≤ A.shares*Animals.ballCost (d+1)*m := by
  apply le_trans <| Finset.card_le_card (show P ⊆ univ.filter fun i : ι => p i ∈ A.dome d from
    fun i hi => mem_filter.mpr ⟨mem_univ _,ht i hi⟩)
  exact (h _).trans (Nat.mul_le_mul_right _ (dome_count A _))
lemma postedBound (A : Stores S) (d : ℕ) :
    (posted A d).card ≤ A.shares*Animals.ballCost (d+1)*spots S.patch.L :=
  offset_bound (anchors S) _ _ _ fun _ hi => (mem_filter.mp hi).2
lemma posted_here {s : Signed} (A : Stores S) (p : Coat.Spot c f) (d : ℕ) :
    p∈Coat.posted (turnStore s A) d ↔ Inside (s.act (Coat.lead S p)) A d := by simp [posted,Inside,rotates_dome]

lemma width_rate (G : Gauge) (L : Side) (d e : ℕ) : Rate G L 0 (fun x => (Animals.ballCost (d*radiusB x+e):ℝ)) := by
  unfold Animals.ballCost; push_cast
  have he := ((((Rate.transfers (G:=G) (L:=L) d e).mul_left 2).add (Rate.const 1)).pow 4)
  simpa [two_mul] using he

lemma width_bound (G : Gauge) (L : Side) (d e : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ x : ℝ, (Animals.ballCost (d*radiusB x+e):ℝ) ≤ C*Delay.bill G L x^4 := by
  let A : ℝ := 2*d+2*e+1
  have he : 0<A := by unfold A; positivity
  refine ⟨A^4,by positivity,fun x => ?_⟩
  unfold Animals.ballCost; push_cast
  have hh : (radiusB x:ℝ) ≤ Delay.bill G L x := by unfold Delay.bill; linarith [sq_nonneg (Real.log (betaF G x L))]
  rw [← mul_pow]
  have hx := Delay.bill_ge G L x
  gcongr
  unfold A; nlinarith
end Census
end YM.ConnectedActivityE6
