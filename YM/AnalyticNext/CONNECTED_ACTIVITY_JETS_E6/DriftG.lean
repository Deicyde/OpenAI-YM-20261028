import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood
import YM.Push.ABSOLUTE_SUMS.Gas

/-! # Precision, mean and conjugacy at exact Sector -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Hues
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll  
open Gas Ursell Trees    Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {L : Side} {B : ℕ}
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma reverses {A E : Matrix ι ι ℝ} {Z D : Matrix ι ι ℝ} (h : A*E=E*Z) (he : E*D=1) :
    A⁻¹*E=E*Z⁻¹ := by
  have hp : E.det*D.det=1 := by rw [← det_mul,he,det_one]
  have hh : IsUnit E.det := (isUnit_iff_ne_zero).mpr (by intro H; rw [H,zero_mul] at hp; exact zero_ne_one hp)
  have hi : A=E*Z*E⁻¹ := by rw [← h,mul_assoc,mul_nonsing_inv _ hh,mul_one]
  rw [hi,Matrix.mul_inv_rev,Matrix.mul_inv_rev,Matrix.nonsing_inv_nonsing_inv _ hh,mul_assoc,mul_assoc (_⁻¹),nonsing_inv_mul _ hh,mul_one]

lemma toss {A D : Matrix κ ι ℝ} {E : Matrix κ κ ℝ} {V : Matrix ι ι ℝ} (h : A*V= E*D) (he : E.transpose*E=1)
    (hv : V.transpose*V=1) : A.transpose*E=V*D.transpose := by
  have hx : Vᵀ*Aᵀ=Dᵀ*Eᵀ := by rw [← transpose_mul,h,transpose_mul]
  have hj := mul_eq_one_comm.mp hv
  calc
    _=(V*(Vᵀ*Aᵀ))*E := by rw [← Matrix.mul_assoc V,hj,Matrix.one_mul]
    _=_ := by rw [hx, Matrix.mul_assoc V, Matrix.mul_assoc D.transpose, he, Matrix.mul_one]

abbrev sheen (_X : Coat T F) (z : Site c→ G.El) := Rotation.colorwise (z ∘ atEdge S)

lemma pad_rotates (X : Coat T F) (z : Site c→ G.El) {A A' : Mat f G} (he : A'*sheen X z=sheen X z*A) :
    X.shutter.pad A'* sheen X z=sheen X z* X.shutter.pad A := by
  let E:= sheen X z; let p:=X.shutter
  ext i j
  let w:= p.take j
  have hx a b (ha : a∈w) (hb : b∉w) : E a b=0∧E b a=0 := by
    have ht : Prod.fst a ≠ b.1 := by
      intro h; apply hb; unfold w p Coat.shutter at ha ⊢
      rw [Coat.in_frame] at ha ⊢; rw [← h]; exact ha
    exact ⟨Rotation.off (z ∘ atEdge S) _ _ ht, Rotation.off (z ∘ atEdge S) _ _ ht.symm⟩
  let h (Z : Mat f G):= Batch.principal w Z
  have hh : h A'*h E=h E*h A := by
    unfold h; rw [← Batch.localize_right (P:=E) (fun a ha b hb=> (hx b a hb ha).2), he,← Batch.localize_left (Y:=E) (fun i hi j hj=> (hx i j hi hj).1)]
  have hr : h Eᵀ*h E=1 := by unfold h; rw [← Batch.localize_right (P:=E) (fun a ha b hb=> (hx b a hb ha).2), inverse_up, Batch.within_one]
  let v : ↥w := ⟨j,p.here j⟩
  have hz' (Y : Mat f G) (q : ↥w) (k : Tubular f G) (hk : k∈w) (hp : k.1=j.1) :
    p.pad Y q.val k=(h Y)⁻¹ q ⟨k,hk⟩ := by
    have he' : w=p.take k := by
      ext; unfold w p shutter; rw [Coat.in_frame,Coat.in_frame]; rw [hp]
    unfold h; rw [p.inside Y k ⟨q.val,he' ▸ q.2⟩]; clear v hx hr hh h; clear_value w
    subst w; rfl
  have hZ (a : ↥w) : (h E*(h A)⁻¹) a v=(E*(p.pad A)) a.val j := by
    rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_subset (s₁:=w) (s₂:= @univ (Tubular f G) _) (f:=fun t=> E a.val t*p.pad A t j) (subset_univ _)
      (by intro t _ ht; rw [p.outside A _ _ ht,mul_zero]), ← sum_attach w];
    refine sum_congr rfl fun t _ => ?_; rw [hz' A t j (p.here _) rfl]; rfl
  by_cases hi : i∈w
  · change _=(E*p.pad A) i j
    rw [← hZ ⟨i,hi⟩, ← reverses hh (mul_eq_one_comm.mp hr)]
    have hp (k : Tubular f G) (hk : k∉w) : p.pad A' i k*E k j=0 := by rw [(hx _ _ (p.here j) hk).2,mul_zero]
    change (p.pad A'*E) i j=_
    rw [Matrix.mul_apply, ← Finset.sum_subset (subset_univ w) (fun i _ hi=>hp i hi), ← sum_attach w, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hF : t.val.1=j.1
    · rw [hz' A' ⟨i,hi⟩ t.val t.2 hF]; rfl
    have hr : E t.val j=0 := Rotation.off (z ∘ atEdge S) _ _ hF
    change _*E t.val j=_*E t.val j; rw [hr,mul_zero,mul_zero]
  · have hr (k : Tubular f G) : X.shutter.pad A' i k * E k j = 0 := by
      by_cases hp : k.1=j.1
      · have hv : p.take k=p.take j := by ext; unfold p shutter; rw [Coat.in_frame,Coat.in_frame,hp]
        rw [p.outside A' i k (by rw [hv]; exact hi), zero_mul]
      rw [show E k j=0 from Rotation.off (z ∘ atEdge S) _ _ hp, mul_zero]
    change _=(E*p.pad A) i j; rw [Matrix.mul_apply,Matrix.mul_apply,sum_eq_zero (f:=fun k=> p.pad A' i k*E k j) (fun t _=>hr t)]
    symm; refine sum_eq_zero fun k _=> ?_; by_cases hs : k∈w
    · rw [(hx k i hs hi).2,zero_mul]
    rw [p.outside A k j hs,mul_zero]
end YM.ConnectedActivityE6.Hues
