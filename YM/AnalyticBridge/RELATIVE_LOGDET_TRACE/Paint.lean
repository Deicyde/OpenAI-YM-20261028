import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.PSeries
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Walls
import YM.Push.FREE_RESOLVENT.Focus

/-!
# Color-read reassembly

The alphabet power sums may be kept as *whole color* letters for gauge
covariance. Reassemble this way before acting with a physical symmetry!
No assumption that a particular matrix element is a scalar under local
rotations. All gauges here orthogonal in counting coordinates. Apply also
with windows which select complete colors. Import into allocation/anchor
clients to use grouped ballots with the same determinant ledger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet.Paint
open Function Set Matrix MeasureTheory FreeResolvent Next.SectorChange
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {ι κ γ : Type} [Fintype ι] [Fintype κ] [Fintype γ] [DecidableEq ι] [DecidableEq κ]
variable {A B : Square (ι × κ)} {H : ι → Square κ}

def block {ι κ : Type} (A : Square (ι × κ)) (i j : ι) : Square κ := Matrix.of fun k l => A (i,k) (j,l)
omit [DecidableEq ι] [DecidableEq κ] in
lemma factor (A B : Square (ι×κ)) (i j : ι) : block (A*B) i j=∑ k,block A i k*block B k j := by
  ext m n; unfold block
  rw [Matrix.sum_apply,of_apply, Matrix.mul_apply,Fintype.sum_prod_type]
  rfl
omit [Fintype ι] [Fintype κ] in
lemma foundation (i j : ι) : block (1:Square (ι × κ)) i j= if i=j then (1:Square κ) else 0 := by
  ext m n; rw [block,of_apply]; by_cases hx : i=j
  · simp [hx,Matrix.one_apply]
  simp [hx]

def Moves (H : ι→Square κ) := ∀ i,(H i).transpose * H i=1

def Elation (H : ι→Square κ) (A B : Square (ι×κ)) := ∀ i j : ι, block B i j=H i * block A i j * (H j).transpose

namespace Elation

omit [Fintype ι] [DecidableEq ι] in
lemma rectangle (hi : Moves H) (i j k : ι) (P Q : Square κ) : (H i * P * (H j).transpose) * (H j*Q*(H k).transpose)=H i*(P*Q)*(H k).transpose := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((H j).transpose),hi,Matrix.one_mul]
omit [DecidableEq ι] [Fintype ι] in
lemma relaxed (hi : Moves H) (i : ι) (P : Square κ) : Matrix.trace (H i * P * (H i).transpose)=Matrix.trace P := by
  rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,hi,Matrix.one_mul]

omit [Fintype ι] in
lemma colorless (hi : Moves H) : Elation H 1 1 := by
  intro i j
  have ht := @foundation ι κ _ _ i j
  rw [ht]
  by_cases he : i=j
  · rw [he,if_pos rfl,Matrix.mul_one]; exact (mul_eq_one_comm.mp (hi j)).symm
  rw [if_neg he]; simp
omit [DecidableEq ι] [DecidableEq κ] [Fintype ι] in
lemma add (h : Elation H A B) {C D : Square (ι×κ)} (hc : Elation H C D) : Elation H (A+C) (B+D) := by
  intro i j
  change block B i j+block D i j= H i*(block A i j+block C i j)*_
  rw [h,hc,Matrix.mul_add,Matrix.add_mul]
omit [DecidableEq ι] [DecidableEq κ] [Fintype ι] in
lemma scale (h : Elation H A B) (t : ℝ) : Elation H (t•A) (t•B) := by
  intro i j; change t • block B i j = _*(t • block A i j)*_; rw [h,Matrix.mul_smul,Matrix.smul_mul]
omit [DecidableEq ι] [DecidableEq κ] [Fintype ι] in
lemma opposite (h : Elation H A B) : Elation H (-A) (-B) := by simpa only [neg_one_smul] using h.scale (-1)
omit [DecidableEq ι] in
lemma times (hi : Moves H) (h : Elation H A B) {C D : Square (ι×κ)} (hc : Elation H C D) : Elation H (A*C) (B*D) := by
  intro i j; rw [factor,factor,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by rw [h,hc,rectangle hi]
omit [DecidableEq ι] [DecidableEq κ] [Fintype ι] in
lemma reflects (h : Elation H A B) : Elation H A.transpose B.transpose := by
  intro i j; change (block B j i).transpose=_*(block A j i).transpose*_
  rw [h,Matrix.transpose_mul,Matrix.transpose_mul,transpose_transpose,Matrix.mul_assoc]

-- Work only with *the positive reference* inverse; can show inverse mapping also as total function incl defaults,
-- but unnecessary here.
lemma inverted (hi : Moves H) (h : Elation H A B) (ha : IsUnit A.det) : Elation H A⁻¹ B⁻¹ := by
  let C : Square (ι×κ) := Matrix.of fun i j=> (H i.1 * block A⁻¹ i.1 j.1 * (H j.1).transpose) i.2 j.2
  have hc : Elation H A⁻¹ C := fun _ _=> rfl
  have ht := h.times hi hc
  rw [Matrix.mul_nonsing_inv _ ha] at ht
  have hp : B*C=1 := by ext ⟨i,u⟩ ⟨j,v⟩; exact congr_fun (congr_fun ((ht i j).trans (colorless hi i j).symm) u) v
  rw [Matrix.inv_eq_right_inv hp]; exact hc
lemma shifted (hi : Moves H) (h : Elation H A B) (ha : A.PosDef) (t : ℝ) (ht : 0≤t) : Elation H (resolve A t) (resolve B t) :=
  (h.add ((colorless hi).scale t)).inverted hi (IsUnit.mk0 _ (shift_posDef ha ht).det_pos.ne')
end Elation

def all (W : ι→Set ι) (k : ι×κ) : Set (ι×κ) := {j|j.1 ∈ W k.1}

def restrict (W : Set ι) : (W×κ) ↪ ι×κ := Embedding.prodMap (Embedding.subtype _) (Embedding.refl _)
omit [DecidableEq ι] [DecidableEq κ] [Fintype ι] in
lemma select (h : Elation H A B) (W : Set ι) : Elation (H ∘ ((↑) : W→ι))
    (A.submatrix (restrict W) (restrict W)) (B.submatrix (restrict W) (restrict W)) := fun _ _=> h _ _

def within (W : Set ι) : (W × κ) ≃ {x : ι×κ | x.1 ∈ W} where
  toFun v:= ⟨restrict W v,v.1.2⟩
  invFun v:= (⟨v.val.1,v.2⟩,v.val.2)
  left_inv _:=rfl
  right_inv _:=rfl

lemma read_pie (W : ι→Set ι) (A : Square (ι×κ)) (t : ℝ) (i j : ι) (hi : i∈ W j) (hj : j∈W j) :
    block (pie (all W) A t) i j=block (resolve (A.submatrix (restrict (W j)) (restrict (W j))) t) ⟨i,hi⟩ ⟨j,hj⟩ := by
  ext u v; unfold block
  rw [of_apply,of_apply,pie_read (all W) A t (i,u) (j,v) hi hj]
  let g : (W j × κ) ≃ all W (j,v) := within (W j)
  have he:= resolve_equiv g (Schur.principal A (all W (j,v))) t
  exact (congr_fun (congr_fun he (⟨i,hi⟩,u)) (⟨j,hj⟩,v)).symm
lemma closed_pie (W : ι → Set ι) (A : Square (ι×κ)) (t : ℝ) (i j : ι) (hx : i∉W j) : block (pie (all W) A t) i j=0 := Matrix.ext fun _ _=> pie_miss _ _ _ _ _ hx
lemma caught (W : ι→Set ι) (hw : ∀ i,i∈W i) (hi : Moves H) (h : Elation H A B) (ha : A.PosDef) (t : ℝ) (ht : 0≤t) :
    Elation H (pie (all W) A t) (pie (all W) B t) := by
  intro i j; by_cases he : i∈W j
  · rw [read_pie _ _ _ i j he (hw j),read_pie _ _ _ i j he (hw j)]
    exact (select h _).shifted (fun x=>hi x.val) (ha.submatrix (restrict _).injective) t ht (⟨i,he⟩:W j) (⟨j,hw j⟩:W j)
  rw [closed_pie _ _ _ _ _ he,closed_pie _ _ _ _ _ he]; simp
lemma circles (W : ι→Set ι) (hw : ∀ i,i∈W i) (hi : Moves H) (h : Elation H A B) (ha : A.PosDef) (t : ℝ) (ht : 0≤t) :
    Elation H (defect (all W) A t) (defect (all W) B t) := by
  unfold defect; rw [sub_eq_add_neg,sub_eq_add_neg]
  exact ((h.add ((Elation.colorless hi).scale t)).times hi (caught W hw hi h ha t ht)).add ((Elation.colorless hi).opposite)
lemma cursed (W : ι→Set ι) (hw : ∀ i,i∈W i) (hi : Moves H) (h : Elation H A B) (ha : A.PosDef) :
    Elation H (excess (all W) A) (excess (all W) B) := by
  unfold excess; rw [sym_cloud,sym_cloud,sub_eq_add_neg,sub_eq_add_neg]
  have he := caught W hw hi h ha 0 le_rfl
  exact (h.times hi ((he.add he.reflects).scale _)).add (Elation.colorless hi).opposite
end YM.AnalyticBridge.RelativeLogdet.Paint
