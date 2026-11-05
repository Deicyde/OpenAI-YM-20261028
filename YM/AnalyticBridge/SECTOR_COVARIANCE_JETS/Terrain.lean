import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Coloring

set_option warningAsError false

/-!
# Complete lookup for precision and symmetrized covariance

This file relates the completed presentation to calculation of A,
Π,C, E_u, S letters on a fixed set of coordinates in the physical
common orientation. `Outside` interpretation via actual entries in
Chalet. Membership of a coordinate at all is not the value of its
Gaussian multiplier. The V-predicate of the measure is still a
(global) flag-clause, separate from such numerical reads.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance.Terrain
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Precision Exterior Bloch Tree Matrix
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Completion FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent (native Bundle Cost)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x u : ℝ}

/-- Coordinates ON in the literal approximation. -/
def onStage (A : Stores S) (F : Forest S.ratio) (x : ℝ) (e : Bond f) :=
    e∉F.trunks ∧ S.ratio.parent e.1∉A.dome (10*radiusB x) ∧ S.ratio.parent (e.1+step e.2)∉A.dome (10*radiusB x)
lemma acts_here (A : Stores S) (F : Forest S.ratio) {e : Bond f} :
    onStage A F x e ↔ ∃ i : Active A x F, i.val.val=e := by
  constructor
  · rintro ⟨hv,hh,hk⟩; exact ⟨⟨⟨e,hv⟩,fun h => h.elim hh hk⟩,rfl⟩
  rintro ⟨⟨⟨e,ht⟩,hp⟩,rfl⟩; exact ⟨ht,fun he => hp (Or.inl he),fun he => hp (Or.inr he)⟩

def scanD (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x : ℝ) (V : Config G c) :
    Matrix (Receipt G S) (Atom G f) ℝ := Matrix.of fun i j => if onStage A F x j.1 then
      tape.symm (Rows.selected T x V t (shots S x) A F (atom j)) i else 0

def shard (A : Stores S) (F : Forest S.ratio) (x : ℝ) : Gaussian.Table (Atom G f) := diagonal fun j => if onStage A F x j.1 then 0 else 1

def scanA (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x : ℝ) (V : Config G c) :=
  (scanD T A F t x V).transpose*scanD T A F t x V+shard A F x

def unitWin (S : StepData c f) (x : ℝ) (i : Atom G f) := {j : Atom G f | meeting S x i.1 j.1}

def lookPi (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x u : ℝ) (V : Config G c) := per (unitWin S x) (scanA T A F t x V + u • 1)

def lookC (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x : ℝ) (V : Config G c) := clouded (unitWin S x) (scanA T A F t x V)

def backPrice (A : Stores S) (F : Forest S.ratio) (x : ℝ) (M : Gaussian.Table (Atom G f)) := M.submatrix (sorted A F (x:=x)) (sorted A F (x:=x))

lemma exits (A : Stores S) (F : Forest S.ratio) (j : vacant A F x G) : ¬onStage A F x j.val.1 := by
  rw [acts_here]; rintro ⟨i,h⟩
  apply j.property; refine ⟨(i,j.val.2),Prod.ext ?_ rfl⟩; exact h.symm
lemma pick (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x : ℝ) (V : Config G c) (i : Receipt G S) (j : Layer G A F x) :
    scanD T A F t x V i (sorted A F j) = j.elim (Rows.move T x V t (shots S x) A F i) (fun _ => 0) := by
  unfold scanD; rw [Matrix.of_apply]
  cases j with
  | inl j =>
    have hs := (acts_here A F).mpr (show ∃ i : Active A x F, i.val.val=j.1.val.val from ⟨j.1,rfl⟩)
    rw [if_pos (show onStage A F x ((sorted A F) (Sum.inl j)).1 from hs)]; dsimp only [Sum.elim_inl,Rows.move, Matrix.of_apply]
    rw [fresh_atom]; rfl
  | inr j => rw [sorted_last,if_neg (exits A F j)]; rfl

lemma backA (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x : ℝ) (V : Config G c) :
    backPrice A F x (scanA T A F t x V) = wide (gram T x V t (shots S x) A F) 1 := by
  let h : Layer G A F x → Atom G f := sorted A F
  have he (i j : Layer G A F x) : shard A F x (h i) (h j) = (wide (0:Gaussian.Table (In x A F (G:=G))) 1 i j) := by
    let Q : Gaussian.Table (In x A F (G:=G)) := 0
    by_cases hr : i=j
    · subst j
      rw [shard, diagonal_apply_eq]
      cases i with
      | inl i => rw [if_pos (show onStage A F x (h (Sum.inl i)).1 from (acts_here A F).mpr ⟨i.1,rfl⟩)]
                 rfl
      | inr i => rw [if_neg (show ¬onStage A F x (h (Sum.inr i)).1 from exits A F i)]; simp [wide]
    rw [shard,diagonal_apply_ne _ (show h i ≠ h j from (fun he => hr ((sorted A F).injective he)))]
    rcases i with i|i <;> rcases j with j|j <;> try rfl
    change 0=(1:Gaussian.Table _) i j; rw [Matrix.one_apply, if_neg (mt (congr_arg Sum.inr) hr)]
  unfold backPrice; ext i j
  simp only [Matrix.submatrix_apply,scanA,Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, pick]
  rw [show shard A F x _ _=_ from he i j]
  cases i <;> cases j <;> simp [Rows.gram,wide,Matrix.mul_apply]

-- Reindex per. No gap assumption.
section coordinate
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

private def subEqv (t : Set β) (e : α ≃ β) : (e ⁻¹' t) ≃ t where
  toFun i := ⟨e i.val,i.property⟩
  invFun i := ⟨e.symm i.val,by rw [Set.mem_preimage,e.apply_symm_apply]; exact i.property⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i.val)
  right_inv i := Subtype.ext (e.apply_symm_apply i.val)

lemma reindexWin (e : α ≃ β) (W : β → Set β) (A : Gaussian.Table β) :
    (per W A).submatrix e e = per (fun i => e ⁻¹' W (e i)) (A.submatrix e e) := by
  ext j i; rw [Matrix.submatrix_apply]
  by_cases hi : e i ∈ W (e i)
  swap
  · unfold per; rw [Matrix.of_apply, Matrix.of_apply, dif_neg hi,dif_neg (show i ∉ (fun i => e ⁻¹' W (e i)) i from hi)]
  by_cases hj : e j ∈ W (e i)
  swap
  · exact (per_zero W A hj).trans (per_zero (fun i => e ⁻¹' W (e i)) _ hj).symm
  let H k := e ⁻¹' W (e k)
  let E := subEqv (W (e i)) e
  have hs : principal (A.submatrix e e) (H i) = (principal A (W (e i))).submatrix E E := rfl
  have hi' : i∈H i := hi; have hj' : j∈H i := hj
  change per W A (e j) (e i) = per H _ _ _
  rw [per_read W A hi hj, per_read H (A.submatrix e e) hi' hj',hs, Matrix.inv_submatrix_equiv]; rfl
lemma reindexCloud (e : α ≃ β) (W : β → Set β) (A : Gaussian.Table β) :
    (clouded W A).submatrix e e = clouded (fun i => e ⁻¹' W (e i)) (A.submatrix e e) := by
  unfold clouded; rw [← reindexWin]; rfl
end coordinate
lemma back_shift (A : Stores S) (F : Forest S.ratio) (x : ℝ) (M : Gaussian.Table (Atom G f)) (u : ℝ) :
    backPrice A F x (M + u•1)=backPrice A F x M + u•1 := by
  ext i j; simp [backPrice, Matrix.one_apply]

lemma backPi (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x u : ℝ) (V : Config G c) :
    backPrice A F x (lookPi T A F t x u V) = per (allPanels A F) (wide (gram T x V t (shots S x) A F) 1+ u • 1) := by
  rw [← backA,←back_shift]; unfold backPrice lookPi
  have hx := reindexWin (sorted A F (G:=G) (x:=x)) (unitWin S x) (scanA T A F t x V + u • 1)
  rw [show (fun i => (sorted A F (x:=x) (G:=G)) ⁻¹' unitWin S x (sorted A F i)) =
    allPanels A F from funext (fun i => by ext k; rfl)] at hx
  convert hx using 3
lemma backC (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x : ℝ) (V : Config G c) :
    backPrice A F x (lookC T A F t x V)=clouded (allPanels A F) (wide (gram T x V t (shots S x) A F) 1) := by
  rw [← backA]; unfold backPrice lookC
  have hx := reindexCloud (sorted A F (x:=x) (G:=G)) (unitWin S x) (scanA T A F t x V)
  rw [show (fun i => (sorted A F (x:=x) (G:=G)) ⁻¹' unitWin S x (sorted A F i)) =
    allPanels A F from funext (fun i => by ext k; rfl)] at hx
  convert hx using 1
end YM.AnalyticBridge.Covariance.Terrain
