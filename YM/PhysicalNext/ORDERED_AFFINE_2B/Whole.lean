import YM.Further.CURVED_GAUSSIAN_JETS.Bridge
import YM.Further.CURVED_GAUSSIAN_JETS.Law
import YM.Further.CURVED_GAUSSIAN_JETS.LocalJets
import YM.PhysicalNext.ORDERED_AFFINE_2B.Padding
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Reads


/-!
# Ordering on one full alphabet for the paired log and Frco

Compute everything from literal tables (inactive entries combined
algebraically, never independent flags). Do the ORDERED route on ALL
physical positive bond/color keys `Atom`, including the tree. Permute
back to `ActualScalar` memory layout; determinants get no extra terms
from this temporary identity completion. Frozen-link MASS in the scalar
remains explicit; extra coordinates MUST NOT be counted there. All
transforms incl these lookups in SectorChange's endpoint convention for
`panels`, budgeted into `Tracks` support currency later. Retains ALL
window arguments and exterior generator reads from A. No equality or
operation corresponding to re-truncating COMPRESSED A's D-rows. This
part still before any analytic assertions; when issuing estimates need
post-L spectral, eta/g, support budgets later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Whole
open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree
open AnalyticBridge AnalyticBridge.SectorAffine AnalyticBridge.Covariance AnalyticBridge.Covariance.Terrain
open AnalyticBridge.ResetIncome SectorTools.ActualScalar
open Further Further.CurvedGaussianJets
open Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Completion
open Push.SectorMeasure Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {c f : Side} {G : Gauge} {S : StepData c f}
abbrev Thing (G : Gauge) (f : Side) := Covariance.Atom G f
abbrev initial (G : Gauge) (f : Side) (i : Thing G f) := i.1.1

section wood
variable (F : Forest S.ratio) (G : Gauge) (e : Plate G S) (he : Doors e)

abbrev Lumber := ↥F.trunks × G.ColorIndex

def allThings : Key F G ⊕ Lumber F G ≃ Thing G f where
  toFun x := x.elim (fun i => (i.1.val,i.2)) (fun i=> (i.1.val,i.2))
  invFun i := if hi : i.1 ∈ F.trunks then Sum.inr (⟨i.1,hi⟩,i.2) else Sum.inl (⟨i.1,hi⟩,i.2)
  left_inv i := by rcases i with i|i <;> simp [i.1.property]
  right_inv i := by dsimp only; split <;> rfl

variable {G} (A : Stores S) (t : S.Choices) (V : Config G c)
lemma below (p : Bond f) (h : p ∈ e.forest.trunks) (u : G.ColorIndex) (j : Thing G f) :
    scanA e.tube A e.forest t e.x V j (p,u) = (1:CurvedGaussianJets.Table (Thing G f)) j (p,u) := by
  have he : ¬onStage A e.forest e.x p := fun he=>he.1 h
  unfold scanA shard; rw [Matrix.add_apply,Matrix.mul_apply]
  simp_rw [show ∀ k, scanD e.tube A e.forest t e.x V k (p,u)=0 from fun k=>if_neg he,mul_zero,Finset.sum_const_zero,zero_add,Matrix.one_apply]
  by_cases hh : j=(p,u)
  · subst j; rw [diagonal_apply_eq,if_neg (show ¬ onStage A e.forest _ _ from he),if_pos rfl]
  rw [diagonal_apply_ne _ hh,if_neg hh]

lemma across (Y : GaussianScalar.Frozen (held e A) G) :
    scanA e.tube A e.forest t e.x V = Joint.place (allThings e.forest G) (Joint.join ((page e he A t V).sigma Y) 1) := by
  let X := scanA e.tube A e.forest t e.x V
  let W := allThings e.forest G
  have hX : X.IsSymm := by unfold X scanA shard Matrix.IsSymm; simp
  ext i j; obtain ⟨(i|i),rfl⟩ := W.surjective i <;> obtain ⟨(j|j),rfl⟩ := W.surjective j <;>
    change X _ _ = (Joint.join _ _) (W.symm _) (W.symm _) <;> rw [W.symm_apply_apply,W.symm_apply_apply] <;> unfold X
  · exact congr_fun (congr_fun (Locations.scan_restrict he A t V Y) i) j |>.symm
  · rw [show W (.inr j)=(j.1.val,j.2) from rfl,below e A t V j.1 _ j.2 _]
    · change (1:CurvedGaussianJets.Table _) _ _ = 0; apply Matrix.one_apply_ne
      change W (.inl i) ≠ W (.inr j); simp
    exact j.1.property
  · change X _ _ = _; rw [hX.apply]; unfold X; rw [show W (.inr i)=(i.1.val,i.2) from rfl,below e A t V i.1 _ i.2 _]
    · change (1:CurvedGaussianJets.Table _) _ _ = 0; apply Matrix.one_apply_ne
      change W (.inl j) ≠ W (.inr i); simp
    exact i.1.property
  · rw [show W (.inr j)=(j.1.val,j.2) from rfl,below e A t V j.1 _ j.2 _]
    · change (1:CurvedGaussianJets.Table _) (W (.inr i)) (W (.inr j)) = (1:CurvedGaussianJets.Table _) i j
      simp [Matrix.one_apply]
    exact j.1.property
end wood

section ghost
variable (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c)

abbrev charter := scanA T A F k x
abbrev flat := scanA T noHole F k x 1

def windows (S : StepData c f) (G : Gauge) (x : ℝ) (hx : 120 ≤ radiusB x) : CurvedGaussianJets.Windows (Thing G f) where
  box i := Finset.univ.filter fun j=> j∈unitWin S x i
  within i := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Footprint.Padded.push_if x i hx⟩
variable (hx : 120 ≤ radiusB x)

lemma wind (i j : Thing G f) : i∈(windows S G x hx).box j ↔ meeting S x j.1 i.1 := by simp [windows,unitWin]
lemma column (u : ℝ) :
    (windows S G x hx).column (charter T x A F k V) u = lookPi T A F k x u V := by
  let W := windows S G x hx
  let L : Thing G f → Set (Thing G f) := fun i => W.box i
  have he : L = unitWin S x := by ext i j; exact wind x hx j i
  unfold lookPi; rw [←he]
  let X := charter T x A F k V
  ext i j; change W.column X u i j=Schur.per L (X+u•1) i j
  by_cases hv : i∈L j
  swap
  · rw [Schur.per_zero _ _ hv]; exact dif_neg hv
  rw [Schur.per_read L (X+u•1) (W.within j) hv]
  let α := Schur.principal (X+u•1) (L j)
  have hα : α=shifted (W.localGram X j) u := by
    ext i j; simp [α, CurvedGaussianJets.shifted, Schur.principal,Windows.localGram,Matrix.one_apply]
  unfold Windows.column; rw [Matrix.of_apply,dif_pos (show i∈ W.box j from hv)]; unfold Windows.resolvent
  rw [←hα]; congr!

lemma blend : (windows S G x hx).blend (charter T x A F k V) = lookC T A F k x V := by
  unfold Windows.blend; rw [column]; ext i j; rw [C_read]; rfl

def identityPut (C : Gaussian.Table (Rows.In x A F (G:=G))) := Joint.place (sorted A F (x:=x)) (wide C 1)
lemma back (C : Gaussian.Table (Thing G f)) (L : Gaussian.Table (Rows.In x A F (G:=G)))
    (h : backPrice A F x C = wide L 1) : C=identityPut x A F L := by
  unfold identityPut Joint.place; rw [←h]; simp [backPrice, Matrix.submatrix_submatrix]
lemma plinth : charter T x A F k V = identityPut x A F (Fixed.precision T x A F k V) := back x A F _ _ (backA ..)
lemma actual_cloud {η : ℝ} (hη : 0<η) (hg : Schur.Gapped (Fixed.precision T x A F k V) η) :
    Jets.covariance (windows S G x hx) (charter T x A F k) V = identityPut x A F (Fixed.covariance T x A F k V) := by
  unfold Jets.covariance; rw [blend]; refine back x A F _ _ (by rw [backC]; exact (stocked _ _ _ _ _ _ hη hg hx).2.1)

lemma det_back (C : Gaussian.Table (Rows.In x A F (G:=G))) : (identityPut x A F C).det=C.det := by
  unfold identityPut; rw [show wide C (1:Gaussian.Table (vacant A F x G))=Joint.join C 1 from rfl,Joint.place_det,Matrix.det_one,mul_one]
end ghost
end YM.PhysicalNext.OrderedAffine2B.Whole
