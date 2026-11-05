import YM.Push.FREE_RESOLVENT.Flat
import YM.Push.FREE_RESOLVENT.Inverse
import YM.Push.FREE_RESOLVENT.Probe
import YM.Push.FREE_RESOLVENT.Torus


/-!
# Assembly of the actual period-independent flat precision stencil and prices

Displacement in full block row in COARSE units, full fine positions and
colors as extra types. This enables period comparison with irregular tree
selections; the *inverse on the slice* need not be translation-invariant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F08
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {c f n L : Side} {S : StepData c f} {G : Gauge}

section block
variable {α β : Type*}

/-- A square fine row, reblocked using F08 composition (there's no period in
its construction). -/
def reblock (L : Side) [Fintype α] [DecidableEq α] (H : Row α α) : Row (Co L α) (Co L α) :=
  fineCompose H (unitRow _)
lemma reblock_price [Fintype α] [DecidableEq α] {H : Row α α} {σ M : ℝ} (hs : 0 ≤ σ) (h : H.strip σ M) :
    (reblock L H).strip σ ((Fintype.card α:ℝ)*M) := by
  unfold reblock; simpa using strip_fine (L:=L) hs h (strip_unit (α:=Co L α))
lemma reblock_periods [Fintype α] [DecidableEq α] {H : Row α α} (g : Ratio c f) {σ M : ℝ} (hs : 0 ≤ σ) (h : H.strip σ M) :
    H.acts f = ((reblock g.count H).acts c).submatrix (splitCo g α) (splitCo g α) := by
  let E := splitCo g α
  have he : installed g (unitRow (Co g.count α)) = (1 : Matrix _ _ ℝ).submatrix E id := by
    unfold installed; rw [acts_unit]
  ext i j
  change _ = installed g (reblock g.count H) i (E j)
  rw [reblock, installed_fine _ hs h strip_unit, he]
  simp [Matrix.mul_apply, Matrix.one_apply,E.injective.eq_iff]

lemma probeGram (S : StepData c f) :
    (probe S).transpose * probe S =
    ((composeRows (transRows (probeRow S.patch)) (probeRow S.patch)).acts c).submatrix
      (splitCo S.ratio (TypeFace 1)) (splitCo S.ratio (TypeFace 1)) := by
  obtain ⟨B,-,h⟩ := probe_ready S.patch 0 le_rfl
  rw [block_probe, acts_compose le_rfl (strip_trans h) h, acts_trans]
  rfl

def hBlock (H : FaceRow) := composeRows (transRows (cobound 1)) (composeRows H (cobound 1))
def dPrice (s : ℝ) := (cobound_ready 1 s).choose
def kinPrice (s M : ℝ) :=
  let d := dPrice s
  let n : ℝ := Fintype.card (TypeFace 2)
  n*(d*(n*(M*d)))
lemma kinPrice_nn (s M : ℝ) (hm : 0 ≤ M) : 0 ≤ kinPrice s M := by
  have h : 0 ≤ dPrice s := (cobound_ready 1 s).choose_spec.1
  unfold kinPrice; positivity
lemma hBlock_width {H : FaceRow} {s M : ℝ} (hs : 0 ≤ s) (h : H.strip s M) : (hBlock H).strip s (kinPrice s M) := by
  have hc := (cobound_ready 1 s).choose_spec.2
  exact strip_compose hs (strip_trans hc) (strip_compose hs h hc)
lemma hBlock_periods {H : FaceRow} {s M : ℝ} (hs : 0 ≤ s) (h : H.strip s M) (f : Side) :
    (hBlock H).acts f = Precision.K (H.acts f) := by
  have hc := (cobound_ready 1 s).choose_spec.2
  rw [hBlock, acts_compose hs (strip_trans hc) (strip_compose hs h hc), acts_trans, acts_compose hs h hc, Precision.K, Matrix.mul_assoc]

def outputPrice (P : Patch) (k s M : ℝ) :=
  let A := (probe_ready P (max s 0) (le_max_right ..)).choose
  (Fintype.card (TypeFace 1):ℝ)*kinPrice s M + ‖k‖ * ((Fintype.card (TypeFace 1):ℝ)*(A*A))
lemma outputPrice_nn (P : Patch) (k s M : ℝ) (hm : 0 ≤ M) : 0 ≤ outputPrice P k s M := by
  have ha := (probe_ready P (max s 0) (le_max_right ..)).choose_spec.1
  have h := kinPrice_nn s M hm
  unfold outputPrice; positivity

/-- Period-free counting stencil on block origins. -/
def flatRow (P : Patch) (k : ℝ) (H : FaceRow) : Row (Co P.L (TypeFace 1)) (Co P.L (TypeFace 1)) :=
  plusRows (reblock P.L (hBlock H)) (scaleRows k (composeRows (transRows (probeRow P)) (probeRow P)))
lemma flatRow_strip (P : Patch) (k : ℝ) {H : FaceRow} {s M : ℝ} (hs : 0 ≤ s) (h : H.strip s M) :
    (flatRow P k H).strip s (outputPrice P k s M) := by
  have hh := strip_mono (probe_ready P (max s 0) (le_max_right ..)).choose_spec.2 (le_max_left ..) le_rfl
  exact strip_plus (reblock_price hs (hBlock_width hs h)) (strip_scale (strip_compose hs (strip_trans hh) hh) _)
lemma flatRow_periods (S : StepData c f) {s M : ℝ} {H : FaceRow} (hs : 0 ≤ s) (h : H.strip s M) :
    baseMatrix S H = ((flatRow S.patch S.kernel.penalty H).acts c).submatrix
      (splitCo S.ratio (TypeFace 1)) (splitCo S.ratio (TypeFace 1)) := by
  have hh := hBlock_width hs h
  obtain ⟨Q,-,hp⟩ := probe_ready S.patch s hs
  rw [flatRow, acts_plus (reblock_price hs hh) (strip_scale (strip_compose hs (strip_trans hp) hp) _) hs,
    acts_scale, Matrix.submatrix_add, Matrix.submatrix_smul, baseMatrix, probeGram, ← hBlock_periods hs h]
  congr 1; exact reblock_periods S.ratio hs hh

/-- Tensor on site-expanded row coordinates. -/
def colorRow (G : Gauge) {r : ℕ} (A : Row (Co L (TypeFace r)) (Co L (TypeFace r))) :
    Row (Co L (PAC G r)) (Co L (PAC G r)) := fun i j z =>
  if i.2.2=j.2.2 then A (i.1,i.2.1) (j.1,j.2.1) z else 0

def fullRow (G : Gauge) (P : Patch) (k : ℝ) (H : FaceRow) := colorRow G (flatRow P k H)

lemma fullRow_periods (S : StepData c f) {s M : ℝ} {H : FaceRow} (hs : 0 ≤ s) (h : H.strip s M) :
    fullMatrix G S H = ((fullRow G S.patch S.kernel.penalty H).acts c).submatrix
      (splitCo S.ratio (PAC G 1)) (splitCo S.ratio (PAC G 1)) := by
  ext ⟨x,i,j⟩ ⟨y,b,k⟩
  by_cases he : j=k
  · rw [fullMatrix,flatRow_periods S hs h,tensor,Matrix.of_apply,if_pos he,Matrix.submatrix_apply,Matrix.submatrix_apply,
      split_co,split_co,split_co,split_co]
    simp only [fullRow, Row.acts,colorRow,Matrix.of_apply,if_pos he]; rfl
  rw [fullMatrix,tensor,Matrix.of_apply,if_neg he,Matrix.submatrix_apply,split_co,split_co]
  simp [fullRow,Row.acts,colorRow,he]

lemma fullRow_width (P : Patch) (k : ℝ) {H : FaceRow} {s M : ℝ} (hs : 0 ≤ s) (hm : 0 ≤ M) (h : H.strip s M) :
    (fullRow G P k H).strip s (outputPrice P k s M) := by
  intro i j
  by_cases hi : i.2.2=j.2.2
  · unfold fullRow
    rw [show colorRow G _ i j = flatRow P k H (i.1,i.2.1) (j.1,j.2.1) from funext fun _ => if_pos hi]
    exact flatRow_strip _ _ hs h _ _
  simp [fullRow,colorRow,hi,Laurent.Width,RG.SumBudget,outputPrice_nn P k s M hm]
end block

-- width (tile exponent) converted to physical Schur
def theta (g : Ratio c f) (T : Forest g) (i : Active G T) : Site c := g.parent i.1.val.1

def billing (G : Gauge) (P : Patch) (k s M : ℝ) :=
  (Fintype.card (Co P.L (PAC G 1)):ℝ)*outputPrice P k s M
lemma billing_nn (G : Gauge) (P : Patch) (k s M : ℝ) (hm : 0 ≤ M) : 0 ≤ billing G P k s M :=
  mul_nonneg (by positivity) (outputPrice_nn P k s M hm)
lemma fullSchur (S : StepData c f) {s M : ℝ} {H : FaceRow} (hs : 0 ≤ s) (hm : 0 ≤ M) (h : H.strip s M) :
    (native c).Schur (S.ratio.parent ∘ Prod.fst) (S.ratio.parent ∘ Prod.fst) s
      (billing G S.patch S.kernel.penalty s M) (fullMatrix G S H) := by
  let E := splitCo S.ratio (PAC G 1)
  -- equality of locations, not by arbitrary identification of forest
  have he : Prod.fst ∘ E = S.ratio.parent ∘ Prod.fst := funext fun i => by simp [E,split_co]
  rw [fullRow_periods S hs h, ← he]
  exact (physical (fullRow_width S.patch _ hs hm h) hs c).submatrix E.injective E.injective
lemma treeSchur (S : StepData c f) (T : Forest S.ratio) {s M : ℝ} {H : FaceRow} (hs : 0 ≤ s) (hm : 0 ≤ M) (h : H.strip s M) :
    (native c).Schur (theta S.ratio T) (theta S.ratio T) s (billing G S.patch S.kernel.penalty s M) (treeMatrix G S T H) :=
  (fullSchur S hs hm h).submatrix (plant_inj T) (plant_inj T)

lemma treeVolume (S : StepData c f) (T : Forest S.ratio) {s : ℝ} (hs : 0 < s) :
    (native c).Volume (theta S.ratio T (G:=G)) s (torusPay (Co S.patch.L (PAC G 1)) s) := by
  let E := splitCo S.ratio (PAC G 1)
  have he : (theta S.ratio T) = Prod.fst ∘ (E ∘ plant (G:=G) T) := by ext; rw [Function.comp_apply,Function.comp_apply]; unfold E; rw [split_co]; rfl
  rw [he]; exact (volume c _ s hs).comp (E.injective.comp (plant_inj T))

/-- Symbolic schedule price. Radii/periods later; here ALL hold
once Larger is met (explicit geometric condition and Branches). No beta. -/
def expansion (G : Gauge) (P : Patch) (K : KernelChoices) (s M a : ℝ) :=
  safeRate s (billing G P K.penalty s M) (treeFare G P K a)



end YM.FreeResolvent
