import YM.Push.FREE_RESOLVENT.Masking
import YM.Push.FREE_RESOLVENT.Midpoint
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Completion


set_option warningAsError false

/-!
# Two actual window conventions on one RG step

`SectorChange.Chosen` uses
maximum over projected *endpoint* pairs.

`FreeResolvent.Mid` models physical
*midpoints*.

Keep both color-complete cuts.

Here are exact adapters (not an
assertion the cuts agree).

Inactive counting slots may be dropped or padded
by identity **before** taking shifted principal matrices, retaining boundary
rows of the very same Gram.

Full window readings are related below even on
the period seam.

Haar factors on frozen links are NOT part of this algebraic
completion.

None of these projections eliminate momentum-zero directions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment
open Function Filter Set Lattice Wilson RG Precision Exterior Tree Matrix
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Completion
open Pressure Pressure.Tube Pressure.Stores Bid
open scoped Topology BigOperators Classical ContDiff Completion

variable {G : Gauge} {c f : Side} {S : StepData c f}

-- Axis/outcome orders, not just types of covariance matrices.
abbrev Raw (G : Gauge) (f : Side) := FreeResolvent.Affine.raw G f

def asSlot : Bond f × G.ColorIndex ≃ Raw G f where
  toFun i := (i.1.1,axisEquiv i.1.2,i.2)
  invFun j := (FreeResolvent.Mid.cull j, j.2.2)
  left_inv i := by change ((_,axisEquiv.symm (axisEquiv _)),_) = _; rw [axisEquiv.symm_apply_apply]
  right_inv i := by simp [FreeResolvent.Mid.cull]

variable (A : Stores S) (F : Forest S.ratio) (x : ℝ)

def live : In x A F (G:=G) ↪ Precision.Key F G where
  toFun i := (i.1.val,i.2)
  inj' := by rintro ⟨i,k⟩ ⟨j,l⟩ he; cases Prod.mk.inj he; congr; exact Subtype.ext (Prod.mk.inj he).1

def address : In x A F (G:=G) ↪ Raw G f where
  toFun i := FreeResolvent.plant F (live A F x i)
  inj' := (FreeResolvent.plant_inj F).comp (live A F x).injective


lemma cull_address (i : In x A F (G:=G)) : FreeResolvent.Mid.cull (address A F x i) = i.1.val.val := by
  change (_,axisEquiv.symm (axisEquiv _)) = _; rw [axisEquiv.symm_apply_apply]; rfl

def sortSlots : (In x A F (G:=G) ⊕ vacant A F x G) ≃ Raw G f := (sorted A F).trans asSlot
lemma sort_first (i : In x A F (G:=G)) : sortSlots A F x (.inl i) = address A F x i := rfl

open FreeResolvent.Mid (cull window cutView)
-- Keep all components when taking either prescription.
def endsAt (S : StepData c f) (x : ℝ) (i : Raw G f) : Set (Raw G f) := {j | meeting S x (cull i) (cull j)}
def midsAt (S : StepData c f) (x : ℝ) (i : Raw G f) : Set (Raw G f) := window S (radiusB x) i

def mids (i : In x A F (G:=G)) := address A F x ⁻¹' midsAt S x (address A F x i)

lemma panels_eq (i : In x A F (G:=G)) : panels A F i = address A F x ⁻¹' endsAt S x (address A F x i) := by
  ext j; simp only [panels, mem_preimage, endsAt, cull_address,mem_setOf_eq]

lemma ends_self (he : 120 ≤ radiusB x) (i : Raw G f) : i ∈ endsAt S x i := by
  intro y hy z hz
  have ht := meetings (S:=S) _ hy; have ht' := meetings (S:=S) _ hz; rw [separation_comm] at ht
  exact (separation_triangle y (S.ratio.parent (cull i).1) z).trans (show _ ≤ _ from by omega)

lemma mids_self (i : Raw G f) : i ∈ midsAt S x i := FreeResolvent.Mid.member ..

lemma mids_bars (h : 120 ≤ radiusB x) : Schur.Bars (mids (G:=G) A F x) (Wisps.front A F) (radiusB x / 60) := by
  intro i j hj
  have H := FreeResolvent.Mid.priced S (address A F x i) (address A F x j)
  let L := S.patch.L.val
  let q := separation (Wisps.front A F i) (Wisps.front A F j)
  change _ ≤ 2*(L*q+L)+2 at H
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,(Nat.mul_le_mul_left 20 H).trans ?_⟩
  have hq : q*60 ≤ radiusB x := Nat.mul_le_of_le_div 60 _ _ hj
  have hL : 3 ≤ L := S.patch.coarse
  change 20*(2*(L*q+L)+2) ≤ 2*L*radiusB x
  nlinarith [Nat.mul_le_mul_left L hq, Nat.mul_le_mul_left L h]

/-- Build a Survey using actual Sector address lists. No weight conventions
entered here. Endpoints may fail to include self if used too early! -/
def view {α : Type} (P : α → Set α) (h : ∀ i, i∈P i) : FreeResolvent.Window.Survey (fun i => ↥(P i)) where
  loc _ := Function.Embedding.subtype _
  root i := ⟨i,h i⟩
  atRoot _ := rfl

section generic
variable {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

lemma per_view (P : α → Set α) (h : ∀ i,i∈P i) (Q : Gaussian.Table α) :
    (view P h).inspect Q 0 = Schur.per P Q := by
  ext i j; let T := view P h
  change FreeResolvent.Pane.column Q (T.loc j) 0 (T.root j) i = Schur.per P Q i j
  by_cases hi : i∈P j
  · let u : P j := ⟨i,hi⟩
    rw [show FreeResolvent.Pane.column Q _ 0 _ i = _ from FreeResolvent.Pane.local_entry Q 0 (T.loc j) (T.loc j).injective (T.root j) u,
      Schur.per_read _ _ (h j) hi]; unfold FreeResolvent.Pane.thin FreeResolvent.resolve
    rw [zero_smul,add_zero]; rfl
  rw [FreeResolvent.Pane.unused _ _ _ _ _ (fun ⟨k,hk⟩ => hi (hk ▸ k.property)),Schur.per_zero _ _ hi]

/-- All subsequent arithmetic is unchanged by a common permutation of
addresses *and their window lists*, with the same precision under reindexing.
No symmetry or invertibility needed here. -/
lemma per_relabel (e : α ≃ β) (P : β → Set β) (Q : Gaussian.Table β) :
    (Schur.per P Q).submatrix e e = Schur.per (fun i => e ⁻¹' P (e i)) (Q.submatrix e e) := by
  ext i j
  change Schur.per P Q (e i) (e j) = _
  by_cases hj : e j ∈ P (e j)
  swap
  · have h : j ∉ e ⁻¹' P (e j) := hj
    unfold Schur.per; rw [of_apply,of_apply,dif_neg hj,dif_neg h]
  by_cases hi : e i ∈ P (e j)
  swap
  · exact (Schur.per_zero P Q hi).trans (Schur.per_zero (fun i => e ⁻¹' P (e i)) _ (i:=j) (j:=i) hi).symm
  let T := P (e j)
  let t : ↥(e ⁻¹' T) ≃ T := Equiv.subtypeEquiv e (by intro; rfl)
  rw [Schur.per_read P Q hj hi, Schur.per_read (fun i => e ⁻¹' P (e i)) _ (i:=j) (j:=i) hj hi]
  let D := Schur.principal Q T
  change (D⁻¹.submatrix t t) ⟨i,hi⟩ ⟨j,hj⟩ = ((D.submatrix t t)⁻¹) ⟨i,hi⟩ ⟨j,hj⟩
  rw [Matrix.inv_submatrix_equiv]

def fill (e : α ↪ ι) (Q : Gaussian.Table α) : Gaussian.Table ι :=
    FreeResolvent.insertion e * Q * (FreeResolvent.insertion e).transpose + FreeResolvent.Shell.off e

omit [DecidableEq α] in
lemma fill_pad (e : α ↪ ι) (Q : Gaussian.Table ι) :
    fill e (Q.submatrix e e) = FreeResolvent.Shell.pad e Q := by
  rw [fill,FreeResolvent.Shell.pad, FreeResolvent.Shell.sliced]

omit [DecidableEq α] [Fintype β] in
lemma fill_read (e : α ↪ ι) (Q : Gaussian.Table α) (p : α ⊕ β ≃ ι) (hp : ∀ i, p (.inl i) = e i) :
    (fill e Q).submatrix p p = wide Q 1 := by
  let R := (wide Q (1 : Gaussian.Table β)).submatrix p.symm p.symm
  have hl (i : α) : p.symm (e i) = Sum.inl i := by rw [← hp,p.symm_apply_apply]
  rw [show Q = R.submatrix e e from ?_] -- R uses the original Q
  swap
  · symm; ext i j; change wide Q (1 : Gaussian.Table β) _ _ = _; rw [hl,hl]; rfl
  rw [fill_pad]
  ext (i|i) (j|j) <;> (
    rw [Matrix.submatrix_apply,FreeResolvent.Shell.pad, Matrix.add_apply,
      FreeResolvent.Shell.slice_test, FreeResolvent.Shell.off_test])
  all_goals have h (j : β) : p (.inr j) ∉ range e := fun ⟨k,hk⟩ => by have := p.injective ((hp k).trans hk); contradiction
  all_goals simp [hp,h,R,hl,wide,Matrix.one_apply]
  exact fun ht => h i ⟨j,ht.symm⟩

lemma per_fill (P : ι → Set ι) (hw : ∀ i, i∈P i) (e : α ↪ ι) (Q : Gaussian.Table α) {η : ℝ}
    (hQ : Q.IsSymm) (he : 0 < η) (hg : Schur.Gapped Q η) (p : α ⊕ β ≃ ι) (hp : ∀ i,p (.inl i)=e i) :
    Schur.per P (fill e Q) = fill e (Schur.per (fun i => e ⁻¹' P (e i)) Q) := by
  ext i j
  obtain ⟨i,rfl⟩ := p.surjective i; obtain ⟨j,rfl⟩ := p.surjective j
  change ((Schur.per P (fill e Q)).submatrix p p) _ _ = ((fill e _).submatrix p p) _ _
  rw [per_relabel, fill_read e _ p hp, fill_read e _ p hp, stamp Q _ hg hQ he (fun i => hw (p i))]
  congr 3 -- small private view
  ext i j; change (p (.inl j) ∈ P (p (.inl i))) ↔ _; simp [hp]

omit [DecidableEq α] [Fintype β] in
lemma sym_fill (e : α ↪ ι) (Q : Gaussian.Table α) (p : α ⊕ β ≃ ι) (hp : ∀ i,p (.inl i)=e i) :
    (1/2:ℝ) • (fill e Q + (fill e Q).transpose) = fill e ((1/2:ℝ) • (Q+Q.transpose)) := by
  ext i j
  obtain ⟨i,rfl⟩ := p.surjective i; obtain ⟨j,rfl⟩ := p.surjective j
  change (1/2:ℝ)*((fill e Q).submatrix p p i j+(fill e Q).submatrix p p j i)=(fill e _).submatrix p p i j
  rw [fill_read e _ p hp,fill_read e _ p hp]; cases i <;> cases j <;> first | rfl | simp [wide,Matrix.one_apply,eq_comm]
  split <;> norm_num

end generic

def middle (T : Tube G S) (V : Config G c) (k : S.Choices) : Gaussian.Table (In x A F (G:=G)) :=
    Schur.clouded (mids A F x) (Rows.gram T x V k (shots S x) A F)

def middleLog (T : Tube G S) (V : Config G c) (k : S.Choices) (q : Push.SectorMeasure.Chi) (d : ℝ)
    (Y : LinkArray G (Frozen A x F)) :=
    -(Schur.per (mids A F x) (Rows.gram T x V k (shots S x) A F)).transpose *ᵥ
      Rows.blame T x V k (shots S x) A F q d Y

lemma sym_gram (T : Tube G S) (V : Config G c) (k : S.Choices) :
    (Rows.gram T x V k (shots S x) A F).IsSymm := by unfold Rows.gram Matrix.IsSymm; rw [transpose_mul,transpose_transpose]

/-- cross-check using the doubled-torus construction from FREE_RESOLVENT on the *full* tree and hole padding.
Retains every boundary row. `fog` uses instead `endsAt`, on the exact same
selected Gram; neither window law used at nonpositive precisions here. -/
theorem prescription (T : Tube G S) (V : Config G c) (k : S.Choices) {η : ℝ}
    (hg : Schur.Gapped (Rows.gram T x V k (shots S x) A F) η) (he : 0 < η) (hb : 120 ≤ radiusB x) :
    let Q := Rows.gram T x V k (shots S x) A F
    let e := address A F x (G:=G); let U := fill e Q
    let L := (cutView G S (radiusB x)).inspect U 0
    let K := (view (endsAt S x (G:=G)) (ends_self x hb)).inspect U 0
    L = fill e (Schur.per (mids A F x) Q) ∧ (1/2:ℝ) • (L+L.transpose) = fill e (middle A F x T V k) ∧
      K = fill e (Schur.per (panels A F) Q) ∧ (1/2:ℝ) • (K+K.transpose) = fill e (fog A F T x V k) := by
  intro Q e U L K
  let p := sortSlots A F x (G:=G)
  have hQ := sym_gram A F x T V k
  have hl : L = (view (midsAt S x (G:=G)) (mids_self x)).inspect U 0 := by congr! 1
  rw [hl,per_view,per_fill _ (mids_self x) e Q hQ he hg p (sort_first A F x), sym_fill e _ p (sort_first A F x)]
  have hk : K = fill e (Schur.per (panels A F) Q) := by
    unfold K; rw [per_view,per_fill _ (ends_self x hb) e Q hQ he hg p (sort_first A F x), show panels (G:=G) (x:=x) A F = _ from funext (panels_eq A F x (G:=G))]
  rw [hk,sym_fill e _ p (sort_first A F x)]
  exact ⟨rfl,rfl,rfl,rfl⟩

end YM.AnalyticBridge.GaussianFieldAlignment
