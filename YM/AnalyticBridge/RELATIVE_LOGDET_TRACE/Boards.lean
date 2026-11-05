import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Walls
import YM.Next.FREE_KERNELS.Lifts
import YM.Push.FREE_RESOLVENT.Focus
import YM.Push.FREE_RESOLVENT.Torus
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Completion


/-!
# Parse on the full physical fine columns

Use `sorted` only to transport receipts. Everything subtracted/marked/addressed
is in the SAME basis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Function Filter Set Matrix Lattice RG Wilson Precision Pressure Tree
open Next.SectorChange Next.SectorChange.Completion FreeResolvent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

section matrices
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma equiv_pie (P : Square ι) (W : ι → Set ι) (W' : κ→Set κ) (e : κ ≃ ι) (h : ∀ i j, i ∈ W' j ↔ e i ∈ W (e j))
    (hx : ∀ i, i∈W' i) (u : ℝ) : pie W' (P.submatrix e e) u=(pie W P u).submatrix e e := by
  ext i j
  let Q := P.submatrix e e
  change pie W' Q u i j=pie W P u (e i) (e j)
  by_cases hi : i∈W' j
  · rw [pie_read W' _ u i j hi (hx j),pie_read W P u _ _ ((h i j).1 hi) ((h _ _).1 (hx j))]
    let g := Equiv.subtypeEquiv e (p:=fun i => i∈W' j) (q:=fun i => i∈W (e j)) (fun i => h i j)
    have he := resolve_equiv (show W' j≃ W (e j) from g) (Schur.principal P (W (e j))) u
    exact congr_fun (congr_fun he (⟨i,hi⟩:W' j)) (⟨j,hx j⟩:W' j)
  rw [pie_miss W' Q u i j hi,pie_miss W P u (e i) (e j) (mt ((h i j).2) hi)]

lemma equiv_cloud (P : Square ι) (W : ι → Set ι) (W' : κ→Set κ) (e : κ ≃ ι) (h : ∀ i j, i ∈ W' j ↔ e i ∈ W (e j))
    (hx : ∀ i, i∈W' i) : Schur.clouded W' (P.submatrix e e)=(Schur.clouded W P).submatrix e e := by
  rw [sym_cloud, sym_cloud,equiv_pie P W W' e h hx]
  rfl

lemma wide_positive (P : Square ι) (Q : Square κ) (hP : P.PosDef) (hQ : Q.PosDef) : (wide P Q).PosDef := by
  have he : (wide P Q).IsSymm := by
    unfold Matrix.IsSymm wide; rw [Matrix.fromBlocks_transpose,Matrix.transpose_zero,(Matrix.isHermitian_iff_isSymm.mp hP.1).eq,
      (Matrix.isHermitian_iff_isSymm.mp hQ.1).eq]; rfl
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.isHermitian_iff_isSymm.mpr he, fun x hx => ?_⟩
  simp only [star_trivial]
  rw [wide_cost]
  let a := x ∘ Sum.inl; let b := x ∘ Sum.inr
  by_cases ha : a=0
  · have hb : b ≠ 0 := fun hb => hx (funext fun i => i.casesOn (fun j => congr_fun ha j) fun j => congr_fun hb j)
    change 0<a ⬝ᵥ (P *ᵥ a)+ b ⬝ᵥ (Q*ᵥ b); rw [ha,zero_dotProduct,zero_add]; simpa using
      ((Matrix.posDef_iff_dotProduct_mulVec.mp hQ).2 hb)
  have ht : 0 < a ⬝ᵥ (P*ᵥ a) := by simpa using ((Matrix.posDef_iff_dotProduct_mulVec.mp hP).2 ha)
  exact add_pos_of_pos_of_nonneg ht (by simpa using ((Matrix.posSemidef_iff_dotProduct_mulVec.mp hQ.posSemidef).2 b))

omit [DecidableEq ι] [DecidableEq κ] in
lemma wide_pours {P : Square ι} {Q : Square κ} {X : Type*} (p : ι⊕κ → X) {D : Cost X} {μ C : ℝ}
    (hP : D.Schur (p ∘ Sum.inl) (p ∘ Sum.inl) μ C P) (hQ : D.Schur (p ∘ Sum.inr) (p ∘ Sum.inr) μ C Q) :
    D.Schur p p μ C (wide P Q) := by
  have H (P : Square ι) (Q : Square κ)
      (hp : D.Rows (p ∘ Sum.inl) (p ∘ Sum.inl) μ C P) (hq : D.Rows (p ∘ Sum.inr) (p ∘ Sum.inr) μ C Q) :
      D.Rows p p μ C (wide P Q) := by
    constructor
    rintro (i|i) <;> rw [Fintype.sum_sum_type]
    · simpa [wide] using hp.bound i
    · simpa [wide] using hq.bound i
  refine ⟨H _ _ hP.rows hQ.rows,?_⟩
  rw [show (wide P Q).transpose=wide P.transpose Q.transpose by unfold wide; rw [Matrix.fromBlocks_transpose]; rfl]
  exact H _ _ hP.cols hQ.cols

omit [DecidableEq ι] in
lemma gapped' (A : Square ι) {η : ℝ} (h : Schur.Gapped A η) : FreeResolvent.Gap A η := by
  constructor; intro v; rw [← Schur.sumSq_dot]; exact h v
omit [DecidableEq ι] in
lemma pours' {c : Side} (A : Square ι) (p : ι → Site c) {μ C : ℝ} (h : Schur.Pours A p p μ C) :
    (native c).Schur p p μ C A := by
  refine ⟨⟨h.row⟩,⟨fun j => ?_⟩⟩
  simp_rw [Cost.weight_symm _ μ (p j)]; exact h.col _
end matrices

namespace Physical

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ} (T : Tube G S) (A : Stores S)
  (F : Forest S.ratio)

/-- Components include all positive links and whole real orthonormal color components. -/
abbrev Key (G : Gauge) (f : Side) := Bond f × G.ColorIndex
abbrev place (S : StepData c f) (i : Key G f) := S.ratio.parent i.1.1

def windows (S : StepData c f) (x : ℝ) (i : Key G f) : Set (Key G f) := {j | meeting S x i.1 j.1}

def AFull (x : ℝ) (V : Config G c) (k : S.Choices) : Square (Key G f) :=
    let P := Rows.gram T x V k (shots S x) A F
    let e := sorted A F (x:=x) (G:=G)
    (wide P (1:Square (vacant A F x G))).submatrix e.symm e.symm

def CFull (x : ℝ) (V : Config G c) (k : S.Choices) : Square (Key G f) :=
    let Q := fog A F T x V k
    let e := sorted A F (x:=x) (G:=G)
    (wide Q (1:Square (vacant A F x G))).submatrix e.symm e.symm

lemma a_det (x) (V) (k) : det (AFull T A F x V k) = det (Rows.gram T x V k (shots S x) A F) := by
  unfold AFull; dsimp only; rw [Matrix.det_submatrix_equiv_self]
  have hv := (wide_det (Rows.gram T x V k (shots S x) A F) (1:Square (vacant A F x G)))
  rw [Matrix.det_one,mul_one] at hv
  convert hv using 2
lemma a_pos {V : Config G c} (k) (he : (Rows.gram T x V k (shots S x) A F).PosDef) : (AFull T A F x V k).PosDef :=
  (wide_positive _ (1:Square (vacant A F x G)) he Matrix.PosDef.one).submatrix (sorted (G:=G) A F).symm.injective
lemma c_det (x) (V) (k) : det (CFull T A F x V k)=det (fog A F T x V k) := by
  unfold CFull; dsimp only; rw [Matrix.det_submatrix_equiv_self]
  have hv := (wide_det (fog A F T x V k) (1:Square (vacant A F x G)))
  rw [Matrix.det_one,mul_one] at hv
  convert hv using 2
lemma c_pos {V : Config G c} (k) (he : (fog A F T x V k).PosDef) : (CFull T A F x V k).PosDef :=
  (wide_positive _ (1:Square (vacant A F x G)) he Matrix.PosDef.one).submatrix (sorted (G:=G) A F).symm.injective

lemma contained (i j : Key G f) (h : j ∈ windows S x i) : separation (place S i) (place S j) ≤ radiusB x/20 :=
  h _ (Set.mem_insert ..) _ (Set.mem_insert ..)
lemma near_contains {i j : Key G f} (hb : 120 ≤ radiusB x) (h : separation (place S i) (place S j) ≤ radiusB x / 60) :
    j ∈ windows S x i := by
  intro y hy z hz
  have ha : separation y (place S i) ≤ 1 := (separation_comm ..).trans_le (meetings _ hy)
  have he : separation (place S j) z ≤ 1 := meetings _ hz
  apply (separation_triangle y (place S i) z).trans
  have := separation_triangle (place S i) (place S j) z; omega
lemma centered (hb : 120 ≤ radiusB x) (i : Key G f) : i ∈ windows S x i := near_contains hb (by simp)

/-- The covariance here is still the literal assembled (endpoint-pair)
window prescription, after padding and reindexing. -/
lemma produced (hb : 120 ≤ radiusB x) (V : Config G c) (k) {η : ℝ} (hη : 0 < η)
    (hg : Schur.Gapped (Rows.gram T x V k (shots S x) A F) η) :
    Schur.clouded (windows S x) (AFull T A F x V k)=CFull T A F x V k := by
  let E := (sorted A F (x:=x) (G:=G))
  let U := allPanels A F (x:=x) (G:=G)
  let P := Rows.gram T x V k (shots S x) A F
  change Schur.clouded _ ((wide P (1:Square (vacant A F x G))).submatrix E.symm E.symm) = _
  have hW (i j : Key G f) : i∈windows S x j ↔ E.symm i∈U (E.symm j) := by
    change _ ↔ meeting S x (E (E.symm j)).1 (E (E.symm i)).1; simp only [Equiv.apply_symm_apply]; rfl
  rw [equiv_cloud _ U _ E.symm hW (centered hb),show Schur.clouded U _=_ from (stocked A F x T k V hη hg hb).2.1]
  rfl

lemma blueprint (x : ℝ) (V : Config G c) (k) {v C η : ℝ}
    (h : Schur.Pours (Rows.gram T x V k (shots S x) A F) (Wisps.front A F) (Wisps.front A F) v C)
    (hg : Schur.Gapped (Rows.gram T x V k (shots S x) A F) η) :
    (native c).Schur (place S) (place S) v (max C 1) (AFull T A F x V k) ∧
      FreeResolvent.Gap (AFull T A F x V k) (min η 1) := by
  let E:=sorted A F (x:=x) (G:=G)
  let Q:=Rows.gram T x V k (shots S x) A F
  have he : Wisps.front A F (x:=x) (G:=G) = (place S ∘ E) ∘ Sum.inl := rfl
  have h1 := ((pours' _ _ h).mono le_rfl (le_max_left _ 1))
  rw [he] at h1
  have ht := wide_pours (P:=Q) (p:=place S ∘ E) h1 (Cost.Schur.one.mono le_rfl (le_max_right C 1))
  have hy := ht.submatrix E.symm.injective E.symm.injective
  have hi : (place S ∘ E) ∘ E.symm = place S := by ext i; simp only [Function.comp_apply,Equiv.apply_symm_apply]
  rw [hi] at hy
  have hh : Q.IsSymm := by unfold Q Rows.gram Matrix.IsSymm; rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  exact ⟨hy,(gapped' _ (wide_gap hh hg).2).submatrix E.symm E.symm.injective⟩

/-- Full cost-volume, paid after L, includes all keys, independent of f,c. -/
def ceiling (G : Gauge) (P : Patch) (θ : ℝ) :=
    ((Fintype.card G.ColorIndex:ℝ)*((Fintype.card Axis:ℝ)*Fintype.card (Site P.L))) * Tier.wealth θ

lemma ceiling_nn (P : Patch) (G : Gauge) (θ : ℝ) : 0 ≤ ceiling G P θ :=
  mul_nonneg (by positivity) (Tier.wealth_nn θ)
lemma audience (S : StepData c f) (G : Gauge) {θ : ℝ} (he : 0<θ) : (native c).Volume (place S (G:=G)) θ (ceiling G S.patch θ) := by
  constructor; intro y
  let L := fun i => (native c).weight (-θ) y i
  have ht : ∑ i : Site c,L i ≤ Tier.wealth θ := by
    change (∑ i : Site c,Wisps.rate (-θ) (separation y i)) ≤ _
    simp_rw [separation_comm y]; exact Tier.land he y
  have hp {α β : Type} [Fintype α] [Fintype β] (x : α → ℝ) : (∑ i : α × β,x i.1) = Fintype.card β * ∑ i,x i := by
    rw [Fintype.sum_prod_type]; simp [Finset.mul_sum]
  change (∑ i : Bond f × G.ColorIndex, L (S.ratio.parent i.1.1)) ≤ _
  rw [hp (fun i : Bond f => L (S.ratio.parent i.1)),hp (fun i : Site f => L (S.ratio.parent i)),Work.F01.sum_parent]
  unfold ceiling
  rw [mul_assoc, mul_assoc (Fintype.card Axis : ℝ)]
  change (Fintype.card G.ColorIndex:ℝ)*((Fintype.card Axis:ℝ)*((Fintype.card (Site S.patch.L):ℝ)*_)) ≤ _
  gcongr
end Physical
end YM.AnalyticBridge.RelativeLogdet
