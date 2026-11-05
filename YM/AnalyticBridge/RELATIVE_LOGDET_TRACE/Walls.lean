import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Resolvent
import YM.Push.FREE_RESOLVENT.Windows
import YM.Push.SECTOR_MEASURE.Presented
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Windows


/-!
# Uniform window-resolvent overheads

Uses the actual `SectorChange.Schur.clouded` convention. The inverse
is priced by FREE_RESOLVENT.Window, *u left in*. In particular errors
have no volume term. Principle: compare on the completed keys, but
principal here is a compression of that *same* built matrix. Don't rerun
sector decisions in a subwindow to fill its A entries.

Rates γ used below also bear the root and all other matrix addresses;
tilt is fixed for the whole period-independent estimate.
-/
set_option autoImplicit false

noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Filter Function Set Matrix Unitary MeasureTheory
open Next.SectorChange FreeResolvent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {ι : Type} {X : Type*} [Fintype ι] [DecidableEq ι]
variable (W : ι → Set ι)

/-- Π, the actual assembled column selection (including zeros). -/
def pie (A : Square ι) (u : ℝ) : Square ι := Schur.per W (A+u • 1)
/-- E obstruction to exact inversion. -/
def defect (A : Square ι) (u : ℝ) := (A+u • 1)*pie W A u - 1
/-- S, differs from `defect` due to symmetrization. -/
def excess (A : Square ι) : Square ι := A*Schur.clouded W A-1

lemma sym_cloud (A : Square ι) : Schur.clouded W A = (1/2:ℝ) • (pie W A 0 + (pie W A 0).transpose) := by
  simp only [pie,zero_smul,add_zero,Schur.clouded]
lemma self_cloud (A : Square ι) : (Schur.clouded W A).IsHermitian := by
  rw [sym_cloud]; apply Matrix.isHermitian_iff_isSymm.mpr; simp only [Matrix.IsSymm,transpose_smul,transpose_add,transpose_transpose,add_comm]

lemma pie_miss (A : Square ι) (u : ℝ) (i j) (hi : i ∉ W j) : pie W A u i j = 0 := Schur.per_zero W _ hi
/-- read on submatrix of A; true positive link index. -/
lemma pie_read (A : Square ι) (u : ℝ) (i j) (hi : i ∈ W j) (hj : j ∈ W j) :
    pie W A u i j = resolve (Schur.principal A (W j)) u ⟨i,hi⟩ ⟨j,hj⟩ := by
  rw [pie,Schur.per_read W _ hj hi]
  unfold Schur.principal resolve
  rw [shift_compress ((↑) : W j→ι) _ u Subtype.val_injective]

def study (hW : ∀ i, i∈W i) : Window.Survey (fun i => W i) where
  loc _ := Embedding.subtype _
  root i := ⟨i,hW i⟩
  atRoot _ := rfl

lemma pie_inspects (A : Square ι) (u : ℝ) (hW : ∀ i, i∈W i) : pie W A u = (study W hW).inspect A u := by
  ext i j
  let z : W j := ⟨j,hW j⟩
  change _ = Pane.column A ((↑): W j→ι) u z i
  by_cases hi : i ∈ W j
  · rw [pie_read W _ u i j hi (hW j)]; exact (Pane.local_entry A u _ Subtype.val_injective z (⟨i,hi⟩ : W j)).symm
  rw [pie_miss W _ _ _ _ hi, Pane.unused _ _ _ _ _ ?_]
  rintro ⟨x,rfl⟩; exact hi x.property
lemma defect_survey (A : Square ι) (u : ℝ) (hW : ∀ i, i∈W i) : defect W A u=(study W hW).error A u := by rw [defect,pie_inspects _ _ _ hW]; rfl

lemma defect_zero {A : Square ι} (u : ℝ) (hw : ∀ i, i∈W i)
    (hg : ∀ i, IsUnit ((Schur.principal A (W i)+u • 1).det)) {i j} (h : i ∈ W j) :
    defect W A u i j = 0 := by
  let T := study W hw
  rw [defect_survey W _ _ hw]; change T.error A u i j=0
  rw [T.residual _ _ hg,Window.Survey.outside_apply,if_pos ⟨⟨i,h⟩,rfl⟩]

section envelopes
variable {W} {D : Cost X} {p : ι → X} {A : Square ι}

/-- Bundle at *one* width and cost. `q` may then be made arbitrarily
small at exponential rate by window size. Here no smallness or gap
hypothesis in the definition except A itself positive; ask q<1 and PosDef
of covariance separately when using. -/
structure Priced (D : Cost X) (p : ι → X) (W : ι → Set ι) (A : Square ι) (v C q : ℝ) : Prop where
  root : ∀ i, i ∈ W i
  gram : A.PosDef
  paid : 1 ≤ C
  rate : 0 ≤ v
  coupon : 0 ≤ q
  kernel : D.Schur p p v C A
  inverse : ∀ u : ℝ, 0 ≤ u → D.Schur p p v (C*attenuation u) (resolve A u)
  columns : ∀ u : ℝ, 0 ≤ u → D.Schur p p v (C*attenuation u) (pie W A u)
  shift : ∀ u : ℝ, 0 ≤ u → D.Schur p p v (q*attenuation u) (defect W A u)
  mix : D.Schur p p v q (excess W A)

omit [Fintype ι] [DecidableEq ι] in
lemma sym_change (C L : Square ι) (hL : L.IsSymm) : (1/2:ℝ) • (C + C.transpose) - L =
    (1/2:ℝ) • ((C-L)+(C-L).transpose) := by
  rw [transpose_sub,hL.eq]; ext i j; change (1/2:ℝ)*(C i j+C j i)-L i j= (1/2:ℝ)*((C i j-L i j)+(C j i-L i j)); ring

omit [DecidableEq ι] in
lemma sym_cost {C L : Square ι} (hL : L.IsSymm) {v q : ℝ}
    (he : D.Schur p p v q (C-L)) : D.Schur p p v q ((1/2:ℝ) • (C + C.transpose)-L) := by
  rw [sym_change _ _ hL]
  exact (((he.add he.transpose).smul (1/2:ℝ))).mono le_rfl (by rw [abs_of_nonneg (by norm_num)]; linarith)

lemma tilted_price {D : Cost X} {σ M r m γ V R C : ℝ} (hm : 0 ≤ M) (hσ : 0 < σ) (hr : 0<r)
    (hγ : 0 ≤ γ) (he : γ ≤ m) (hl : m ≤ σ) (hV : 0 ≤ V)
    (hC : 1≤C) (hx : M ≤ C) (hc : V*(min (r/2) 1)⁻¹ ≤ C)
    (h : D.Schur p p σ M A) (hA : Gap A r) (hp : A.PosDef)
    (hv : D.Volume p (safeRate σ M r-m) V)
    (hw : ∀ i, i∈W i) (hw' : ∀ i j, j ∉ W i → R ≤ D.d (p i) (p j)) :
    Priced D p W A γ C (C^4 * Real.exp (-(m-γ)*R)) := by
  let e := Real.exp (-(m-γ)*R)
  let T := study W hw
  have hh (u : ℝ) (hu : 0 ≤ u) : V*(r/2+u)⁻¹ ≤ C * attenuation u := calc
    _ ≤ V*((min (r/2) 1)⁻¹ * attenuation u) := mul_le_mul_of_nonneg_left (uniform_shift r u hr hu) hV
    _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hc (attenuation_pos hu).le
  have ht : T.Near D p R := fun i j hi => hw' i j (fun hx => hi ⟨⟨j,hx⟩,rfl⟩)
  have hg u (hu : 0 ≤ u) : D.Schur p p γ (C * attenuation u) (resolve A u) :=
    (resolve_schur hm hσ h hA hr hu hv).mono he (hh u hu)
  have hy u (hu : 0 ≤ u) : D.Schur p p γ (C * attenuation u) (pie W A u) := by
    rw [pie_inspects _ _ _ hw]
    exact (T.prices hu hr hσ hm h hA hv).mono he (hh u hu)
  have he' : 0 < e := Real.exp_pos _
  have h₀ : 0 < C := zero_lt_one.trans_le hC
  have hz u (hu : 0 ≤ u) : D.Schur p p γ (C^2 * e * attenuation u) (defect W A u) := by
    rw [defect_survey _ _ _ hw]
    apply (T.error_price ht hu hr hσ hm (hγ.trans he) he hl hV h hA hv).mono le_rfl
    have hi : 0 ≤ V*(r/2+u)⁻¹ := by positivity
    exact (mul_le_mul_of_nonneg_left (mul_le_mul hx (hh u hu) hi h₀.le) he'.le).trans_eq (by ring)
  have ha : D.Schur p p γ C A := h.mono (he.trans hl) hx
  refine ⟨hw,hp,hC,hγ,(mul_pos (by positivity) he').le,ha,hg,hy,fun u hu => (hz u hu).mono le_rfl ?_,?_⟩
  · change _ ≤ C^4*e*_
    have := attenuation_pos hu; gcongr; norm_num
  unfold excess
  rw [show A*Schur.clouded W A-1=A*(Schur.clouded W A-A⁻¹) by
    rw [Matrix.mul_sub,Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hp.det_pos.ne')], sym_cloud]
  have hi : resolve A 0=A⁻¹ := by simp [resolve]
  have hsum : pie W A 0-A⁻¹=resolve A 0*defect W A 0 := by
    rw [defect_survey _ _ _ hw,pie_inspects _ _ _ hw,← hi]; exact T.replacement A 0 ((hA.shift 0).unit_det (by linarith))
  have hj : D.Schur p p γ (C*(C^2*e)) (pie W A 0-A⁻¹) := by
    rw [hsum]; apply Cost.Schur.mul (b:=p) _ _ hγ h₀.le (by positivity)
    · simpa only [attenuation,add_zero, inv_one,mul_one] using hg 0 le_rfl
    simpa only [attenuation,add_zero, inv_one,mul_one] using hz 0 le_rfl
  exact (ha.mul (sym_cost (Matrix.isHermitian_iff_isSymm.mp hp.inv.isHermitian) hj) hγ h₀.le (by positivity)).mono le_rfl (Eq.le (by ring))
end envelopes
end YM.AnalyticBridge.RelativeLogdet
