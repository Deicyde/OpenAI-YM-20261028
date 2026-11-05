import YM.Push.FREE_RESOLVENT.Inverse

/-!
# Principal cuts of the same periodic resolvent

Real energy shift `u ≥ 0`. Principal subset = *after* the precision is built.
Allow indexing arbitrary and different for every column (so this estimate
also works at seam, rotated channels, doubled coordinates with misses,
and for comparing different periods on a common nonwrapping patch).

`inspect` is Pi_u, using zero extension off each window and without requiring
distance geometry. Window identities use just the local compressions;
compare to the full inverse paying the minimum distance to an excluded slot.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Matrix
open scoped BigOperators
variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype ι] in
lemma insertion_at (e : κ → ι) (B : κ → ℝ) (he : Function.Injective e) (i : κ) :
    (insertion e *ᵥ B) (e i) = B i := by classical simp [mulVec,dotProduct,insertion,he.eq_iff]
omit [Fintype ι] in
lemma insertion_misses (e : κ → ι) (B : κ → ℝ) (j : ι) (h : j ∉ Set.range e) :
    (insertion e *ᵥ B) j = 0 := by
  unfold mulVec dotProduct
  exact Finset.sum_eq_zero fun i _ => by simp [insertion,show e i ≠ j from fun he => h ⟨i,he⟩]
omit [Fintype κ] in
lemma probe_insert (e : κ → ι) (B : ι → ℝ) (i : κ) :
    ((insertion e).transpose *ᵥ B) i = B (e i) := by simp [mulVec,dotProduct,insertion]
lemma at_compression (e : κ → ι) (A : Matrix ι ι ℝ) (B : κ → ℝ) (i : κ) :
    (A *ᵥ (insertion e *ᵥ B)) (e i) = ((A.submatrix e e) *ᵥ B) i := by
  rw [← probe_insert e (A *ᵥ (insertion e *ᵥ B)) i, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,insertion.compress]

omit [Fintype ι] [Fintype κ] in
lemma shift_compress [DecidableEq κ] (e : κ → ι) (A : Matrix ι ι ℝ) (u : ℝ) (he : Function.Injective e) :
    (A+u • 1).submatrix e e = A.submatrix e e + u • 1 := by
  ext; simp [Matrix.one_apply,he.eq_iff]

variable {X : Type*}
namespace Pane
variable [DecidableEq κ]

/-- A single window resolvent on a principal list. -/
abbrev thin (A : Matrix ι ι ℝ) (e : κ → ι) (u : ℝ) := resolve (A.submatrix e e) u

def column (A : Matrix ι ι ℝ) (e : κ → ι) (u : ℝ) (i : κ) : ι → ℝ :=
  insertion e *ᵥ (fun j => thin A e u j i)

omit [Fintype ι] in
lemma local_entry (A : Matrix ι ι ℝ) (u : ℝ) (e : κ → ι) (he : Function.Injective e) (i j : κ) :
    column A e u i (e j) = thin A e u j i := insertion_at e _ he j

omit [Fintype ι] in
lemma unused (A : Matrix ι ι ℝ) (u : ℝ) (e : κ → ι) (i : κ) (j : ι) (h : j ∉ Set.range e) :
    column A e u i j = 0 := insertion_misses e _ j h

lemma center_solve {A : Matrix ι ι ℝ} (u : ℝ) (e : κ → ι) (he : Function.Injective e)
    (hw : IsUnit ((A.submatrix e e + u • 1).det)) (i j : κ) :
    ((A+u • 1) *ᵥ column A e u i) (e j) = (1 : Matrix ι ι ℝ) (e j) (e i) := by
  rw [column, at_compression, shift_compress _ _ _ he]
  have hh : (A.submatrix e e + u • 1)*thin A e u = 1 := Matrix.mul_nonsing_inv _ hw
  change ((A.submatrix e e + u • 1) * thin A e u) j i = _
  simp [hh,Matrix.one_apply,he.eq_iff]

lemma center_bound {A : Matrix ι ι ℝ} {u : ℝ} (e : κ → ι) (he : Function.Injective e)
    {σ M r : ℝ} {D : Cost X} {a : ι → X} (hσ : 0 < σ) (hM : 0 ≤ M) (hr : 0 < r) (hu : 0 ≤ u)
    (h : D.Schur a a σ M A) (hg : Gap A r) (i : κ) (j : ι) :
    |column A e u i j| ≤ D.weight (-safeRate σ M r) (a j) (a (e i)) * (r/2+u)⁻¹ := by
  by_cases hj : j ∈ Set.range e
  · obtain ⟨k,rfl⟩ := hj; rw [local_entry _ _ _ he]; exact resolve_point hM hσ
      (h.submatrix he he) (hg.submatrix e he) hr hu (rate_pos hσ hM hr).le le_rfl k i
  rw [unused A u e i j hj,abs_zero]; exact mul_nonneg (D.weight_nn ..) (by positivity)
end Pane

-- Bound any selection of one pane per column.
namespace Window
variable (I : ι → Type*) [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

structure Survey where
  loc (i : ι) : I i ↪ ι
  root (i : ι) : I i
  atRoot (i : ι) : loc i (root i) = i

namespace Survey
variable {I} (T : Survey I)

/-- Width of ball contained about EACH column's center. -/
def Near (D : Cost X) (a : ι → X) (R : ℝ) :=
  ∀ i j : ι, j ∉ Set.range (T.loc i) → R ≤ D.d (a i) (a j)

def inspect (A : Matrix ι ι ℝ) (u : ℝ) : Matrix ι ι ℝ :=
  of fun i j => Pane.column A (T.loc j) u (T.root j) i

/-- Outside product removes the u dependence from estimating *residual*. -/
def outside (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := by
  classical
  exact of fun i j => if i ∈ Set.range (T.loc j) then 0 else A i j
open scoped Classical in
omit [Fintype ι] [∀ i, DecidableEq (I i)] in
lemma outside_apply (A : Matrix ι ι ℝ) (i j : ι) :
    T.outside A i j = if i ∈ Set.range (T.loc j) then 0 else A i j := by
  unfold outside; simp only [of_apply]

def error (A : Matrix ι ι ℝ) (u : ℝ) := (A+u • 1)*T.inspect A u-1

/-- Exact outside-window identity, even in a parameter germ (need only
invertible compressed matrices, not global gap). -/
lemma residual (A : Matrix ι ι ℝ) (u : ℝ) (H : ∀ i, IsUnit (A.submatrix (T.loc i) (T.loc i) + u • 1).det) :
    T.error A u = T.outside (A * T.inspect A u) := by
  classical
  ext i j
  rw [outside_apply]
  split <;> rename_i h
  · obtain ⟨k,rfl⟩ := h
    rw [error, Matrix.sub_apply]; apply sub_eq_zero.mpr
    change ((A+u • 1) *ᵥ Pane.column _ _ _ _) _ = _
    exact (Pane.center_solve u (T.loc j) (T.loc j).injective (H j) (T.root j) k).trans (by rw [T.atRoot])
  have h' : i ≠ j := fun he => h ⟨_,(T.atRoot j).trans he.symm⟩
  have ht : T.inspect A u i j = 0 := Pane.unused _ _ _ _ _ h
  rw [error, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]; simp [ht,h']

lemma replacement (A : Matrix ι ι ℝ) (u : ℝ) (H : IsUnit (A+u • 1).det) :
    T.inspect A u - resolve A u = resolve A u * T.error A u := by
  rw [error, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      show resolve A u*(A+u • 1)=1 from Matrix.nonsing_inv_mul _ H, Matrix.one_mul]

variable {T} {X : Type*} {D : Cost X} {a : ι → X}
variable {γ σ M r u R μ V : ℝ} {A : Matrix ι ι ℝ}

theorem prices (T : Survey I) (hu : 0 ≤ u) (hr : 0 < r) (hs : 0 < σ) (hm : 0 ≤ M) (h : D.Schur a a σ M A)
    (hg : Gap A r) (hv : D.Volume a (safeRate σ M r-γ) V) :
    D.Schur a a γ (V*(r/2+u)⁻¹) (T.inspect A u) := by
  have he (i j) : |T.inspect A u i j| ≤ D.weight (-safeRate σ M r) (a i) (a j) * (r/2+u)⁻¹ := by
    have hh := Pane.center_bound (T.loc j) (T.loc j).injective hs hm hr hu h hg (T.root j) i
    rw [T.atRoot] at hh; exact hh
  exact Cost.Schur.of_point (by positivity) he hv hv

theorem error_price (hp : T.Near D a R) (hu : 0 ≤ u) (hr : 0 < r) (hs : 0 < σ) (hm : 0 ≤ M)
    (hμ : 0 ≤ μ) (hg : γ ≤ μ) (hx : μ ≤ σ) (hV : 0 ≤ V)
    (h : D.Schur a a σ M A) (hA : Gap A r) (hv : D.Volume a (safeRate σ M r-μ) V) :
    D.Schur a a γ (Real.exp (-(μ-γ)*R) * (M*(V*(r/2+u)⁻¹))) (T.error A u) := by
  classical
  rw [T.residual _ u fun i => (((hA.submatrix _ (T.loc i).injective).shift u).unit_det (by positivity))]
  have he := (h.mono hx le_rfl).mul (T.prices hu hr hs hm h hA hv) hμ hm (by positivity)
  apply he.far R hg
  · intro i j h
    rw [D.comm]
    by_contra! H
    rw [outside_apply,if_pos (show i ∈ Set.range (T.loc j) from Classical.byContradiction fun hi => H.not_ge (hp j i hi))] at h
    exact h rfl
  intro i j; rw [outside_apply]; split <;> simp

theorem difference (hp : T.Near D a R) (hu : 0 ≤ u) (hr : 0 < r) (hs : 0 < σ) (hm : 0 ≤ M)
    (hγ : 0 ≤ γ) (hg : γ ≤ μ) (hx : μ ≤ σ) (hV : 0 ≤ V)
    (h : D.Schur a a σ M A) (hA : Gap A r) (hv : D.Volume a (safeRate σ M r-μ) V) :
    D.Schur a a γ ((V*(r/2+u)⁻¹)*(Real.exp (-(μ-γ)*R)*(M*(V*(r/2+u)⁻¹)))) (T.inspect A u - resolve A u) := by
  rw [replacement T A u ((hA.shift u).unit_det (by positivity))]
  exact ((resolve_schur hm hs h hA hr hu hv).mono hg le_rfl).mul
    (T.error_price hp hu hr hs hm (hγ.trans hg) hg hx hV h hA hv) hγ (by positivity) (by positivity)
end Survey
end Window

end YM.FreeResolvent
