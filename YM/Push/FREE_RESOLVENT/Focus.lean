import YM.Push.FREE_RESOLVENT.Windows

/-!
# Single window with arbitrary numbering
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Matrix
open scoped BigOperators
variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma resolve_equiv (e : κ ≃ ι) (A : Matrix ι ι ℝ) (u : ℝ) :
    resolve (A.submatrix e e) u = (resolve A u).submatrix e e := by
  unfold resolve
  rw [← shift_compress _ A u e.injective]
  generalize A + u • 1 = B
  by_cases h : IsUnit B.det
  · let F := (B.submatrix e e)⁻¹
    have ha : IsUnit (B.submatrix e e).det := by rw [Matrix.det_submatrix_equiv_self]; exact h
    calc
      F = F * ((B.submatrix e e)*(B⁻¹.submatrix e e)) := by
        rw [Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv B h, submatrix_one_equiv, Matrix.mul_one]
      _ = _ := by unfold F; rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]
  have ha : ¬ IsUnit (B.submatrix e e).det := by rw [Matrix.det_submatrix_equiv_self]; exact h
  rw [Matrix.nonsing_inv_apply_not_isUnit B h, Matrix.nonsing_inv_apply_not_isUnit _ ha]; rfl

variable {X : Type*}
namespace Pane
variable (e : κ ↪ ι) (i : κ)

def spots (k : ι) : Finset ι := if k=e i then Finset.univ.map e else Finset.univ
omit [DecidableEq κ] in
lemma covers (k : ι) : k ∈ spots e i k := by unfold spots; split <;> simp_all

def focus : Window.Survey (fun k => ↥(spots e i k)) where
  loc _ := Function.Embedding.subtype _
  root k := ⟨k,covers e i k⟩
  atRoot _ := rfl

omit [DecidableEq κ] in
lemma focus_near (D : Cost X) (a : ι → X) (R : ℝ)
    (H : ∀ j : ι, j ∉ Set.range e → R ≤ D.d (a (e i)) (a j)) :
    (focus e i).Near D a R := by
  intro k j hj
  have ht : j ∉ spots e i k := fun h => hj ⟨⟨j,h⟩,rfl⟩
  unfold spots at ht; split at ht <;> rename_i h
  · rw [h]
    apply H j; rintro ⟨l,rfl⟩; simp at ht
  exact False.elim (by simp at ht)

def mapHere (x : κ) : spots e i (e i) := ⟨e x,by simp [spots]⟩
omit [DecidableEq κ] in
lemma here_bijective : Function.Bijective (mapHere e i) := by
  constructor
  · intro j k he; exact e.injective (congrArg Subtype.val he)
  intro j
  have hx := j.property
  simp only [spots,if_true, Finset.mem_map, Finset.mem_univ, true_and] at hx
  obtain ⟨b,hb⟩ := hx
  exact ⟨b,Subtype.ext hb⟩

lemma sees (A : Matrix ι ι ℝ) (u : ℝ) (j : κ) :
    (focus e i).inspect A u (e j) (e i) = Pane.thin A e u j i := by
  let T := focus e i
  let E := Equiv.ofBijective (mapHere e i) (here_bijective e i)
  have hi : T.root (e i) = E i := Subtype.ext rfl
  change Pane.column _ _ _ (T.root (e i)) (T.loc (e i) (E j)) = _
  rw [hi,Pane.local_entry _ _ _ (T.loc (e i)).injective]
  have hh := resolve_equiv E (A.submatrix (T.loc (e i)) (T.loc (e i))) u
  exact congr_fun (congr_fun hh j) i |>.symm
end Pane

def windowPrice (M V r u μ γ R : ℝ) := (V*(r/2+u)⁻¹)*(Real.exp (-(μ-γ)*R)*(M*(V*(r/2+u)⁻¹)))

/-- Bound against any given principal window at one column. Price decays
exponentially in R at any fixed μ>γ, and integrably in u. Exposed up to
each entry inside that window with its smaller exponent payment still included. -/
theorem focus_price (e : κ ↪ ι) (i : κ) {D : Cost X} {a : ι → X} {R u r σ μ γ V M : ℝ}
    {A : Matrix ι ι ℝ} (H : ∀ j : ι, j ∉ Set.range e → R ≤ D.d (a (e i)) (a j))
    (hu : 0 ≤ u) (hr : 0 < r) (hs : 0 < σ) (hm : 0 ≤ M) (hγ : 0 ≤ γ) (hg : γ ≤ μ)
    (hx : μ ≤ σ) (hV : 0 ≤ V) (h : D.Schur a a σ M A) (hA : Gap A r)
    (hv : D.Volume a (safeRate σ M r-μ) V) (j : κ) :
    D.weight γ (a (e i)) (a (e j)) * |Pane.thin A e u j i-resolve A u (e j) (e i)| ≤
      windowPrice M V r u μ γ R := by
  have ht := (Window.Survey.difference (Pane.focus_near e i D a R H)
    hu hr hs hm hγ hg hx hV h hA hv).cols.weighted (e i) (e j)
  rw [Matrix.transpose_apply, Matrix.sub_apply, Pane.sees] at ht
  exact ht
end YM.FreeResolvent
