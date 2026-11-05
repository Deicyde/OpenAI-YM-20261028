import YM.Work.B09.Core

/-! Inclusions and derivatives through the same evaluation. For the latter
 we can differentiate a genuinely norm-regular slab insertion (Laws hypothesis),
 keeping the same width and shift in a neighborhood. -/

set_option autoImplicit false
noncomputable section
namespace YM.Work.B09
open Set Filter Function Analysis OS Word
open scoped Topology ContDiff NNReal InnerProductSpace BigOperators

variable {G : Gauge} {L : Register G} {S T : Table L} {V : Chamber S timeAxis} {A : Spread V}
variable {P : DiffPlan S} {φ : V.H.Op →L[ℂ] ℂ}
variable {d n : ℕ} {s : E4} {D : ℝ≥0} {x : Points (n+1)}

lemma Evaluates.inclusions (he : Evaluates T A φ) (H : S.Hierarchy) (h : P.Inclusions S) :
    P.Inclusions T := by
  constructor
  intro d e hde B n x hx q
  obtain ⟨s, D, ht, -⟩ := exists_padded hx isCompact_empty
  rw [he ht, he ht]
  apply congr_arg φ
  apply tester_ext
  intro l r
  rw [(matrix_at_center H ht q l r _).2, (matrix_at_center H ht q l r _).2]
  exact h.kernels hde B ((matrix_at_center (V := V) (A := A) H ht q l r ⟨d,B⟩).1) _

lemma middle_derivative (h : Padded s D x) (hp : A.Laws P) (B : S.Field d) (a : Axis)
    (q : Fin n → S.Tag) :
    Analysis.D (Points.direction 0 a) (middle A s D (Fin.cons ⟨d,B⟩ q)) x =
      middle A s D (Fin.cons ⟨d+1,P.deriv d a B⟩ q) x := by
  rw [middle_eq_comp, middle_eq_comp]
  let v : Fin (n+1) → L.Token := Ward.expose ∘ (Fin.cons ⟨d,B⟩ q)
  let y := Points.across s x
  have ht : Slab timeAxis D (realize v y) := carry_realize v x ▸ h.slab v
  have hf : DifferentiableAt ℝ (fun w => A.place D (realize v w)) y :=
    ((hp.regular D (n+1) v y ht).contDiffAt (slab_near v ht)).differentiableAt (by simp)
  unfold Analysis.D
  rw [fderiv_comp x hf (across_derivative s x).differentiableAt, (across_derivative s x).fderiv]
  change Analysis.D _ (fun w => A.place D (realize v w)) y = A.place D (realize _ y)
  rw [hp.positional D (n+1) v y 0 ht a]
  apply congr_arg (A.place D)
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [update_self]
    change Sigma.mk (d+1) (S.representative _ (P.deriv d a (S.project d (S.representative d B)))) =
      ⟨d+1,S.representative _ (P.deriv d a B)⟩
    rw [S.rep]
  rw [update_of_ne (Fin.succ_ne_zero j)]
  simp only [v, comp_apply, Fin.cons_succ]

lemma Evaluates.derivatives (he : Evaluates T A φ) (hp : A.Laws P) : P.Derivatives T := by
  constructor
  intro d a B n x hx q
  obtain ⟨s, D, ht, -⟩ := exists_padded hx isCompact_empty
  let v : Fin (n+1) → S.Tag := Fin.cons ⟨d,B⟩ q
  have hg : (fun y => S.useAt T y v) =ᶠ[𝓝 x] φ ∘ middle A s D v :=
    ht.near.mono fun y hy => he hy v
  rw [he ht, ← middle_derivative ht hp B]
  let c := φ.restrictScalars ℝ
  change φ _ = Analysis.D _ _ _
  rw [GermD _ hg]
  change c _ = fderiv ℝ (c ∘ middle A s D v) x (Points.direction 0 a)
  rw [fderiv_comp x c.differentiableAt (middle_diff ht v hp), c.fderiv]; rfl

end YM.Work.B09
