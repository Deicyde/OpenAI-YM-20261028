import YM.Analysis.Exchange

/-!
# Finite Taylor substitution tools

Used by G05 on the analytic-at-zero local recovery map itself, before
substituting it into any reference polynomials. Work over the reals,
including for complex-valued outputs. We only need finite regularity in
these lemmas.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.G05
open Function Filter YM.Analysis
open scoped Topology ContDiff BigOperators

variable {E F J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup J] [NormedSpace ℝ J]
  {d : ℕ} {f f' : E → F}

/-- Congruence through finite order, also for changing both functions in a composition. -/
theorem jets_comp {g g' : F → J} {x : E}
    (hf : ContDiffAt ℝ d f x) (hf' : ContDiffAt ℝ d f' x)
    (hg : ContDiffAt ℝ d g (f x)) (hg' : ContDiffAt ℝ d g' (f' x))
    (h0 : f x = f' x)
    (h₁ : ∀ k ≤ d, iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k f' x)
    (h₂ : ∀ k ≤ d, iteratedFDeriv ℝ k g (f' x) = iteratedFDeriv ℝ k g' (f' x)) :
    ∀ k ≤ d, iteratedFDeriv ℝ k (g ∘ f) x = iteratedFDeriv ℝ k (g' ∘ f') x := by
  intro k hk
  have hi : (k : WithTop ℕ∞) ≤ (d : WithTop ℕ∞) := Nat.cast_le.mpr hk
  rw [iteratedFDeriv_comp hg hf hi, iteratedFDeriv_comp hg' hf' hi, h0]
  apply Finset.sum_congr rfl
  intro c _
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition, ftaylorSeries]
  rw [h₂ c.length (c.length_le.trans hk),
    show (fun m => iteratedFDeriv ℝ (c.partSize m) f x) =
        (fun m => iteratedFDeriv ℝ (c.partSize m) f' x) from
      funext fun m => h₁ _ ((c.partSize_le m).trans hk)]

/-- Finite Taylor polynomial as a function on a real vector space. -/
def blockTaylor (d : ℕ) (f : E → F) : E → F :=
  ∑ j ∈ Finset.range (d+1), Tensor.diagonal (Tensor.coeff f j 0)

theorem blockTaylor_contDiff (d : ℕ) (f : E → F) (k : WithTop ℕ∞) :
    ContDiff ℝ k (blockTaylor d f) := by
  rw [show blockTaylor d f = (fun x => ∑ j ∈ Finset.range (d+1),
    Tensor.diagonal (Tensor.coeff f j 0) x) from funext fun x => Finset.sum_apply ..]
  exact ContDiff.sum fun j _ => Tensor.diag_smooth (Tensor.coeff f j 0) k

theorem blockTaylor_zero (d : ℕ) (f : E → F) : blockTaylor d f 0 = f 0 := by
  classical
  rw [blockTaylor, Finset.sum_apply, Finset.sum_eq_single 0]
  · exact Tensor.coeff_apply_zero _ _ _
  · intro b _ hb
    simpa [hb] using Tensor.homogeneous (Tensor.coeff f b 0) 0 0
  · intro h; simp at h

/-- `Tensor.slot_lower` identifies each summand for this differentiation,
with the factorials already accounted for. The polynomial identities hold
globally; `f` is assumed sufficiently smooth only at zero. -/
theorem D_blockTaylor (hf : ContDiffAt ℝ (↑(d+1 : ℕ)) f 0) (u : E) :
    D u (blockTaylor (d+1) f) = blockTaylor d (D u f) := by
  classical
  funext z
  let T (j : ℕ) := Tensor.diagonal (Tensor.coeff f j 0)
  have ht (j : ℕ) : DifferentiableAt ℝ (T j) z :=
    (Tensor.diag_smooth _ 1).contDiffAt.differentiableAt one_ne_zero
  have ht0 : fderiv ℝ (T 0) z = 0 := by
    rw [show T 0 = (fun _ => f 0) from funext fun _ => Tensor.coeff_apply_zero _ _ _]
    exact fderiv_const_apply ..
  change fderiv ℝ (∑ j ∈ Finset.range (d+1+1), T j) z u = _
  rw [fderiv_sum (fun i _ => ht i), sum_apply,
    Finset.sum_range_succ', ht0]
  simp only [zero_apply, add_zero]
  rw [blockTaylor, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  exact Tensor.slot_lower (hf.of_le (Nat.cast_le.mpr (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))) u z

/-- These are all the real Fréchet jets, including order 0. -/
theorem blockTaylor_jets (hf : ContDiffAt ℝ d f 0) :
    ∀ k ≤ d, iteratedFDeriv ℝ k (blockTaylor d f) 0 = iteratedFDeriv ℝ k f 0 := by
  induction d generalizing f with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := Nat.eq_zero_of_le_zero hk
    ext1 v
    simp [blockTaylor_zero]
  | succ d ih =>
    intro k hk
    ext1 v
    cases k with
    | zero => simp [blockTaylor_zero]
    | succ k =>
      have ht : ContDiffAt ℝ (↑(k+1 : ℕ)) (blockTaylor (d+1) f) 0 :=
        (blockTaylor_contDiff (d+1) f _).contDiffAt
      have hf' : ContDiffAt ℝ (↑(k+1 : ℕ)) f 0 := hf.of_le (Nat.cast_le.mpr hk)
      have he := ih (f := D (v 0) f) (dSmooth hf _ (by push_cast; rfl)) k (Nat.le_of_succ_le_succ hk)
      rw [← Fin.cons_self_tail v, cons_inner ht, cons_inner hf', D_blockTaylor hf, he]

/-- Taylor truncation turns equivariance of germs into equivariance on the
whole vector spaces. Use `jets_comp` to apply the global linear
precomposition derivative formula only to the polynomial. -/
theorem blockTaylor_equivariant (hf : ContDiffAt ℝ d f 0) (L : E →L[ℝ] E) (R : F →L[ℝ] F)
    (h : f ∘ L =ᶠ[𝓝 0] R ∘ f) (x : E) : blockTaylor d f (L x) = R (blockTaylor d f x) := by
  have ht : ContDiff ℝ (d : WithTop ℕ∞) (blockTaylor d f) := blockTaylor_contDiff d f _
  have hc : ∀ k ≤ d, iteratedFDeriv ℝ k (blockTaylor d f ∘ L) 0 =
      iteratedFDeriv ℝ k (f ∘ L) 0 := by
    refine jets_comp L.contDiff.contDiffAt L.contDiff.contDiffAt ht.contDiffAt ?_ rfl (fun _ _ => rfl) ?_
    · rw [map_zero]; exact hf
    · rw [map_zero]; exact blockTaylor_jets hf
  unfold blockTaylor
  rw [Finset.sum_apply, Finset.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hd := (hc k he).trans ((h.iteratedFDeriv ℝ k).eq_of_nhds)
  have hk' : (k : WithTop ℕ∞) ≤ (d : WithTop ℕ∞) := Nat.cast_le.mpr he
  rw [L.iteratedFDeriv_comp_right ht 0 hk', R.iteratedFDeriv_comp_left hf hk',
    map_zero, blockTaylor_jets hf k he] at hd
  have hy : iteratedFDeriv ℝ k f 0 (fun _ => L x) = R (iteratedFDeriv ℝ k f 0 (fun _ => x)) :=
    congr_arg (fun A : Tensor.T E F k => A (fun _ => x)) hd
  simp only [Tensor.diagonal, Tensor.coeff, smul_apply, hy, map_smul]

end YM.Work.G05
