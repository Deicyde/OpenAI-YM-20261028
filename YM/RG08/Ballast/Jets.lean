import YM.RG08.Ballast.Coda
import YM.Analysis.Exchange

/-! # Homogeneous Taylor coefficients for stanzas

Seats ℝ. Using Sharp Maxwell `coeff_diagonal` METHOD with generic E.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Set Function Filter Finset Tensor Analysis
open scoped Topology ContDiff

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {j k : ℕ}
lemma coeff_at_diagonal (A : T E F j) (ha : Sym A) : coeff (diagonal A) j 0=A := by
  induction j with
  | zero => ext1 u; rw [coeff_apply_zero]; exact congr_arg A (Subsingleton.elim ..)
  | succ j ih =>
    ext1 b
    let C (v : E) := (A.curryLeft v)
    let t := ((↑(j+1 : ℕ)) : ℝ)
    have hy (v : E) : Analysis.D v (diagonal A)=t • diagonal (C v) := by
      funext u; unfold Analysis.D; rw [differential_diagonal _ ha, ← Nat.cast_smul_eq_nsmul ℝ]; rfl
    have ht : t≠0 := by unfold t; positivity
    rw [← Fin.cons_self_tail b,coeff_apply_cons ((diag_smooth _ _).contDiffAt),hy, coeff_smul _ ((diag_smooth _ _).contDiffAt),ih _ (freeze_sym _ ha _),_root_.smul_apply]
    rw [inv_smul_smul₀ ht]; rfl
lemma coeff_diagonal_else (A : T E F j) (ha : Sym A) (hv : k≠j) : coeff (diagonal A) k 0=0 := by
  induction k generalizing j with
  | zero =>
    cases j with
    | zero => exact (hv rfl).elim
    | succ j => ext1 u; rw [coeff_apply_zero]; exact A.map_coord_zero (0 : Fin (j+1)) rfl
  | succ k ih =>
    ext1 b; rw [← Fin.cons_self_tail b, coeff_apply_cons ((diag_smooth _ _).contDiffAt)]
    cases j with
    | zero =>
      rw [show diagonal A=(fun _=> diagonal A 0) from funext fun _=>congr_arg A (Subsingleton.elim ..)]
      rw [show Analysis.D (b 0) (fun _=> diagonal A 0)=(fun _ => (0:F)) from funext fun _=> by simp [Analysis.D]]; simp
    | succ j =>
      let C (v:E) := A.curryLeft v
      let t := ((↑(j+1 : ℕ)):ℝ)
      rw [show Analysis.D (b 0) (diagonal A)=t • diagonal (C (b 0)) from funext fun u=> by unfold Analysis.D; rw [differential_diagonal _ ha,← Nat.cast_smul_eq_nsmul ℝ]; rfl, coeff_smul _ ((diag_smooth _ _).contDiffAt), ih _ (freeze_sym _ ha _) (by omega)]; simp

open RG Laurent Lattice Wilson Bloch
variable {α : Type} [Fintype α] {m : Side}

lemma extract_verses {K : Shale α j} (h : Summable K) (m : Side) :
    Tensor.coeff (stanza K m) j 0=recital (score K) m := by
  rw [← stanza_score h]; exact coeff_at_diagonal _ (score_tunable h|>.2.2 m)
lemma extract_else {K : Shale α j} (h : Summable K) (hv : k≠j) (m : Side) : Tensor.coeff (stanza K m) k 0=0 := by
  rw [← stanza_score h]; exact coeff_diagonal_else _ (score_tunable h|>.2.2 m) hv
lemma Tunable.pick {K : Shale α j} (h : Tunable K) (m : Side) : Tensor.coeff (stanza K m) j 0=recital K m := by rw [extract_verses h.1,h.score_eq]
end YM.RG08
