import YM.Trace.Ordered

/-! Keep the same local stress and fix the subtraction by the actual selected one-point
function. -/
noncomputable section
namespace YM.Trace
open Boundary Table Function Complex MeasureTheory Filter
open scoped Topology BigOperators ContDiff
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order} (Y : Spec.Final C f S)

abbrev state (Y : Spec.Final C f S) := Y.α.ensemble Y.α.atPoint
lemma fits : (state Y).respects S  := fun _ => le_of_eq (Y.phase.phase.retains .. |>.symm)

noncomputable def oneptL (k : ℕ) : S.Field k→ₗ[ℂ] ℂ := (S.classMoment (state Y) (n:=1) (fun _ => k) 0).toLinearMap
    (fun _ => 0) 0
lemma onept_eq {k : ℕ} (b : S.Field k) : oneptL Y k b=S.useAt (state Y) 0 (fun _ : Fin 1 => ⟨k,b⟩) := by
  unfold oneptL useAt; simp only [MultilinearMap.toLinearMap_apply]; congr 1; funext i; fin_cases i
  exact (by simp)
omit Y in
lemma valid_one (x : Points 1) : x∈conf _ := by intro i j hij; exact Subsingleton.elim i j
lemma onept_project {k : ℕ} (b : C.book.Ref k) (x : Points 1 := 0) :
    S.useAt (state Y) x (fun _ : Fin 1 => ⟨k,S.project _ b⟩) = (state Y).read x (fun _ : Fin 1 => ⟨k,b⟩) :=
  S.at_project (state Y) (Y.phase.phase.states .. |>.laws.toSymmetric) (fits Y) (valid_one x) (fun _ => (⟨k,b⟩: C.book.Token))
lemma onept_at {k : ℕ} (b : S.Field k) (x : Points 1) : oneptL Y k b=S.useAt (state Y) x (fun _ : Fin 1 => ⟨k,b⟩) := by
  obtain ⟨v,rfl⟩ := S.onto k b
  rw [onept_eq,onept_project,onept_project Y v x]
  convert (Y.phase.phase.states Y.α.atPoint).translations 1 0 (valid_one _) (x 0) _ |>.symm
  exact PiLp.ext (fun i=>by fin_cases i; change x 0=0+x 0; simp)
lemma onept_unit (k) : oneptL Y k (S.unit k)=1 := by
  rw [unit,onept_eq, onept_project]
  let H := Y.phase.phase.states Y.α.atPoint |>.laws
  refine Eq.trans ?_ (H.trivial (fun _ : Fin 0=> C.book.one k) (Points.tail (0: Points 1)))
  rw [← H.unital (valid_one _) k (fun _ : Fin 0 => C.book.one k)]
  congr 1; ext1 i; fin_cases i; rfl
lemma onept_conj (k) (z : S.Field k) : oneptL Y k (S.conj Y.room.kernel.spin k z)=star (oneptL Y k z) := by
  obtain ⟨v,rfl⟩ := S.onto k z
  simp_rw [S.conj_project]; rw [onept_eq, onept_eq,onept_project Y,onept_project];
  exact (Y.phase.phase.states _).spin.real (valid_one _) (fun _ : Fin 1 => (⟨k,v⟩ : C.book.Token))
  -- may need ext
def meanExact (Y : Spec.Final C f S) : ℝ := (oneptL Y 4 (theta Y 0)).re

theorem mean_correct : (oneptL Y 4 (theta Y 0))=(meanExact Y : ℂ) := by
  have he := onept_conj Y _ (theta Y 0); rw [theta_real Y] at he
  apply Complex.ext
  · rfl
  rw [Complex.star_def] at he; have he' := congrArg im he; rw [conj_im] at he'
  rw [ofReal_im]; exact_mod_cast (by linarith [he'] : _)

abbrev traceField (Y : Spec.Final C f S) : S.Field 4 := theta Y (meanExact Y)
lemma traceField_eq : traceField Y = theta Y 0 - (meanExact Y:ℂ) • S.unit 4 := by simp [traceField,theta,withoutMean]
lemma centered_zero (x : Points 1) : S.useAt (state Y) x (fun _i : Fin 1 => (⟨4,traceField Y⟩ : S.Tag)) = 0 := by
     rw [← onept_at, traceField_eq Y,map_sub, map_smul,onept_unit]; simp_rw [mean_correct]; simp

/-- Existence of the nonnegative tempered measure via the actual field-domain translation
system, and equality of its energy Laplace transforms to the corresponding strict Euclidean
values. The phase in `restTrace` is the one selected by `Y`. No big-log estimate needed here. -/
theorem centered_spectral : let v := oneWave Y (S.pin 4 (traceField Y));
   ∃ M : Measure E4, Tempered M ∧ M (Mink.coneᶜ)=0 ∧
      (∀ s : ℝ, 0<s → restTrace Y (meanExact Y) s=↑(∫ p, Real.exp (-s*time p) ∂M)) ∧
      ∀ a b : Test4, inner ℂ (v a) (v b)=∫ x, paid M a b x ∂M := by
   obtain ⟨M,hM,hN,hm⟩ := theta_measure Y (meanExact Y)
   exact ⟨M,hM,hN,fun s => fun h => (heat_eq_rest Y hM hN (meanExact Y) s h hm).trans integral_complex_ofReal,hm⟩
end YM.Trace
