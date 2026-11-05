import YM.Push.FREE_RESOLVENT.Differentiated
import YM.Push.FREE_RESOLVENT.PatchComparison


/-!
# Patchwise comparison of inverse jets

Even if the arrays of gauges/metric across a whole period don't
intertwine. Include exact correspondence of mark values on addressed slots.
The jets are pulled back to arbitrary COMMON perturbation directions (can be
linear mappings into different V arrays). Thus gives quantitative comparison
also at differing periods. Inputs compare on just the shared patch's forward
precisions; not the inverse here or there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Matrix Filter Function Mark TestD Pane
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {τ X Y E F ι ι' κ : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ] [DecidableEq κ]

namespace TestD
variable {C : Mark τ X} {C' : Mark τ Y} {D : Cost X} {D' : Cost Y} {v : τ → E} {a : ι → X} {b : ι' → Y}
variable {A B : E → Matrix ι ι ℝ} {A' : E → Matrix ι' ι' ℝ} {x : E} {i : κ ↪ ι} {j : κ ↪ ι'}
variable {R s M r d U γ V u ε N : ℝ} {k : ℕ}

omit [DecidableEq ι] in
lemma Knew.test {A : E → Matrix ι ι ℝ} {v : τ → F} (L : F →L[ℝ] E)
    (h : Knew C D a (L ∘ v) 0 k s M r ε A) : Knew C D a v 0 k s M r ε (A ∘ L) := by
  refine ⟨ContDiffAt.comp 0 (by rw [map_zero]; exact h.smooth) L.contDiff.contDiffAt, by simpa using h.gap, by simpa using h.schur,?_⟩
  intro l hl hk
  have he : jet v (A ∘ L) l 0 = jet (L ∘ v) A l 0 := by
    unfold jet; rw [YM.Next.Foundations.jets_linear L (smooth_of_le h.smooth hk)]; rfl
  rw [he]; exact h.jets _ hl hk

def patchFee (d R M U V Q : ℝ) (k : ℕ) := tagPrice U k Q (Real.exp (-(k+1:ℕ)*d*R)*tagPrice U k M (V*Q))



/-- Shared marks can refer to the projected origin x both as a Taylor
position and for transfer costs. -/
def Comark (e : κ → X) (f : κ → Y) (C : Mark τ X) (C' : Mark τ Y) := ∀ k t, C.cents t (e k)=C'.cents t (f k)
omit [DecidableEq κ] [Fintype κ] in
lemma Comark.same {e : κ → X} {f : κ → Y} (hc : Comark e f C C') (l k) : C.pay l (e k) = C'.pay l (f k) := by
  induction l with
  | nil => rfl
  | cons t l h => rw [pay,pay,h,hc k t]
omit [DecidableEq κ] in
lemma sharing {e : κ → X} {f : κ → Y} (hc : Comark e f C C') (he : D.pull e = D'.pull f)
    {P : E → Matrix κ κ ℝ} (h : Knew C' D' f v x k s M r ε P) : Knew C D e v x k s M r ε P := by
  refine ⟨h.smooth,h.gap,rows_here he.symm (P x) h.schur,fun l ha hl => ?_⟩
  have hh := h.jets l ha hl
  have ht (i j) : D.weight s (e i) (e j)=D'.weight s (f i) (f j) := congrArg (fun K : Cost κ => K.weight s i j) he
  constructor <;> constructor <;> intro i <;> simp_rw [hc.same l,ht]
  · exact hh.row.rows i
  exact hh.col.rows i


end TestD
end YM.FreeResolvent
