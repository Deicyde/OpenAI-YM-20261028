import YM.Ward.Sum

/-!
# Angular jets for fixed anchor line (no continuation yet)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Ward
open Set Function Filter Analysis Table
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

/-- `cast`, `propagates`: one-axis along i(b) straight segment. -/

def cast (x : Points n) (j : Fin n) (b : Axis) (t : ℝ) : Points n := x+t • Points.direction j b
@[simp] lemma start x (j : Fin n) b : cast x j b 0=x := by rw [cast, zero_smul,add_zero]
@[simp] lemma atCast x (j : Fin n) b t : cast x j b t j= inc b (x j) t := by simp [cast,Points.direction,inc]
lemma near x (j i : Fin n) (h : i ≠ j) b t : cast x j b t i=x i := by simp [cast,Points.direction,h]

theorem moves (x : Points n) (j) b t : HasDerivAt (cast x j b) (Points.direction j b) t := by
  have he := (ContinuousLinearMap.toSpanSingleton ℝ (Points.direction j b)).hasDerivAt (x := t)
  unfold cast; simpa using he.const_add x

variable (W : DiffPlan S) (T : SpinRows S)
theorem arrow (h : S.Hierarchy) (g : W.Derivatives S) (hc : commutes W T) (K : Ortho.Skew) (q : Fin n → S.Tag)
    (x : Points n) (j b s) (ht : cast x j b s∈conf _) :
    HasDerivAt (angular W T q K ∘ cast x j b) (angular W T (update q j (rise W b (q j))) K (cast x j b s)) s := by
  rw [← traverses W T h g hc ht]; exact ((ac W T h ht K q).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt s (moves x j b s)

lemma jet_line (h : S.Hierarchy) (g : W.Derivatives S) (hc : commutes W T) (K : Ortho.Skew) (q : Fin n → S.Tag)
    (x : Points n) (i b s) (ht : cast x i b s ∈ conf _) (hp : ∀ w, angular W T w K (cast x i b s)=0) (m : ℕ) :
    iteratedDeriv m (angular W T q K ∘ cast x i b) s=0 := by
  induction m generalizing q with
  | zero => simp [hp]
  | succ m ih =>
    have hx := (conf_open _).mem_nhds ht
    have hu : deriv (angular W T q K ∘ cast x i b) =ᶠ[𝓝 s] angular W T (update q i (rise W b (q i))) K ∘ cast x i b :=
      Eventually.mono (p := fun j => cast x i b j ∈ conf n) ((moves _ _ _ s).continuousAt.preimage_mem_nhds hx)
        fun k hk => (arrow W T h g hc K q _ _ _ _ hk).deriv
    rw [iteratedDeriv_succ', hu.iteratedDeriv_eq (n := m)]
    exact ih _
end YM.Ward
