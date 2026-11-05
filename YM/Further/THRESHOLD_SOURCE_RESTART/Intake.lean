import YM.Extra.MULTISOURCE_BOUNDS.LogTerms
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
/-!
# Income transfer per occurrence

Donor → any of its variants, **in unscaled currency at output exponent
through every tested use**, not just the exponent after the step. Keeps the
whole marker-mode and support bill of the occurrence. We never need to
interpret a variant's *pricing* support as its read on marginal fine
configurations. The physical shape/identities for entries which become
output are imposed separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart
open Function Filter MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Prepare Width Extra.Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {V α β : Type*} {m n : Side}

/-- Each support-export variant assigned to its input donor address. Flexible
for step vs. same-lattice restart; only a pricing test but on the SUPPORT cost
of every charged variant. `γ` pays normalization (e.g. a pre-L constant in the
principal transfer). Multiplicity explicitly in finite sums.
-/
structure Route (v : α → Finset V) (X : α → Support n) (M : ℕ) (A : ℝ) (f : α → ℝ) (o : V → Site m)
    (t : β → Finset V) (Y : β → Support m) (B : ℕ) (a : ℝ) (g : β → ℝ) (c : ℝ) : Prop where
  pos i : 0 ≤ g i
  tone : ∃ p : β → α, (∀ i, 0 < g i → t i = v (p i) ∧ ∃ j ∈ t i, o j ∈ Y i) ∧
    ∀ j s, (∀ i∈s,p i=j) → (∑ i∈s,Real.exp (a*coverNumber B (Y i))*g i) ≤ c*Real.exp (A*coverNumber M (X j))*f j

variable {v : α → Finset V} {X : α → Support n} {f : α → ℝ} {o : V → Site m} {M B : ℕ} {A a b c : ℝ}
    {t : β → Finset V} {Y : β → Support m} {g : β → ℝ} {w : V → ℝ}
abbrev tariff (w : V → ℝ) (v : α → Finset V) (f : α → ℝ) :=
    fun i => LogTerms.duty w (v i)*f i
lemma tariff_nonneg (hf : ∀ i,0 ≤ f i) (hw : ∀ v,0 < w v) (i) : 0 ≤ tariff w v f i :=
  mul_nonneg (Finset.prod_nonneg fun v _ => (hw v).le) (hf i)


/-- No absolute torus volume bill. All marker weights `w` permitted by the
preceding levels can be kept. -/
theorem Route.cost (h : Route v X M A f o t Y B a g c) (hw : ∀ v,0<w v) (hc : 0 ≤ c)
    (hh : Rooted v X M A (tariff w v f) b) : Rooted t Y B a (tariff w t g) (c*b) := by
  intro x
  let C i := if x∈t i then Real.exp (a*coverNumber B (Y i)) * tariff w t g i else 0
  let D i := if x∈v i then Real.exp (A*coverNumber M (X i)) * tariff w v f i else 0
  have hp : SumBudget D b := hh x
  have ht i : 0 ≤ C i := by unfold C; split; exact mul_nonneg (Real.exp_pos _).le (tariff_nonneg h.pos hw i); rfl
  refine Budget.certify ht ?_
  obtain ⟨p,hp',hu⟩ := h.tone
  intro s; let S i := s.filter fun j => p j=i
  have hE i : ∑ j∈S i,C j ≤ c * D i := by
    let W := LogTerms.duty w (v i)
    have hW : 0 ≤ W := Finset.prod_nonneg fun i _ => (hw _).le
    by_cases hi : x∈v i
    · calc
        _ ≤ ∑ j∈S i,W * (Real.exp (a*coverNumber B (Y j)) * g j) := by
          apply Finset.sum_le_sum; intro j hj; unfold C; split
          next =>
            rcases (h.pos j).eq_or_lt with hb|hb
            · exact le_of_eq (by simp only [tariff,← hb,mul_zero])
            unfold tariff; rw [(hp' j hb).1, (Finset.mem_filter.mp hj).2,mul_left_comm]
          exact mul_nonneg hW (mul_nonneg (Real.exp_pos _).le (h.pos j))
        _ ≤ _ := by
          rw [← Finset.mul_sum]; refine (mul_le_mul_of_nonneg_left (hu _ _ (fun _ hj => (Finset.mem_filter.mp hj).2)) hW).trans (le_of_eq ?_)
          dsimp only [D]; rw [if_pos hi]; unfold tariff W; ring
    rw [show D i=0 from if_neg hi,mul_zero]
    apply le_of_eq (Finset.sum_eq_zero fun j hj => ?_)
    dsimp only [C]; split
    next hx =>
      rcases (h.pos j).eq_or_lt with hb|hb
      · unfold tariff; rw [← hb]; simp
      exact (hi ((Finset.mem_filter.mp hj).2 ▸ (hp' j hb).1 ▸ hx)).elim
    rfl
  change ∑ i∈s, C i≤_
  calc
    _ = ∑ j∈s.image p,∑ i∈S j,C i := (Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem p hj) C).symm
    _ ≤ _ := (Finset.sum_le_sum fun i _ => hE i).trans (Budget.cap (Budget.scale hp hc) _)


end YM.Further.ThresholdSourceRestart
