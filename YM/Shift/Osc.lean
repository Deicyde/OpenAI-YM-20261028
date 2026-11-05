import YM.Shift.Breath

/-!
# Surfaces of heights all WITHOUT ratio restrictions (absolute Points)
from power and lines. No tensor density baked in. -/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary.Waves
open Filter Set Function MeasureTheory Probe Complex LinearMap
open scoped Topology ContDiff BigOperators Interval ENNReal
variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ} (F : Waves S)

section price
variable {v : Fin n → S.Union} {C : ℝ} {m : ℕ}
variable (hm : ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x, ‖F.restricted v y x‖ ≤ C*k⁻¹^m)

def toll (f : Joint n) (C : ℝ) (m : ℕ) := (∑ j ∈ Finset.range (m+1), ‖coal 1 j‖*(C*weight (moves j f)))+
    C*weight (moves (m+1) f)
lemma tolls (m : ℕ) (C : ℝ) : toll (0:Joint n) C m=0 ∧ Continuous fun f : Joint n => toll f C m := by
  unfold toll
  refine ⟨by simp,?_⟩
  apply Continuous.add
  · apply continuous_finsetSum; intro j _; exact Continuous.const_mul (Continuous.const_mul (weight_cont.comp (moves j).continuous) C) _
  exact Continuous.const_mul (weight_cont.comp (moves (m+1)).continuous) _

include hm
lemma cost (y) (hy : y∈sunrise n) (f : Joint n) : ‖F.desired v m y f‖ ≤ toll f C m := by
  unfold desired toll
  refine (norm_sub_le ..).trans (add_le_add ?_ ?_)
  · unfold pol; apply (norm_sum_le ..).trans (Finset.sum_le_sum fun j _ => ?_)
    have he := beam F m C hm hy (moves j f) (show (1:ℝ)∈Ioc 0 1 from ⟨zero_lt_one,le_rfl⟩)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (by simpa only [rocks,one_pow,one_mul] using he) (norm_nonneg _)
  have hh := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (0:ℝ) 1))
    (g := fun _ => C*weight (moves (m+1) f)) (f := F.wind v m y f) (integrable_const _)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun _ hx => F.expense _ hm _ hy f hx)
  simpa using hh

lemma storm (h : F.Along) (p : F.Lines) (y) (hy : y∈sunrise n) (f : Joint n) : Tendsto (fun x => F.psi v x f)
    (𝓝[east n] y) (𝓝 (F.desired v m y f)) := by
  apply ((F.maintains v h _ hm f y hy).mono fun x t => bigger (n:=n) t).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx using F.meant h p _ _ hx f m
end price

lemma seeks (h : F.Bounds) (ha : F.Along) (hm : F.Lines) (hp : F.Breathes) (y) (hy : y∈sunrise n) :
    ∃ W : MultilinearMap ℂ (fun _ : Fin n => S.Union) (Distn (Points n)), ∀ (v : Fin n → S.Union) (f : Joint n),
    Tendsto (fun t => F.psi v t f) (𝓝[east n] y) (𝓝 (W v f)) := by
  classical
  let T := 𝓝[east n] y
  have hT : T.NeBot := awaits hy
  choose m C hC H using hp n
  let g (v : Fin n → S.Union) := F.desired v (m v) y
  have hg v f : Tendsto (fun t => F.psi v t f) T (𝓝 (g v f)) := F.storm (H v) ha hm y hy f
  let D (v : Fin n → S.Union) : Joint n→ₗ[ℂ] ℂ :=
    { toFun := g v
      map_add' := by
        intro f p; refine tendsto_nhds_unique (hg v (f+p)) (((hg v f).add (hg v p)).congr' ?_)
        filter_upwards [self_mem_nhdsWithin (a:=y) (s:=east n)] with t ht
        unfold psi; rw [← integral_add (h n v t ht f) (h n v t ht p)]
        apply integral_congr_ae; filter_upwards with x; simp [mul_add]
      map_smul' := by
        intro c f; apply tendsto_nhds_unique (hg v (c•f)) (((hg v f).const_mul c).congr' ?_)
        filter_upwards [self_mem_nhdsWithin (a:=y) (s:=east n)] with t ht
        unfold psi; rw [← integral_const_mul]; congr! 1; ext x; simp; ring }
  let W (v) : Distn (Points n) := ⟨D v, sways (fun f => toll f (C v) (m v)) (tolls (m v) (C v)).2 (tolls (m v) (C v)).1 (fun f => F.cost (H v) y hy f)⟩
  let B : MultilinearMap ℂ (fun _ : Fin n => S.Union) (Distn (Points n)) :=
    { toFun := W
      map_update_add' := by
        intro _ v j x z; ext1 f
        refine tendsto_nhds_unique (hg (update v j (x+z)) f) (((hg (update v j x) f).add (hg (update v j z) f)).congr' ?_)
        filter_upwards [self_mem_nhdsWithin (a:=y) (s:=east n)] with t ht
        unfold psi
        rw [← integral_add (h n _ t ht _) (h n _ t ht _)]
        congr! 1; ext p; simp [restricted,add_mul]
      map_update_smul' := by
        intro _ v j c x; ext1 f
        refine tendsto_nhds_unique (hg (update v j (c•x)) f) (((hg (update v j x) f).const_mul c).congr' ?_)
        filter_upwards [self_mem_nhdsWithin (a:=y) (s:=east n)] with t ht
        unfold psi
        rw [← integral_const_mul]; congr! 1; ext p; simp [restricted,mul_assoc] }
  exact ⟨B,hg⟩

/-- All ordered heights, *not just fixed slopes*, as required for Hilbert vector limits. -/
lemma jointly (h : F.Bounds) (ha : F.Along) (hm : F.Lines) (hp : F.Breathes) :
    ∃ W : Surface S, F.NonTangentialFree W := by
  choose B hB using fun n : ℕ => F.seeks h ha hm hp 0 (light n)
  exact ⟨⟨B⟩,⟨h,hB⟩⟩
end YM.Boundary.Waves
