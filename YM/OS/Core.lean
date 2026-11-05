import YM.OS.Dynamics

/-!
# Heat-zero space and projection, without spectral theory
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter InnerProductSpace
open scoped NNReal Topology BigOperators InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S : Semigroup H a)

/-- Invariant under all forward time, not assumed vacuum span. -/
def ground : Submodule ℂ H := ⨅ t, LinearMap.ker ((S.E t).toLinearMap-LinearMap.id)

lemma fixed (x : H) : x ∈ S.ground ↔ ∀ t : ℝ≥0, S.E t x = x := by
  rw [ground, Submodule.mem_iInf]; simp [sub_eq_zero]

instance : CompleteSpace S.ground := by
  have he : ((S.ground : Submodule ℂ _) : Set H) = ⋂ t, {x : H | S.E t x=x} := by
    ext x; simp [S.fixed x]
  haveI : IsClosed ((S.ground : Submodule ℂ _) : Set H) := by rw [he]; exact isClosed_iInter fun t => isClosed_eq (S.E t).continuous continuous_id
  infer_instance

abbrev orth := S.ground.starProjection

theorem norm_decrease (x : H) : Antitone fun t => ‖S.E t x‖ := by
  intro i j h
  change ‖S.E j x‖ ≤ ‖S.E i x‖
  conv_lhs => rw [← tsub_add_cancel_of_le h, S.time]
  exact ((S.E (j-i)).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))

lemma swing t (x y : H) : inner ℂ (S.E t x) y = inner ℂ x (S.E t y) := by
  conv_lhs => rw [← S.sym t]
  rw [ContinuousLinearMap.adjoint_inner_left]

theorem emerges (x : H) : Tendsto (fun t => S.E t x) atTop (𝓝 (S.orth x)) := by
  let f t := S.E t x
  have he : Antitone (fun t => ‖f t‖^2) := fun _ _ h => sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)
    |>.mpr (S.norm_decrease x h)
  let c := ⨅ t, ‖f t‖^2
  have hb : BddBelow (range fun t => ‖f t‖^2) := ⟨0,by rintro z ⟨y,rfl⟩; exact sq_nonneg _⟩
  have hl : Tendsto (fun t => ‖f t‖^2) atTop (𝓝 c) := tendsto_atTop_ciInf he hb
  have hi (u v) : inner ℂ (f u) (f v) = inner ℂ x (f (u+v)) := by unfold f; rw [S.swing,S.time]; rfl
  have hh (u v) (h : u ≤ v) : dist (f u) (f v) ^ 2 ≤ ‖f u‖^2 - ‖f v‖^2 := by
    let t := (u+v)/2
    have ht : t≤v := by unfold t; rw [div_le_iff₀ (by positivity)]; rw [mul_two]; gcongr
    have hw : t+t=u+v := by simp [t]
    rw [dist_eq_norm,norm_sub_sq (𝕜 := ℂ),hi u v,← hw, ← hi,inner_self_eq_norm_sq]
    linarith [he ht]
  have ht : CauchySeq f := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hp
    obtain ⟨N,hN⟩ := (hl.eventually (gt_mem_nhds
      (show c<c+ε^2 from lt_add_of_pos_right _ (pow_pos hp 2)))).exists
    refine ⟨N,fun i h => ?_⟩
    apply (sq_lt_sq₀ dist_nonneg hp.le).mp
    have hn := hh N i h; rw [dist_comm] at hn
    have hy : c≤‖f i‖^2 := ciInf_le hb i
    change ‖f N‖ ^2 < c + ε^2 at hN
    linarith
  obtain ⟨y,hY⟩ := cauchySeq_tendsto_of_complete ht
  have hv : y ∈ S.ground := (S.fixed _).mpr fun t => by
    have hu : (fun i => f (t+i)) = fun i => S.E t (f i) := by funext i; unfold f; rw [S.time]; rfl
    have hw : Tendsto (fun i => f (t+i)) atTop (𝓝 y) := hY.comp (show Tendsto (fun i => t+i) atTop atTop from
      tendsto_atTop_mono (show (fun i => i) ≤ fun i => t+i from fun i => by simp) tendsto_id)
    rw [hu] at hw
    exact tendsto_nhds_unique ((S.E t).continuous.continuousAt.tendsto.comp hY) hw
  suffices h : y=S.orth x from h ▸ hY
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hv
  intro u hu
  have hx (t) : inner ℂ (f t) u = inner ℂ x u := by unfold f; rw [S.swing,(S.fixed _).1 hu]
  have he : inner ℂ x u=inner ℂ y u := tendsto_nhds_unique (f := fun t => inner ℂ (f t) u)
    (tendsto_const_nhds.congr' (Eventually.of_forall fun i => (hx i).symm))
    (hY.inner tendsto_const_nhds)
  rw [inner_sub_left,he,sub_self]
end YM.OS.Semigroup
