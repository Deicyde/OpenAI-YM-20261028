import YM.Bid.Phase

/-!
# Deriving all the (fixed arity and fixed labels) caps from `OneCap`

First bound the iterated derivatives of `S.useAt T` using label
derivatives on the S tags (with all spectators allowed). Recover norms
at each induction step using finite sums of coordinate bounds. Then
transfer the statement to raw T labels by `T.respects S`. All jet
identifications here are local in `conf`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.B10

open Function Filter
open scoped Topology ContDiff BigOperators

variable {n : ℕ}

/-- Norm on positions is ℓ² over the point index, of ℓ² over spacetime
indices. A loose operator-norm estimate; the sum avoids having to ask
for a nonzero-dimensional position space (`n=0` also works). -/
theorem norm_le_direction_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Points n →L[ℝ] E) : ‖F‖ ≤ ∑ b : Fin n × Axis, ‖F (Points.direction b.1 b.2)‖ := by
  refine F.opNorm_le_bound (by positivity) fun u => ?_
  have hu : ∑ b : Fin n × Axis, (u b.1 b.2) • Points.direction b.1 b.2 = u := by
    ext i a
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp [Points.direction, Pi.single_apply, apply_ite]
  calc
    ‖F u‖ = ‖∑ b : Fin n × Axis, (u b.1 b.2) • F (Points.direction b.1 b.2)‖ := by
      conv_lhs => rw [← hu]
      simp only [map_sum, map_smul]
    _ ≤ ∑ b : Fin n × Axis, ‖(u b.1 b.2) • F (Points.direction b.1 b.2)‖ := norm_sum_le _ _
    _ ≤ _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun b _ => ?_
      rw [norm_smul, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (PiLp.norm_apply_le (u b.1) b.2).trans (PiLp.norm_apply_le u b.1)

variable {G : Gauge} {L : Register G} {S T : Table L} (P : DiffPlan S)

/-- One more positional coordinate derivative can be paid for as a shift in a
tag in `S.useAt T` (using the specified representatives). -/
theorem jet_at_direction (h : P.Derivatives T) (hs : T.Smooth) (hp : T.Symmetric)
    (v : Fin n → S.Tag) {x : Points n} (hx : x ∈ conf n) (i : Fin n) (a : Axis) (j : ℕ) :
    fderiv ℝ (iteratedFDeriv ℝ j (fun y => S.useAt T y v)) x (Points.direction i a) =
    iteratedFDeriv ℝ j (fun y => S.useAt T y (update v i
      ⟨(v i).1 + 1, P.deriv (v i).1 a (v i).2⟩)) x := by
  let v' := update v i (⟨(v i).1 + 1, P.deriv (v i).1 a (v i).2⟩ : S.Tag)
  let f := fun y => S.useAt T y v
  have he : Analysis.D (Points.direction i a) f =ᶠ[𝓝 x] fun y => S.useAt T y v' := by
    filter_upwards [(conf_open _).mem_nhds hx] with y hy
    have hz := (P.derivative_slot h hp hs hy i v (v i).2 a).symm
    rw [show update v i (⟨(v i).1, (v i).2⟩ : S.Tag) = v from update_eq_self ..] at hz
    exact hz
  have hw : ContDiffAt ℝ (↑(j+1 : ℕ)) f x :=
    (((S.class_smooth T hs v) _ hx).contDiffAt ((conf_open _).mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top)
  change fderiv ℝ (iteratedFDeriv ℝ j f) x (Points.direction i a) =
    iteratedFDeriv ℝ j (fun y => S.useAt T y v') x
  ext u
  calc
    _ = iteratedFDeriv ℝ (j+1) f x (Fin.cons (Points.direction i a) u) := by
      rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
    _ = iteratedFDeriv ℝ j (Analysis.D (Points.direction i a) f) x u := Analysis.cons_inner hw _ _
    _ = _ := by rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]

/-- Even before needing `respects`. Constants depend on S tags (by
applying the cap to T at S-representatives), not on positions or r. -/
theorem capped_tags (h : P.Derivatives T) (hs : T.Smooth) (hp : T.Symmetric) (ht : Bid.OneCap T)
    (v : Fin n → S.Tag) (j : ℕ) : ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x : Points n, spaced r x →
        ‖iteratedFDeriv ℝ j (fun y => S.useAt T y v) x‖ ≤ C * r⁻¹ ^ A := by
  induction j generalizing v with
  | zero =>
    obtain ⟨A,C,hC,H⟩ := ht n (fun i => (v i).1) fun i => S.representative _ (v i).2
    refine ⟨A,C,hC,fun r hr hr' x hx => ?_⟩
    rw [norm_iteratedFDeriv_zero]; exact H r hr hr' x hx
  | succ j IH =>
    let v' (b : Fin n × Axis) := update v b.1 (⟨(v b.1).1 + 1,
      P.deriv _ b.2 (v b.1).2⟩ : S.Tag)
    choose A C hC H using (fun b : Fin n × Axis => IH (v' b))
    refine ⟨Finset.univ.sup A, ∑ b, C b, Finset.sum_nonneg (fun b _ => hC b), fun r hr hr' x hx => ?_⟩
    rw [← norm_fderiv_iteratedFDeriv, Finset.sum_mul]
    refine (norm_le_direction_sum _).trans (Finset.sum_le_sum fun b hb => ?_)
    rw [jet_at_direction P h hs hp v (spaced_conf hr hx)]
    apply (H b r hr hr' x hx).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_inv₀ hr |>.mpr hr') (Finset.le_sup hb)) (hC b)

/-- This doesn't require equality of null spaces, just `T.respects S`.
Also, spectators in `Derivatives` may already have arbitrary weights,
so `Inclusions` needn't be used. -/
theorem answer : YM.Bid.B10 := by
  intro G L S T P hR hs hp _ h hT n d v j
  let q : Fin n → L.Token := fun i => ⟨d i,v i⟩
  let w : Fin n → S.Tag := S.classTokens ∘ q
  obtain ⟨A,C,hC,H⟩ := capped_tags P h hs hp.toSymmetric hT w j
  refine ⟨A,C,hC,fun r hr hr' x hx => ?_⟩
  have he : (fun y => T.value d y v) =ᶠ[𝓝 x] fun y => S.useAt T y w := by
    filter_upwards [(conf_open _).mem_nhds (spaced_conf hr hx)] with y hy
    exact (S.at_project T hp.toSymmetric hR hy q).symm
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  exact H r hr hr' x hx

end YM.Work.B10
