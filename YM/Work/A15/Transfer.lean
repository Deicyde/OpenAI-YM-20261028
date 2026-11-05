import YM.Bid.Angular
import YM.Work.A15.Shell

/-!
# Each rotated stress satisfies the two flux laws

Use actual covariance along `Ortho.move`, not a formal identity of generators
alone. For `K`, lower the calculation to that for the unrotated stress with all
the points and tags pulled back by `K⁻¹`. Constant vector fields pull back as
vectors; centered angular vector fields pull back to centered angular vector
fields at the new center, hence the need for the adjoint transformation law.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A15

open Set Function Filter MeasureTheory Analysis Table
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

/-- Use the given shell after the change of coordinates. -/
theorem window_pull (K : Ortho) {x : Points (n+1)} {χ : E4 → ℝ} (w : Window x χ) :
    Window (Points.move K⁻¹ x) (χ ∘ Ortho.move K) := by
  obtain ⟨hc,hk,h0,he⟩ := w
  let f := (Ortho.motion K).toHomeomorph
  have h (i : Fin (n+1)) : f (Points.move K⁻¹ x i) = x i := Ortho.move_inv ..
  refine ⟨hc.comp ((Ortho.motion K).toContinuousLinearEquiv.toContinuousLinearMap.contDiff),
    hk.comp_homeomorph f, h0.comp_tendsto ?_, fun i => ?_⟩
  · have ht : Tendsto f (𝓝 (Points.move K⁻¹ x 0)) (𝓝 (x 0)) := by
      rw [← h 0]
      exact f.continuous.continuousAt
    exact ht
  change Points.move K⁻¹ x i.succ ∉ tsupport (χ ∘ f)
  rw [tsupport_comp_eq_preimage χ f]
  simpa only [mem_preimage, h] using he i

lemma move_basis_sum (K : Ortho) (i : Axis) :
    Ortho.move K (basis i) = ∑ j : Axis, K.val j i • basis j := by
  ext1 j
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp [Ortho.move]

lemma gradVec_pull (K : Ortho) {χ : E4 → ℝ} (hc : ContDiff ℝ ∞ χ) (y : E4) :
    gradVec (χ ∘ Ortho.move K) y = Ortho.move K⁻¹ (gradVec χ (Ortho.move K y)) := by
  ext1 i
  let t := (Ortho.motion K).toContinuousLinearEquiv.toContinuousLinearMap
  change (fderiv ℝ (χ ∘ t) y) (basis i) = _
  rw [fderiv_comp y ((hc.differentiable (by simp)) _) t.differentiableAt, t.fderiv,
    ContinuousLinearMap.comp_apply]
  change fderiv ℝ χ (Ortho.move K y) (Ortho.move K (basis i)) = _
  rw [move_inv_apply, move_basis_sum, map_sum]
  simp only [map_smul, smul_eq_mul, gradVec_apply, Analysis.D]

lemma pull_centered (K : Ortho) (g : Ortho.Skew) (z y : E4) :
    Ortho.move K⁻¹ (M4.move g.val (Ortho.move K y - z)) =
      M4.move ((K⁻¹).val * g.val * star (K⁻¹).val) (y - Ortho.move K⁻¹ z) := by
  rw [show star (K⁻¹).val = K.val from star_star _, M4.move_mul, M4.move_mul]
  change _ = Ortho.move K⁻¹ (M4.move g.val (Ortho.motion K (y - (Ortho.move K⁻¹ z))))
  rw [map_sub, Ortho.motion_at, Ortho.motion_at, Ortho.move_inv]

lemma label_cons (X : Rotation S) (K : Ortho) (q : Fin n → S.Tag)
    (d : ℕ) (B : S.Field d) :
    X.label K ∘ Fin.cons (α := fun _ => S.Tag) ⟨d,B⟩ q =
    Fin.cons ⟨d,X.act d K B⟩ (X.label K ∘ q) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Function.comp_apply, Fin.cons_zero, Fin.cons_zero]; rfl
  · rw [Function.comp_apply, Fin.cons_succ, Fin.cons_succ, Function.comp_apply]

lemma oriented_cons {X : Rotation S} (p : X.Oriented S) (K : Ortho)
    {x : Points (n+1)} (hx : x ∈ conf _) (q : Fin n → S.Tag) (d : ℕ) (B : S.Field d) :
    S.useAt S (Points.move K x) (Fin.cons ⟨d,X.act d K B⟩ (X.label K ∘ q)) =
      S.useAt S x (Fin.cons ⟨d,B⟩ q) := by
  rw [← label_cons]
  exact p _ _ _ hx K

/-- Change of variables at the shell. The formal equality of integrals uses
measure preservation and ae congruence (use covariance only off collisions);
in our applications W is continuous and we have the hierarchy’s smoothness, with shell
integrability as in `Shell`. -/
theorem pull_flux {V : DiffPlan S} {H : S.RealSpin} {X : Rotation S}
    (h : X.Laws V H) (p : X.Oriented S) (K : Ortho) {x : Points (n+1)} (hx : x ∈ conf _)
    {χ : E4 → ℝ} (w : Window x χ) (q : Fin (n+1) → S.Tag) (W : E4 → E4) (J : S.Stress) :
    fluxCore x q χ W (rotateStress X K J) = fluxCore (Points.move K⁻¹ x) (X.label K⁻¹ ∘ q)
      (χ ∘ Ortho.move K) (fun y => Ortho.move K⁻¹ (W (Ortho.move K y))) J := by
  let x' := Points.move K⁻¹ x
  have hf (z : S.Tag) : X.label K (X.label K⁻¹ z) = z := by
    rcases z with ⟨d,v⟩
    change Sigma.mk d (X.act d K (X.act d K⁻¹ v)) = _
    rw [← h.group, mul_inv_cancel, h.fixes]
  let f := Ortho.motion K
  unfold fluxCore
  apply congrArg Neg.neg
  rw [← MeasurePreserving.integral_comp f.measurePreserving f.toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [(Set.finite_range x'.ofLp).countable.ae_notMem (volume : Measure E4)] with y hy
  have hxy : Points.cons y x' ∈ conf _ :=
    Fin.cons_injective_of_injective hy (show Injective x'.ofLp from Points.move_in K⁻¹ hx)
  have he : Points.move K (Points.cons y x') = Points.cons (f y) x := by
    ext1 i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Points.cons, f]
    · simp [Points.cons, x']
  change front (Points.cons (f y) x) q 4
    (contractStress (gradVec χ (Ortho.move K y)) (W (Ortho.move K y)) (rotateStress X K J)) = _
  rw [contract_rotate, front_apply, front_apply, gradVec_pull K w.1]
  have orient := oriented_cons p K hxy (X.label K⁻¹ ∘ q) 4
    (contractStress (Ortho.move K⁻¹ (gradVec χ (Ortho.move K y)))
      (Ortho.move K⁻¹ (W (Ortho.move K y))) J)
  rw [show X.label K ∘ X.label K⁻¹ ∘ q = q from funext fun i => hf _, he] at orient
  exact orient

private def pullSkew (K : Ortho) (g : Ortho.Skew) : Ortho.Skew :=
  ⟨(K⁻¹).val * g.val * star (K⁻¹).val, by
    change star _ = -_
    have hg : star g.val = -g.val := g.property
    simp only [star_mul, star_star, hg, neg_mul, ← mul_assoc, mul_neg]⟩

/-- The compensated rotations of any stress already giving the D and lie
fluxes give those *same* fluxes. Use A10 on this actual `X`, including the
elements of O outside proper rotations. -/
theorem rotate_flux (A : Bid.A10) {V : DiffPlan S} (H : S.Hierarchy) {X : Rotation S}
    (h : X.Laws V H.spin) (p : X.Oriented S) (K : Ortho) (J : S.Stress)
    (c : StressLaws S J V.deriv X.lie) : StressLaws S (rotateStress X K J) V.deriv X.lie where
  translation := by
    intro n x hx q χ w b d B
    let x' := Points.move K⁻¹ x
    let q' := X.label K⁻¹ ∘ q
    let B' := X.act d K⁻¹ B
    have hx' : x' ∈ conf (n+1) := Points.move_in K⁻¹ hx
    have w' := window_pull K w
    calc
      _ = fluxCore x (Fin.cons ⟨d,B⟩ q) χ (fun _ => basis b) (rotateStress X K J) :=
        (fluxCore_basis hx w H.smooth q B (rotateStress X K J) b).symm
      _ = fluxCore x' (Fin.cons ⟨d,B'⟩ q') (χ ∘ Ortho.move K)
          (fun _ => Ortho.move K⁻¹ (basis b)) J := by
        rw [pull_flux h p K hx w, label_cons]
      _ = ∑ j : Axis, ((Ortho.move K⁻¹ (basis b) j : ℝ) : ℂ) •
          S.useAt S x' (Fin.cons ⟨d+1,V.deriv d j B'⟩ q') := by
        rw [fluxCore_const hx' w' H.smooth]
        simp_rw [c.translation hx' q' w']
      _ = front x' q' (d+1) (X.act (d+1) K⁻¹ (V.deriv d b B)) := by
        rw [h.vector]
        simp only [map_sum, map_smul, front_apply, B', Ortho.move, M4.move_basis]
      _ = _ := by
        rw [front_apply]; exact oriented_cons p K⁻¹ hx q (d+1) (V.deriv d b B)
  rotation := by
    intro n x hx q χ w g d B
    let x' := Points.move K⁻¹ x
    let q' := X.label K⁻¹ ∘ q
    let B' := X.act d K⁻¹ B
    have hx' : x' ∈ conf (n+1) := Points.move_in K⁻¹ hx
    have w' := window_pull K w
    let g' := pullSkew K g
    have ad : X.act d K⁻¹ (X.lie d g B) = X.lie d g' B' :=
      (A H.spin X ⟨h.spin,h.fixes,h.group,h.signed,h.real,h.infinitesimal⟩).2 d K⁻¹ g B
    calc
      _ = fluxCore x (Fin.cons ⟨d,B⟩ q) χ (fun y => M4.move g.val (y-x 0)) (rotateStress X K J) :=
        (fluxCore_angular hx w H.smooth q B (rotateStress X K J) g).symm
      _ = fluxCore x' (Fin.cons ⟨d,B'⟩ q') (χ ∘ Ortho.move K)
          (fun y => M4.move g'.val (y-x' 0)) J := by
        rw [pull_flux h p K hx w, label_cons]
        simp_rw [pull_centered]; rfl
      _ = S.useAt S x' (Fin.cons ⟨d,X.lie d g' B'⟩ q') := by
        rw [fluxCore_angular hx' w' H.smooth, c.rotation hx' q' w']
      _ = _ := by rw [← ad]; exact oriented_cons p K⁻¹ hx q d (X.lie d g B)

end YM.Work.A15
