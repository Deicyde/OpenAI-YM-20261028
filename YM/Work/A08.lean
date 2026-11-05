import Mathlib.Analysis.Calculus.VectorField
import YM.Bid.Angular


/-!
# Actual Lie brackets after Ward propagation

Work on `conf` at finite arities and with the quotient fields of S. Rewrite
`Still` as a directional derivative equals minus a spin substitution sum. This
is a local identity (no contact assertions), but holds at *every* separated
configuration, so we can differentiate it. Both the action of the position
matrices as orbital derivatives, and that of the label matrices as substitutions
in a multilinear correlation, have a minus sign in their commutator.
This puts the Lie defect in the internal Ward kernel tested by `erases`.
No integration of the spin rows or determination of that kernel here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A08

open Set Function Filter Analysis Table Ward
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

/-- The simultaneous orbital velocity on all n positions. -/
private def velocity (u : Ortho.Skew) : Points n →L[ℝ] Points n := LinearMap.toContinuousLinearMap {
  toFun x := points fun i => M4.move u.val (x i)
  map_add' x y := by
    ext1 i
    exact map_add (Matrix.toEuclideanLin u.val) (x i) (y i)
  map_smul' c x := by
    ext1 i
    exact map_smul (Matrix.toEuclideanLin u.val) c (x i) }

private lemma velocity_apply (u : Ortho.Skew) (x : Points n) (i : Fin n) :
    velocity u x i = M4.move u.val (x i) := rfl

private lemma velocity_directions (u : Ortho.Skew) (x : Points n) :
    velocity u x = ∑ i, ∑ b : Axis, M4.move u.val (x i) b • Points.direction i b := by
  ext1 i
  rw [velocity_apply]
  simp [WithLp.ofLp_sum, Finset.sum_apply, Points.direction, Pi.single_apply, smul_ite]
  ext1 j
  simp [WithLp.ofLp_sum, Finset.sum_apply]

/-- As vector fields the bracket has the opposite sign to `Org.bracket`. -/
private lemma velocity_lieBracket (u v : Ortho.Skew) (x : Points n) :
    VectorField.lieBracket ℝ (velocity u) (velocity v) x = -velocity (Org.bracket u v) x := by
  have h (a b : M4) (z : E4) : M4.move (a - b) z = M4.move a z - M4.move b z := by
    simp only [M4.move, map_sub, LinearMap.sub_apply]
  rw [VectorField.lieBracket, (velocity u).fderiv, (velocity v).fderiv]
  ext1 i
  simp only [PiLp.sub_apply, PiLp.neg_apply, velocity_apply, Org.bracket, h,
    M4.move_mul, neg_sub]



private def orbital (u : Ortho.Skew) (f : Points n → ℂ) (x : Points n) := D (velocity u x) f x

private lemma orbital_comm {f : Points n → ℂ} (u v : Ortho.Skew) {x : Points n}
    (hf : ContDiffAt ℝ ∞ f x) :
    orbital u (orbital v f) x - orbital v (orbital u f) x = -orbital (Org.bracket u v) f x := by
  have h := VectorField.fderiv_apply_lieBracket hf (by simp; exact WithTop.coe_le_coe.mpr le_top)
    (velocity (n := n) v).differentiableAt (velocity (n := n) u).differentiableAt
  rw [velocity_lieBracket, map_neg] at h
  exact h.symm

/-- Spin substitution into the i'th tag (field at its existing cap). -/
private def turnAt (Y : SpinRows S) (u : Ortho.Skew) (q : Fin n → S.Tag) (i : Fin n) :=
  Function.update q i (turns Y u (q i))

private def spinSum (Y : SpinRows S) (u : Ortho.Skew) (q : Fin n → S.Tag) (x : Points n) :=
  ∑ i, disc (turnAt Y u q i) x

private lemma orbital_ward (H : S.Hierarchy) {V : DiffPlan S} (hV : V.Derivatives S)
    {Y : SpinRows S} (u : Ortho.Skew) (q : Fin n → S.Tag) {x : Points n} (hx : x ∈ conf n)
    (h : Still V Y x) : orbital u (disc q) x = -spinSum Y u q x := by
  have hi i b : fderiv ℝ (disc q) x (Points.direction i b) =
      disc (Function.update q i (rise V b (q i))) x := fromD V H hV hx i b q
  simp_rw [orbital, D, velocity_directions, map_sum, map_smul, hi]
  apply eq_neg_of_add_eq_zero_right
  simpa only [angular, Finset.sum_add_distrib, spinSum, turnAt] using h q u

/-!
Use the identity on a whole neighborhood when differentiating it. The spin
substitutions don't depend on the positions, so the orbital derivative can be
taken termwise and Ward used again, now for the substituted labels.
-/
private lemma orbit_twice (H : S.Hierarchy) {V : DiffPlan S} (hV : V.Derivatives S)
    {Y : SpinRows S} (stillAll : ∀ y : Points n, y ∈ conf n → Still V Y y)
    (u v : Ortho.Skew) (q : Fin n → S.Tag) {x : Points n} (hx : x ∈ conf n) :
    orbital u (orbital v (disc q)) x = ∑ i, spinSum Y u (turnAt Y v q i) x := by
  have he : orbital v (disc q) =ᶠ[𝓝 x] (fun y => -spinSum Y v q y) := by
    filter_upwards [(conf_open _).mem_nhds hx] with y hy
    exact orbital_ward H hV v q hy (stillAll y hy)
  change D (velocity u x) _ x = _
  rw [GermD _ he]
  calc
    _ = -(∑ i, orbital u (disc (turnAt Y v q i)) x) := by
      unfold D spinSum orbital
      have hd (i : Fin n) : DifferentiableAt ℝ (disc (turnAt Y v q i)) x :=
        (cont_disc H _ hx).differentiableAt (by simp)
      rw [fderiv_fun_neg, fderiv_fun_sum (fun i _ => hd i)]
      simp only [_root_.neg_apply, _root_.sum_apply, D]
    _ = _ := by simp_rw [orbital_ward H hV u _ hx (stillAll x hx), Finset.sum_neg_distrib, neg_neg]

/-- Match off-diagonal terms in opposite double spin substitutions; the
remaining terms were substituted at the same slot, first v then u on
one side, and first u then v on the other. -/
private lemma double_spin_sub (Y : SpinRows S) (u v : Ortho.Skew) (q : Fin n → S.Tag) (x : Points n) :
    (∑ i, spinSum Y u (turnAt Y v q i) x) - (∑ i, spinSum Y v (turnAt Y u q i) x) =
      ∑ i, (disc (update q i (turns Y u (turns Y v (q i)))) x -
        disc (update q i (turns Y v (turns Y u (q i)))) x) := by
  unfold spinSum
  -- switch indices in the second double sum
  conv_lhs => rhs; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp only [turnAt, update_self, update_idem]
  · intro j _ hji
    unfold turnAt
    rw [update_of_ne hji, update_of_ne hji.symm, update_comm hji.symm, sub_self]

/- The degree-d alternating family. -/
private def gapMap (Y : SpinRows S) (d : ℕ) (u v : Ortho.Skew) : S.Field d →ₗ[ℂ] S.Field d :=
  (Y d u).comp (Y d v) - (Y d v).comp (Y d u) - Y d (Org.bracket u v)

private def gapMapRight (Y : SpinRows S) (d : ℕ) (u : Ortho.Skew) :
    Ortho.Skew →ₗ[ℝ] (S.Field d →ₗ[ℂ] S.Field d) where
  toFun := gapMap Y d u
  map_add' v w := by
    have h : Org.bracket u (v + w) = Org.bracket u v + Org.bracket u w := by
      apply Subtype.ext
      change u.val * (v.val + w.val) - (v.val + w.val) * u.val = _ + _
      simp only [Org.bracket, mul_add, add_mul]
      abel
    simp only [gapMap, h, map_add, LinearMap.comp_add, LinearMap.add_comp]
    abel
  map_smul' c v := by
    have h : Org.bracket u (c • v) = c • Org.bracket u v := by
      apply Subtype.ext
      change u.val * (c • v.val) - (c • v.val) * u.val = c • (u.val * v.val - v.val * u.val)
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    change gapMap Y d u (c • v) = c • gapMap Y d u v
    simp only [gapMap, map_smul, h, LinearMap.comp_smul, LinearMap.smul_comp, smul_sub]

private def defect (Y : SpinRows S) (d : ℕ) : Org.Two S d where
  toFun := gapMapRight Y d
  map_add' u w := by
    ext1 v
    change gapMap Y d (u + w) v = gapMap Y d u v + gapMap Y d w v
    have h : Org.bracket (u + w) v = Org.bracket u v + Org.bracket w v := by
      apply Subtype.ext
      change (u.val + w.val) * v.val - v.val * (u.val + w.val) = _ + _
      simp only [Org.bracket, mul_add, add_mul]
      abel
    simp only [gapMap, h, map_add, LinearMap.comp_add, LinearMap.add_comp]
    abel
  map_smul' c u := by
    ext1 v
    change gapMap Y d (c • u) v = c • gapMap Y d u v
    have h : Org.bracket (c • u) v = c • Org.bracket u v := by
      apply Subtype.ext
      change (c • u.val) * v.val - v.val * (c • u.val) = c • (u.val * v.val - v.val * u.val)
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    simp only [gapMap, map_smul, h, LinearMap.comp_smul, LinearMap.smul_comp, smul_sub]

private lemma defect_apply (Y : SpinRows S) (d) (u v : Ortho.Skew) (w) :
    defect Y d u v w = Y d u (Y d v w) - Y d v (Y d u w) - Y d (Org.bracket u v) w := rfl

private lemma bracket_adj (g : Signed) (u v : Ortho.Skew) :
    Org.orients g (Org.bracket u v) = Org.bracket (Org.orients g u) (Org.orients g v) := by
  let A := g.ortho.val
  have h : star A * A = 1 := g.ortho.property.1
  have he (a b : M4) : (A * a * star A) * (A * b * star A) = A * (a * b) * star A := by
    simp only [mul_assoc]
    rw [← mul_assoc (star A) A, h, one_mul]
  apply Subtype.ext
  change A * (u.val * v.val - v.val * u.val) * star A =
    (A * u.val * star A) * (A * v.val * star A) - (A * v.val * star A) * (A * u.val * star A)
  rw [mul_sub, sub_mul, he, he]

private lemma defect_rise {H : S.RealSpin} {V : DiffPlan S} {Y : SpinRows S}
    (h : Bid.Hyper H V Y) {k d : ℕ} (hkd : k ≤ d) (u v : Ortho.Skew) (w : S.Field k) :
    defect Y d u v (V.rise hkd w) = V.rise hkd (defect Y k u v w) := by
  simp only [defect_apply, h.inter, map_sub]

private lemma defect_winds {H : S.RealSpin} {V : DiffPlan S} {Y : SpinRows S}
    (h : Bid.Hyper H V Y) (d : ℕ) : Org.Winds H V d (defect Y d) where
  polar g _ u v w := by simp only [defect_apply, map_sub, h.hex, bracket_adj]
  real u v w := by simp only [defect_apply, map_sub, h.real]
  unit u v := by simp [defect_apply, h.unity]
  alt u := by
    have hu : Org.bracket u u = 0 := by
      apply Subtype.ext
      change u.val * u.val - u.val * u.val = 0
      rw [sub_self]
    apply LinearMap.ext
    intro w
    simp [defect_apply, hu]
  rises k hk u v w := ⟨defect Y k u v w, (defect_rise h hk u v w).symm⟩

/-- Subtract the `Still` equation for `[u,v]` after commuting; these are
actual separated Ward identities of the degree-d defect. -/
private lemma defect_ward (H : S.Hierarchy) {V : DiffPlan S} (hV : V.Derivatives S)
    {Y : SpinRows S} (stillAll : ∀ y : Points n, y ∈ conf n → Still V Y y)
    {d : ℕ} {x : Points n} (hx : x ∈ conf n) (u v : Ortho.Skew) (w : Fin n → S.Field d) :
    ∑ i, disc (update (Climb.column w) i ⟨d, defect Y d u v (w i)⟩) x = 0 := by
  let q := Climb.column w
  have he := orbital_comm u v (cont_disc H q hx)
  rw [orbit_twice H hV stillAll u v q hx, orbit_twice H hV stillAll v u q hx,
    orbital_ward H hV _ q hx (stillAll x hx), neg_neg, double_spin_sub] at he
  have hi (i : Fin n) : disc (update q i ⟨d, defect Y d u v (w i)⟩) x =
      (disc (update q i (turns Y u (turns Y v (q i)))) x -
        disc (update q i (turns Y v (turns Y u (q i)))) x) -
      disc (turnAt Y (Org.bracket u v) q i) x := by
    unfold turnAt turns
    simp only [defect_apply, q, Climb.column, ← takes, map_sub]
    rfl
  change (∑ i, disc (update q i ⟨d, defect Y d u v (w i)⟩) x) = 0
  -- Split off just the row for [u,v].
  calc
    _ = (∑ i, ((disc (update q i (turns Y u (turns Y v (q i)))) x -
        disc (update q i (turns Y v (turns Y u (q i)))) x) -
      disc (turnAt Y (Org.bracket u v) q i) x)) := Finset.sum_congr rfl fun i _ => hi i
    _ = _ := by rw [Finset.sum_sub_distrib]; exact sub_eq_zero.mpr he

theorem answer : YM.Bid.A08 := by
  intro G L S H V hincl hV _ Y hY h her
  obtain ⟨N, hN⟩ := her
  have hlarge (d : ℕ) (hd : N ≤ d) : defect Y d = 0 :=
    hN d hd (defect Y d) (defect_winds h d)
      fun m _ hx u v w => defect_ward H hV (hY m) hx u v w
  intro d u v
  rw [← sub_eq_zero]
  change defect Y d u v = 0
  apply LinearMap.ext
  intro w
  -- Inject this cap into one of the large caps.
  have hd : d ≤ max d N := le_max_left d N
  apply V.inject H.laws.toSymmetric hincl hd
  rw [← defect_rise h hd u v w, hlarge _ (le_max_right d N)]
  simp

end YM.Work.A08
