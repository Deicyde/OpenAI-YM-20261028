import YM.RG.PathActions


/-!
# Ambient path polynomials

Independent complex matrices for a link and its inverse. They will be evaluated
on the actual `G.mat` pairs in the real problem. Extend at arbitrary physical
configurations (for the ticket we only need analyticity near identity).
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.F02

open Lattice Wilson RG Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}

/-- Sup, product max, and Frobenius. -/
abbrev Ambient (G : Gauge) (n : Side) := Edge (Site n) → G.Mat × G.Mat

def physical (U : Config G n) : Ambient G n :=
  fun i => (G.mat (U i), G.mat (U i)⁻¹)

/-- Negative branch uses an independent variable, *not* the adjoint at
complex values. -/
def letter (M : Ambient G n) (d : Step) (x : Site n) :=
  if d.neg then (M (d.used x)).2 else (M (d.used x)).1

def stringMat (M : Ambient G n) (w : Walk) (x : Site n) : G.Mat :=
  (w.foldr (fun d (T : Site n → G.Mat) y => letter M d y * T (y + d.vec)) (fun _ => 1)) x

lemma stringMat_cons (M : Ambient G n) (d : Step) (w : Walk) (x : Site n) :
    stringMat M (d :: w) x = letter M d x * stringMat M w (x + d.vec) := rfl

lemma letter_physical (U : Config G n) (d : Step) (x : Site n) :
    letter (physical U) d x = G.mat (d.read U x) := by
  unfold letter Step.read
  split <;> rfl

lemma stringMat_physical (U : Config G n) (w : Walk) (x : Site n) :
    stringMat (physical U) w x = G.mat (travel U x w) := by
  induction w generalizing x with
  | nil => rfl
  | cons d w ih =>
    rw [stringMat_cons, travel, G.mat_mul, letter_physical, ih]

lemma stringMat_contDiff (w : Walk) (x : Site n) :
    ContDiff ℂ ω fun M : Ambient G n => stringMat M w x := by
  induction w generalizing x with
  | nil => exact contDiff_const
  | cons d w ih =>
    simp only [stringMat_cons]
    refine ContDiff.mul ?_ (ih _)
    unfold letter
    split <;> first
      | exact (contDiff_apply ℂ _ _).fst
      | exact (contDiff_apply ℂ _ _).snd

lemma stringMat_bound (U : Config G n) {R : ℝ} (hR : 0 ≤ R) (M : Ambient G n)
    (hm : M ∈ closedBall (physical U) R) (w : Walk) (x : Site n) :
    ‖stringMat M w x‖ ≤ (1 + R)^w.length * ‖(1 : G.Mat)‖ := by
  induction w generalizing x with
  | nil => simp [stringMat]
  | cons d w ih =>
    have hj : ‖(M - physical U) (d.used x)‖ ≤ R := by
      apply (norm_le_pi_norm _ _).trans
      rwa [mem_closedBall, dist_eq_norm] at hm
    have he : ‖letter M d x - letter (physical U) d x‖ ≤ R := by
      unfold letter
      rw [Prod.norm_def, max_le_iff] at hj
      split
      · exact hj.2
      · exact hj.1
    let T := stringMat M w (x + d.vec)
    let Y := letter (physical U) d x
    let D := letter M d x - Y
    have hk : ‖Y * T‖ = ‖T‖ := by
      unfold Y
      rw [letter_physical]
      exact Gauge.mul_frob_eq _ _ (G.mat_star_mul _)
    calc
      _ = ‖Y * T + D * T‖ := by
        rw [stringMat_cons]
        dsimp only [Y, D, T]
        rw [sub_mul, add_sub_cancel]
      _ ≤ ‖Y * T‖ + ‖D * T‖ := norm_add_le _ _
      _ ≤ ‖T‖ + R * ‖T‖ := by
        rw [hk]
        exact add_le_add_right ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right he (norm_nonneg _))) _
      _ = (1 + R) * ‖T‖ := by ring
      _ ≤ (1 + R) * ((1 + R)^w.length * ‖(1 : G.Mat)‖) :=
        mul_le_mul_of_nonneg_left (ih _) (by positivity)
      _ = _ := by rw [List.length_cons, pow_succ']; ring

/-- Package a slot's full cover walk (transport there, go around the
plaquette, transport back). We will still use its true length on the torus. -/
def slotWalk (a : Slot) : Walk :=
  (a.walk ++ square a.plaq.val.1 a.plaq.val.2) ++ Lattice.reverse a.walk

lemma atSite_curvature (a : Slot) (U : Config G n) (x : Site n) :
    a.atSite U x = G.curvature (travel U x (slotWalk a)) := by
  have ht : travel (expandAt x U) 0 (slotWalk a) = travel U x (slotWalk a) := by
    simp [travel_at]
  rw [Slot.atSite, Slot.eval, ← G.curvature_conjugate, ← ht]
  congr 1
  rw [slotWalk, travel_append, travel_append, stop_append, square_stop,
    travel_reverse]
  rfl

/-- The amount by which we permit each letter to deviate in the Frobenius norm.
A loop for a transported slot can have up to twice the length budget of the slot. -/
def radius (σ : ℝ) := Real.exp (σ / 2) - 1

lemma radius_pos {σ : ℝ} (hs : 0 < σ) : 0 < radius σ :=
  sub_pos.mpr <| by simpa only [Real.exp_zero] using
    Real.exp_strictMono (half_pos hs)

/-- Sup norm on the complex extension of the (finite-dimensional) color space.
On the real side we of course still use the original `G.Color`. -/
abbrev CColor (G : Gauge) := G.ColorIndex → ℂ

def colorUp (G : Gauge) : G.Color →L[ℝ] CColor G :=
  ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ => ℝ) i)

def colorReal (G : Gauge) : CColor G →L[ℝ] G.Color :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Complex.reCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) i))

lemma colorUp_apply (c : G.Color) (i : G.ColorIndex) :
    colorUp G c i = (c i : ℂ) := rfl

lemma colorReal_up (c : G.Color) :
    colorReal G (colorUp G c) = c := rfl

private def skewCoord (G : Gauge) (i : G.ColorIndex) : StrongDual ℝ G.Mat :=
  ((PiLp.proj (𝕜 := ℝ) 2 (fun _ => ℝ) i).comp G.projectColor.toContinuousLinearMap).comp
    ((1/2 : ℝ) • (ContinuousLinearMap.id ℝ G.Mat -
       (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).toContinuousLinearMap))

private lemma skewCoord_apply (M : G.Mat) (i : G.ColorIndex) :
    skewCoord G i M = G.projectColor ((1/2 : ℝ) • (M - star M)) i := rfl

/-- Extend the real projection *on skew matrices* to a complex linear map on matrices. -/
def colorProject (G : Gauge) : G.Mat →L[ℂ] CColor G :=
  ContinuousLinearMap.pi fun i => StrongDual.extendRCLike (skewCoord G i)

lemma colorProject_skew (M : G.Mat) (hm : star M = -M) :
    colorProject G M = colorUp G (G.projectColor M) := by
  have he : (1/2 : ℝ) • (M - star M) = M := by
    rw [hm, sub_neg_eq_add, ← two_smul ℝ, smul_smul, div_mul_cancel₀ _ (two_ne_zero), one_smul]
  have hp : star (Complex.I • M) = Complex.I • M := by
    rw [star_smul, hm]; simp
  funext i
  rw [colorUp_apply]
  change (StrongDual.extendRCLike (skewCoord G i) M : ℂ) = _
  rw [StrongDual.extendRCLike_apply]
  change (skewCoord G i M : ℂ) - Complex.I * (skewCoord G i (Complex.I • M) : ℂ) = _
  rw [skewCoord_apply, skewCoord_apply, hp, he]
  simp

def slotMatrix (a : Slot) (x : Site n) (M : Ambient G n) :=
  let w := slotWalk a
  (1/2 : ℝ) • (stringMat M w x -
    stringMat M (Lattice.reverse w) (stop x w))

def slotExt (a : Slot) (x : Site n) (M : Ambient G n) :=
  colorProject G (slotMatrix a x M)

lemma slotExt_physical (a : Slot) (x : Site n) (U : Config G n) :
    slotExt a x (physical U) = colorUp G (a.atSite U x) := by
  unfold slotExt slotMatrix
  simp only [stringMat_physical, travel_reverse]
  rw [atSite_curvature, colorProject_skew]
  · rfl
  · simp only [star_smul, star_trivial, G.mat_inv, star_sub, star_star, ← smul_neg, neg_sub]

lemma slotExt_contDiff (a : Slot) (x : Site n) :
    ContDiff ℂ ω (slotExt (G := G) a x) := by
  refine (colorProject G).contDiff.comp ?_
  unfold slotMatrix
  exact ((stringMat_contDiff _ _).sub (stringMat_contDiff _ _)).const_smul (1/2 : ℝ)

-- Express the norm via a helper on normed spaces so it uses the indicated normed
-- space structures (the unbundled topology on matrices is used also with other norms).
private def complexOpNorm {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℂ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℂ Y] (f : X →L[ℂ] Y) : ℝ :=
  ‖f‖

def slotConst (G : Gauge) :=
  complexOpNorm (X := G.Mat) (Y := CColor G) (colorProject G) * ‖(1 : G.Mat)‖

lemma slotExt_bound (U : Config G n) {σ : ℝ} (hs : 0 < σ) (M : Ambient G n)
    (hm : M ∈ closedBall (physical U) (radius σ)) (a : Slot) (x : Site n) :
    ‖slotExt a x M‖ ≤ slotConst G * Real.exp (σ * a.length) := by
  let B := Real.exp (σ * a.length) * ‖(1 : G.Mat)‖
  have hw (w : Walk) (y : Site n) (hh : w.length ≤ 2 * a.length) :
      ‖stringMat M w y‖ ≤ B := by
    apply (stringMat_bound U (radius_pos hs).le M hm w y).trans
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [radius, add_sub_cancel, ← Real.exp_nat_mul]
    have he : (w.length : ℝ) ≤ 2 * a.length := by exact_mod_cast hh
    apply Real.exp_monotone
    nlinarith
  have ht : (slotWalk a).length ≤ 2 * a.length := by
    simp only [slotWalk, List.length_append, Lattice.reverse, List.length_map, List.length_reverse]
    change a.walk.length + 4 + a.walk.length ≤ 2 * (a.walk.length + 4)
    omega
  have h1 := hw _ x ht
  have h2 := hw (Lattice.reverse (slotWalk a)) (stop x (slotWalk a))
    (by simpa only [Lattice.reverse, List.length_map, List.length_reverse] using ht)
  have hz : ‖slotMatrix a x M‖ ≤ B := calc
    _ = (1/2 : ℝ) * ‖stringMat M (slotWalk a) x -
        stringMat M (Lattice.reverse (slotWalk a)) (stop x (slotWalk a))‖ := by
      unfold slotMatrix
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
    _ ≤ _ := by
      have hp := norm_sub_le (stringMat M (slotWalk a) x)
        (stringMat M (Lattice.reverse (slotWalk a)) (stop x (slotWalk a)))
      linarith
  exact ((colorProject G).le_opNorm _).trans ((mul_le_mul_of_nonneg_left hz
    (norm_nonneg _)).trans_eq (by unfold B slotConst complexOpNorm; ring))

variable {k : ℕ}

def atomExt (a : Atom G k) (x : Site n) (M : Ambient G n) : ℂ :=
  ∑ b, (a.coeff b : ℂ) * ∏ i, slotExt (a.leg i) x M (b i)

lemma atomExt_contDiff (a : Atom G k) (x : Site n) :
    ContDiff ℂ ω (atomExt a x) := by
  unfold atomExt
  apply ContDiff.sum
  intro b _
  refine contDiff_const.mul ?_
  apply contDiff_prod
  exact fun i _ => (contDiff_apply ℂ _ _).comp (slotExt_contDiff (a.leg i) x)

lemma atomExt_physical (a : Atom G k) (U : Config G n) (x : Site n) :
    atomExt a x (physical U) = (a.unmasked U x : ℂ) := by
  simp only [atomExt, slotExt_physical, colorUp_apply, Atom.unmasked, Atom.poly,
    Complex.ofReal_sum, Complex.ofReal_prod, Complex.ofReal_mul]

lemma atomExt_bound (a : Atom G k) (U : Config G n) {σ : ℝ} (hs : 0 < σ) (M : Ambient G n)
    (hm : M ∈ closedBall (physical U) (radius σ)) (x : Site n) :
    ‖atomExt a x M‖ ≤ a.budget σ * (slotConst G)^k := by
  have he (i : Fin k) (j : G.ColorIndex) :
      ‖slotExt (a.leg i) x M j‖ ≤ slotConst G * Real.exp (σ * (a.leg i).length) :=
    (norm_le_pi_norm _ j).trans (slotExt_bound U hs M hm (a.leg i) x)
  unfold atomExt Atom.budget Atom.magnitude
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_prod]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ((Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun i _ => he i (b i))).trans_eq ?_) (abs_nonneg _)
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Atom.length, Nat.cast_sum, Finset.mul_sum]
  simp [mul_comm]

end YM.Work.F02
