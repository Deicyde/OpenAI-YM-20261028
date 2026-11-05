import YM.Analysis.Polydisc
import YM.Org.Input


/-!
# Differentiate `Rotation.Oriented` (position derivative form)

This uses the smoothness on Conf of T. Work at each slot in its own finite-dimensional
quotient (of S), as in `useAt`. In the application `T.respects S`. We don't need to choose
new representatives. To differentiate, move one side in positions, the other in labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C07
open Table Analysis Function Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {L : Register G} {S T : Table L}

private lemma parameter_zero (Ω : Ortho.Skew) : Ortho.oneParameter Ω 0 = 1 := by
  apply Subtype.ext
  change NormedSpace.exp ((0 : ℝ) • (Ω.val : M4)) = 1
  rw [zero_smul, NormedSpace.exp_zero]

private lemma parameter_opposite (Ω : Ortho.Skew) (t : ℝ) :
    Ortho.oneParameter Ω t * Ortho.oneParameter Ω (-t) = 1 := by
  apply Subtype.ext
  change NormedSpace.exp (t • (Ω.val : M4)) * NormedSpace.exp ((-t) • (Ω.val : M4)) = 1
  letI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _
  have hop (B : M4) : NormedSpace.exp (B + -B) = NormedSpace.exp B * NormedSpace.exp (-B) :=
    NormedSpace.exp_add_of_commute (Commute.refl B).neg_right
  rw [neg_smul, ← hop, add_neg_cancel, NormedSpace.exp_zero]

private def actionOnTuple {n : ℕ} (p : Points n) : M4 →L[ℝ] Points n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => points fun i => M4.move A (p i)
      map_add' := fun A B => PiLp.ext fun i => by
        change Matrix.toEuclideanLin (A+B) (p i) =
          Matrix.toEuclideanLin A (p i) + Matrix.toEuclideanLin B (p i)
        rw [map_add]; rfl
      map_smul' := fun c A => PiLp.ext fun i => by
        change Matrix.toEuclideanLin (c • A) (p i) = c • Matrix.toEuclideanLin A (p i)
        rw [map_smul]; rfl }

private lemma turnsTuple {n : ℕ} (x : Points n) (Ω : Ortho.Skew) :
    HasDerivAt (fun t : ℝ => Points.move (Ortho.oneParameter Ω t) x)
      (points fun i => M4.move Ω.val (x i)) 0 := by
  have hA : HasDerivAt (fun t => NormedSpace.exp (t • Ω.val)) Ω.val (0 : ℝ) := by
    simpa using! (hasDerivAt_exp_smul_const Ω.val (0 : ℝ))
  exact (actionOnTuple x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA

/-- Version of the finite basis expansion with constant rectangle used for continuity. -/
lemma continuous_cap_multilinear {n : ℕ} (d : Caps n)
    (P : MultilinearMap ℂ (fun i => S.Field (d i)) ℂ) : Continuous P := by
  classical
  let E (i : Fin n) := Module.finBasis ℂ (S.Field (d i))
  let c (i : Fin n) := LinearEquiv.toContinuousLinearEquiv (E i).equivFun
  have hw (w : ∀ i : Fin n, S.Field (d i)) :
      P w = ∑ v : ((i : Fin n) → Fin (Module.finrank ℂ (S.Field (d i)))),
        (∏ i, c i (w i) (v i)) • P (fun i => E i (v i)) := by
    rw [Multilabel.expansion E P w]
    change (∑ e ∈ Fintype.piFinset _, ((∏ i, (E i).repr (w i) (e i)) • (P _))) =
      ∑ e : ((i : Fin n) → Fin (Module.finrank ℂ (S.Field (d i)))),
        (∏ i, (E i).repr (w i) (e i)) • P (fun i => E i (e i))
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    obtain ⟨j,hj⟩ : ∃ j, (E j).repr (w j) (a j) = 0 := by simpa using ha
    have hz : ∏ i : Fin n, (E i).repr (w i) (a i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [hz, zero_smul]
  rw [funext hw]
  refine continuous_finsetSum _ fun v _ => ?_
  have h : Continuous fun w : (∀ i : Fin n, S.Field (d i)) => ∏ i, c i (w i) (v i) := by
    refine continuous_finsetProd _ fun i _ => ?_
    exact (continuous_apply (v i)).comp ((c i).continuous.comp (continuous_apply i))
  exact h.smul (continuous_const (y := P (fun i => E i (v i))))

private lemma use_negative {R : Rotation S} {V : DiffPlan S} {h : S.RealSpin}
    (hR : R.Laws V h) (Ω : Ortho.Skew) {n : ℕ} (x : Points n) (v : Fin n → S.Tag) :
    HasDerivAt (fun t : ℝ => S.useAt T x (R.label (Ortho.oneParameter Ω (-t)) ∘ v))
      (-(∑ i, S.classMoment T (fun j => (v j).1) x
          (update (fun j => (v j).2) i (R.lie (v i).1 Ω (v i).2)))) 0 := by
  let d (i : Fin n) : ℕ := (v i).1
  let w (i : Fin n) : S.Field (d i) := (v i).2
  let U := S.classMoment T d x
  let f (t : ℝ) (i : Fin n) := R.act (d i) (Ortho.oneParameter Ω (-t)) (w i)
  let L' (i : Fin n) := R.lie (d i) Ω (w i)
  have hf : HasDerivAt f (-L') 0 := by
    rw [hasDerivAt_pi]
    intro i
    simpa [L', f, Function.comp_def] using
      ((hR.infinitesimal (d i) Ω (w i)).scomp_of_eq (0 : ℝ) (hasDerivAt_id' (0 : ℝ)).neg
        (by simp))
  let M : ContinuousMultilinearMap ℂ (fun i => S.Field (d i)) ℂ :=
    ⟨U, continuous_cap_multilinear d U⟩
  let A := M.restrictScalars ℝ
  have he : f 0 = w := funext fun i => by dsimp only [f]; rw [neg_zero, parameter_zero, hR.fixes]
  have hh := (A.hasFDerivAt (f 0)).comp_hasDerivAt 0 hf
  rw [he, ContinuousMultilinearMap.linearDeriv_apply] at hh
  change HasDerivAt (fun t => U (f t)) (∑ i, U (update w i (-(L' i)))) 0 at hh
  simp_rw [MultilinearMap.map_update_neg, Finset.sum_neg_distrib] at hh
  exact hh

lemma oriented_differential {R : Rotation S} {V : DiffPlan S} {h : S.RealSpin}
    (hO : R.Oriented T) (hR : R.Laws V h) (hS : T.Smooth)
    (Ω : Ortho.Skew) {n : ℕ} {x : Points n} (hx : x ∈ conf n) (v : Fin n → S.Tag) :
    D (points (fun i => M4.move Ω.val (x i))) (fun y => S.useAt T y v) x =
      -(∑ i, S.classMoment T (fun j => (v j).1) x
          (update (fun j => (v j).2) i (R.lie (v i).1 Ω (v i).2))) := by
  let Q (t : ℝ) := Ortho.oneParameter Ω t
  have hQ : x = Points.move (Q 0) x := PiLp.ext fun i => by simp [Q, parameter_zero]
  have ht : DifferentiableAt ℝ (fun y => S.useAt T y v) x :=
    ((S.class_smooth T hS v x hx).contDiffAt ((conf_open _).mem_nhds hx)).differentiableAt (by simp)
  have hp := (ht.hasFDerivAt.comp_hasDerivAt_of_eq 0 (turnsTuple x Ω) hQ)
  have he (t : ℝ) : S.useAt T (Points.move (Q t) x) v =
      S.useAt T x (R.label (Q (-t)) ∘ v) := by
    have hEq : R.label (Q t) ∘ (R.label (Q (-t)) ∘ v) = v := by
      funext j
      change Sigma.mk _ (R.act (v j).1 (Q t) (R.act (v j).1 (Q (-t)) (v j).2)) = _
      rw [← hR.group (v j).1 (Q t) (Q (-t)), parameter_opposite Ω t, hR.fixes]
    have ht := hO n (R.label (Q (-t)) ∘ v) x hx (Q t)
    rwa [hEq] at ht
  change HasDerivAt (fun t => S.useAt T (Points.move (Q t) x) v) _ _ at hp
  simp_rw [he] at hp
  exact hp.unique (use_negative hR Ω x v)

end YM.Work.C07
