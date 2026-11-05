import YM.Bid.Station
import YM.Work.F02.Path
import YM.Work.F02.Series



/-!
# F02 — analytic uncut main term

Analytic along analytic matrix inputs. Use the ambient extensions of the
true transported slots (see `YM.Work.F02.Path`) and the summability down the
rows from `PathData.Bounds`. We estimate on a full complex ball and then
restrict scalars. All the extensional equalities back at actual link fields
are of the unmasked, uncut functions.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.F02

open Lattice Wilson RG Precision Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {n : Side} {σ C Λ : ℝ} {c : Clip} {W : PathData G}

def rowExt (W : PathData G) (p : Face (Per n)) (i : ℕ) (M : Ambient G n) :=
  (W.row p.2 i).1 • slotExt (W.row p.2 i).2 p.1 M

lemma rowExt_series (h : W.Bounds c σ C Λ) (p : Face (Per n)) (U : Config G n) :
    AnalyticAt ℂ (fun M => ∑' i, rowExt W p i M) (physical U) := by
  refine analytic_series _ (radius_pos h.width) ?_ ((h.rows p.2).2.1.mul_right (slotConst G)) ?_
  · intro i
    have hd : ContDiff ℂ ω (rowExt W p i) :=
      (slotExt_contDiff (W.row p.2 i).2 p.1).const_smul (W.row p.2 i).1
    exact hd.differentiable (by simp)
  intro i M hM
  unfold rowExt
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (slotExt_bound U h.width M (ball_subset_closedBall hM)
    (W.row p.2 i).2 p.1) (abs_nonneg _)).trans_eq (by ring)

lemma rowExt_real (h : W.Bounds c σ C Λ) (p : Face (Per n)) (U : Config G n) :
    (∑' i, rowExt W p i (physical U)) = colorUp G (W.ell U p) := by
  unfold PathData.ell
  rw [(colorUp G).map_tsum ((W.ell_dominated h p).summable U)]
  apply tsum_congr
  intro i
  rw [rowExt, PathData.ellTerms, slotExt_physical, map_smul]

lemma atomExt_series {k : ℕ} {F : ℕ → Atom G k} (hs : 0 < σ)
    (hb : SumBudget (fun i => (F i).budget σ) C) (x : Site n) (U : Config G n) :
    AnalyticAt ℂ (fun M => ∑' i, atomExt (F i) x M) (physical U) :=
  analytic_series _ (radius_pos hs)
    (fun i => (atomExt_contDiff (F i) x).differentiable (by simp))
    (hb.2.1.mul_right ((slotConst G)^k))
    (fun i M hM => atomExt_bound (F i) U hs M (ball_subset_closedBall hM) x)

lemma atomExt_real {k : ℕ} {F : ℕ → Atom G k} (hs : 0 < σ)
    (hb : SumBudget (fun i => (F i).budget σ) C) (x : Site n) (U : Config G n) :
    (∑' i, atomExt (F i) x (physical U)) = Complex.ofRealCLM (∑' i, (F i).unmasked U x) := by
  have ht : Summable (fun i => (F i).unmasked U x) :=
    .of_norm_bounded (hb.2.1.mul_right ((2:ℝ)^k))
      (fun i => ((F i).unmasked_bound U x).trans <|
        mul_le_mul_of_nonneg_right ((F i).lower_budget σ hs) (by positivity))
  rw [Complex.ofRealCLM.map_tsum ht]
  exact tsum_congr fun i => atomExt_physical (F i) U x

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {x : X} {A : X → Config G n}

lemma physical_contDiffAt
    (ha : ∀ i, ContDiffAt ℝ ω (fun y => G.mat (A y i)) x) :
    ContDiffAt ℝ ω (fun y => physical (A y)) x := by
  refine contDiffAt_pi.mpr fun i => ?_
  apply (ha i).prodMk
  exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp x (ha i)

lemma ell_contDiffAt (h : W.Bounds c σ C Λ) (p : Face (Per n))
    (ha : ∀ i, ContDiffAt ℝ ω (fun y => G.mat (A y i)) x) :
    ContDiffAt ℝ ω (fun y => W.ell (A y) p) x := by
  let L (M : Ambient G n) := ∑' i, rowExt W p i M
  have he : ContDiffAt ℝ ω L (physical (A x)) :=
    (rowExt_series h p (A x)).contDiffAt.restrict_scalars ℝ
  have hh : (fun y => W.ell (A y) p) = fun y => colorReal G (L (physical (A y))) := by
    funext y
    rw [show L (physical _) = _ from rowExt_real h p (A y), colorReal_up]
  rw [hh]
  have he' := he.comp x (physical_contDiffAt ha)
  exact (colorReal G).contDiff.contDiffAt.comp x he'

lemma uncut_contDiffAt {k : ℕ} {F : ℕ → Atom G k} (hs : 0 < σ)
    (hb : SumBudget (fun i => (F i).budget σ) C)
    (ha : ∀ i, ContDiffAt ℝ ω (fun y => G.mat (A y i)) x) :
    ContDiffAt ℝ ω (fun y => uncut F (A y)) x := by
  unfold uncut
  refine ContDiffAt.sum fun b _ => ?_
  let L (M : Ambient G n) := ∑' i, atomExt (F i) b M
  have he : ContDiffAt ℝ ω L (physical (A x)) :=
    (atomExt_series hs hb b (A x)).contDiffAt.restrict_scalars ℝ
  have hh : (fun y => ∑' i, (F i).unmasked (A y) b) =
      fun y => Complex.reCLM (L (physical (A y))) := by
    funext y
    rw [show L (physical _) = _ from atomExt_real hs hb b (A y)]
    rfl
  rw [hh]
  have he' := he.comp x (physical_contDiffAt ha)
  exact Complex.reCLM.contDiff.contDiffAt.comp x he'

lemma quadratic_contDiffAt (h : W.Bounds c σ C Λ)
    (ha : ∀ i, ContDiffAt ℝ ω (fun y => G.mat (A y i)) x) :
    ContDiffAt ℝ ω (fun y => quadratic c W (A y)) x := by
  unfold quadratic
  refine ContDiffAt.sum fun p _ => ?_
  have he : ContDiffAt ℝ ω (fun y => G.mat (faceValue (A y) p)) x := by
    simp_rw [faceValue, ← stringMat_physical]
    exact ((stringMat_contDiff (G := G) _ _).restrict_scalars ℝ).contDiffAt.comp x
      (physical_contDiffAt ha)
  have hh : ContDiffAt ℝ ω (fun y => (G.mat (faceValue (A y) p)).trace) x :=
    (Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap.contDiff.contDiffAt.comp x he
  have ht : ContDiffAt ℝ ω (fun y => G.price (faceValue (A y) p)) x :=
    contDiffAt_const.sub ((Complex.reCLM.contDiff.contDiffAt.comp x hh).div_const _)
  exact (contDiffAt_const.mul ht).add (((contDiff_norm_sq ℝ).contDiffAt.comp x
    (ell_contDiffAt h p ha)).div_const _)

lemma mainTerm_contDiffAt (h : W.Bounds c σ C Λ)
    (ha : ∀ i, ContDiffAt ℝ ω (fun y => G.mat (A y i)) x) :
    ContDiffAt ℝ ω (fun y => mainTerm c W (A y)) x := by
  unfold mainTerm Patch.average
  refine contDiffAt_const.mul (ContDiffAt.sum fun s _ => ?_)
  have he (i) : ContDiffAt ℝ ω (fun y => G.mat (pull s 0 (A y) i)) x := by
    unfold pull Step.read
    split
    · exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp x (ha _)
    exact ha _
  let A' (y) := pull s 0 (A y)
  exact ((quadratic_contDiffAt (A := A') h he).add
    (uncut_contDiffAt (A := A') h.width h.three he)).add
    (uncut_contDiffAt (A := A') h.width h.four he)

theorem answer : YM.Bid.F02 := by
  intro G c W σ C Λ h
  exact ⟨fun x n A _ ha => mainTerm_contDiffAt h ha⟩

end YM.Work.F02
