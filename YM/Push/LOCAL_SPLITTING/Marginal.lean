import YM.Next.FOUNDATIONS.SU2
import YM.Push.LOCAL_SPLITTING.Calculus

/-!
# The actual shared-tag push with observations on a set of output edges

No locality/cluster assumptions in this file. Noise likelihood on a subset
of coarse edges (no data of coarse edges outside that subset); tags have their
ORIGINAL full unmarked law, and fine integration is over the full product
probability Haar prior. On the full edge set this is the actual one-step push.
Expose it as a bounded linear read on continuous test functions of the whole
prediction; yields genuine smoothness of its coarse log-coordinate germs (not
smoothness in the fine variables!) for every integrable operand, without
interchanging any unsupported derivatives and conditional limits. Underlies
an independent global/telescoping estimate, NOT a uniform norm step contraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Kernel
open Function Filter Lattice Wilson RG Source MeasureTheory Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} (S : StepData c f)
abbrev Edges (c : Side) := Finset (Edge (Site c))

def edges (X : Support c) : Edges c := Finset.univ.filter (fun e => e.1∈X ∧ e.1 + step e.2 ∈ X)
@[simp] theorem edges_univ : edges (Finset.univ : Support c) = Finset.univ := by simp [edges]

def noisy (β : ℝ) (J : Edges c) (Q V : Config G c) := ∏ b ∈ J, (S.penaltyZ β G)⁻¹ * S.penaltyWeight β (V b * (Q b)⁻¹)

def weights (U : Config G f) (h : Config G c → ℝ) := ∑ t : S.Choices, S.likelihood U t * h (S.prediction U t)

def pdf (β : ℝ) (J : Edges c) (U : Config G f) (V : Config G c) := weights S U (fun Q => noisy S β J Q V)

section Lift
def pairing : G.Mat →L[ℝ] ℝ := (((G.repDim:ℝ)⁻¹ • Complex.reLm) ∘ₗ Matrix.traceLinearMap _ _ _).toContinuousLinearMap

theorem paired (g v : G.El) : G.price (v*g⁻¹) = 1 - pairing (G.mat v * G.mat g⁻¹) := by change (1-_/_:ℝ) = 1-(G.repDim:ℝ)⁻¹*(G.mat v * G.mat g⁻¹).trace.re; rw [G.mat_mul]; ring

abbrev Mats (G : Gauge) (c : Side) := Edge (Site c) → G.Mat

private def linear (J : Edges c) : Mats G c →L[ℝ] C(Config G c,ℝ) := LinearMap.toContinuousLinearMap {
  toFun W := ⟨(fun Q => ∑ i ∈ J, pairing (W i * G.mat (Q i)⁻¹)),by fun_prop⟩
  map_add' W Z := by ext; simp [add_mul,Finset.sum_add_distrib]
  map_smul' a W := by ext; simp [Finset.mul_sum]
}

def noiseLift (β : ℝ) (J : Edges c) (V : Config G c) : C(Config G c,ℝ) :=
  ((S.penaltyZ β G)⁻¹ ^ J.card) • NormedSpace.exp ((-β*S.kernel.penalty : ℝ) •
    ((J.card:ℝ) • (1:C(Config G c,ℝ)) - linear J (G.mat ∘ V)))

theorem lifted (β : ℝ) (J : Edges c) (V Q : Config G c) : noiseLift S β J V Q = noisy S β J Q V := by
  haveI : NormedAlgebra ℚ C(Config G c,ℝ) := .restrictScalars ℚ ℝ _
  have he (h : C(Config G c,ℝ)) : NormedSpace.exp h Q = Real.exp (h Q) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.map_exp (ContinuousMap.evalAlgHom ℝ ℝ Q) (ContinuousMap.evalCLM ℝ Q (M:=ℝ)).continuous _
  simp only [noisy,StepData.penaltyWeight, paired,Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum,Finset.sum_sub_distrib,Finset.prod_const]
  simp [noiseLift,he,linear]

theorem smooth_lift (β : ℝ) (J : Edges c) (V : Config G c) (k : ℕ) : Chart k (noiseLift S β J) V := by
  have hs := show Chart k (fun U : Config G c => G.mat ∘ U) V by
    refine contDiffAt_pi.mpr fun i => ((G.exp_jet.contDiffAt.of_le le_top |>.comp (f:=fun x : Directions G c => x i) _ (contDiff_apply ..).contDiffAt).mul contDiffAt_const)
  let e := linear (G:=G) J
  have hg := ((contDiffAt_const (c:=(J.card:ℝ) • (1:C(Config G c,ℝ))) |>.sub (e.contDiff.contDiffAt.comp _ hs)).const_smul (-β*S.kernel.penalty))
  exact ((NormedSpace.exp_analytic (𝕂:=ℝ) _).contDiffAt.of_le le_top |>.comp _ hg).const_smul _
end Lift

theorem weights_meas (h : S.patch.Branches S.kernel G) (g : C(Config G c,ℝ)) : Measurable (fun U => weights S U g) :=
  Finset.measurable_fun_sum _ fun t _ => (S.likelihood_meas h t).mul (g.continuous.measurable.comp (S.prediction_meas h t))

theorem weights_bound (h : S.patch.Branches S.kernel G) (g : C(Config G c,ℝ)) (U : Config G f) : ‖weights S U g‖ ≤ ‖g‖ := by
  refine (norm_sum_le ..).trans ?_
  conv_rhs => rw [← one_mul ‖g‖,← S.chosen h U,Finset.sum_mul]
  exact Finset.sum_le_sum fun t _ => (norm_mul ..).trans_le (le_of_le_of_eq (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (norm_nonneg _)) (by rw [Real.norm_of_nonneg (S.likelihood_pos ..)]))

section Pass
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pass (β : ℝ) (J : Edges c) (F : Config G f → E) (V : Config G c) := ∫ U, pdf S β J U V • F U ∂prior G f

theorem pass_full (β : ℝ) (F : Config G f → E) : pass S β Finset.univ F = S.push β F := rfl

variable {F : Config G f → E}

theorem slice_int (h : S.patch.Branches S.kernel G) (hF : Integrable F (prior G f)) (g : C(Config G c,ℝ)) :
    Integrable (fun U => weights S U g • F U) (prior G f) :=
  hF.bdd_smul ‖g‖ (weights_meas S h g).aestronglyMeasurable (.of_forall (weights_bound S h g))

private def observe (h : S.patch.Branches S.kernel G) (hF : Integrable F (prior G f)) : C(Config G c,ℝ) →L[ℝ] E := by
  let D : C(Config G c,ℝ) →ₗ[ℝ] E := {
    toFun g := ∫ U, weights S U g • F U ∂prior G f
    map_add' a b := by
      simp_rw [show ∀ U, weights S U ⇑(a+b) = weights S U a + weights S U b from fun U => by simp [weights,mul_add,Finset.sum_add_distrib], add_smul]
      rw [integral_add (slice_int ..) (slice_int ..)] <;> assumption
    map_smul' a b := by
      simp_rw [show ∀ U, weights S U ⇑(a • b) = a*weights S U b from fun U => by simp [weights,Finset.mul_sum,mul_left_comm],mul_smul,integral_smul]; rfl
  }
  apply D.mkContinuous (∫ U, ‖F U‖ ∂prior G f)
  intro g; rw [mul_comm _ ‖g‖, ← integral_const_mul]; exact norm_integral_le_of_norm_le (hF.norm.const_mul _) (.of_forall fun U => (norm_smul ..).trans_le (mul_le_mul_of_nonneg_right (weights_bound S h g U) (norm_nonneg _)))

private theorem pass_observe (β : ℝ) (J : Edges c) (h : S.patch.Branches S.kernel G) (hF : Integrable F (prior G f)) :
    pass S β J F = observe S h hF ∘ noiseLift S β J := by
  funext V; unfold pass pdf; simp_rw [← lifted]; rfl

theorem smooth_pass (β : ℝ) (J : Edges c) (h : S.patch.Branches S.kernel G) (hF : Integrable F (prior G f)) (V : Config G c) (k : ℕ) : Chart k (pass S β J F) V := by
  rw [pass_observe S β J h hF]; exact (observe S h hF).contDiff.contDiffAt.comp _ (smooth_lift S β J V k)

theorem left_pass (β : ℝ) (J : Edges c) (h : S.patch.Branches S.kernel G) (hF : Integrable F (prior G f)) (V : Config G c) (l : List (Directions G c)) :
    leftDerivs (pass S β J F) l V = ∫ U, weights S U (fun Q => leftDerivs (noisy S β J Q) l V) • F U ∂prior G f := by
  have hd := smooth_lift S β J V l.length
  rw [pass_observe S β J h hF,left_linear (observe S h hF) l hd le_rfl]
  have he (Q : Config G c) : leftDerivs (noisy S β J Q) l V = leftDerivs (noiseLift S β J) l V Q := by
    let L : C(Config G c,ℝ) →L[ℝ] ℝ := ContinuousMap.evalCLM ℝ Q
    rw [show noisy S β J Q = L ∘ noiseLift S β J from funext fun v => (lifted ..).symm,left_linear L l hd le_rfl]; rfl
  rw [funext he]; rfl
end Pass

theorem pdf_pos (β : ℝ) (J : Edges c) (h : S.patch.Branches S.kernel G) (U : Config G f) (V : Config G c) : 0 < pdf S β J U V := by
  obtain ⟨t,ht⟩ : ∃ t, 0 < S.likelihood U t := by by_contra! hx; have he := Finset.sum_nonpos (s:=Finset.univ) fun t _ => hx t; rw [S.chosen h] at he; linarith
  have he Q : 0 < noisy S β J Q V := Finset.prod_pos fun _ _ => mul_pos (inv_pos.mpr (S.penaltyZ_pos β)) (Real.exp_pos _)
  exact Finset.sum_pos' (fun t _ => mul_nonneg (S.likelihood_pos ..) (he _).le) ⟨t, Finset.mem_univ _, mul_pos ht (he _)⟩

theorem pdf_integrable (β : ℝ) (J : Edges c) (h : S.patch.Branches S.kernel G) (V : Config G c) {D : Config G f → ℝ}
    (hD : Integrable D (prior G f)) : Integrable (fun U => pdf S β J U V * D U) (prior G f) := by
  unfold pdf; simp_rw [← lifted]; exact slice_int S h hD _

theorem pass_pos (β : ℝ) (J : Edges c) (h : S.patch.Branches S.kernel G) (V : Config G c) {D : Config G f → ℝ}
    (hD : Integrable D (prior G f)) (hp : ∀ U, 0 < D U) : 0 < pass S β J D V := by
  have he U := mul_pos (pdf_pos S β J h U V) (hp U)
  refine (integral_pos_iff_support_of_nonneg (fun U => (he U).le) (pdf_integrable S β J h V hD)).2 ?_
  rw [show Function.support _ = Set.univ from Set.eq_univ_of_forall fun x => (he x).ne']; simp
end YM.Push.Local.Kernel
