import YM.Euclid.Window
import YM.Work.A15.Tensor

/-!
# A linear flux test on stresses

This will let us handle rotations of the shell by pulling back the vector
fields. Also, applying flux to an *average* stress will simply be passing the
linear map through an integral on the group (no Fubini at collisions). We use
`integrableShell` in taking these shell integrals, on the very same windows as
in `StressLaws`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A15

open Set MeasureTheory Analysis Table
open scoped BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L} {n d : ℕ}

/-- The linear evaluation of a quotient field in the first slot. -/
def front (x : Points (n+1)) (q : Fin n → S.Tag) (d : ℕ) : S.Field d →ₗ[ℂ] ℂ :=
  Ward.here (Fin.cons (⟨d,0⟩ : S.Tag) q) x 0 d

lemma front_apply (x : Points (n+1)) (q : Fin n → S.Tag) (d : ℕ) (B : S.Field d) :
    front x q d B = S.useAt S x (Fin.cons ⟨d,B⟩ q) := by
  rw [front, Ward.takes, Ward.disc]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

def gradVec (χ : E4 → ℝ) (y : E4) : E4 := WithLp.toLp 2 fun a => Analysis.D (basis a) χ y

lemma gradVec_apply (χ : E4 → ℝ) (y : E4) (a : Axis) :
    gradVec χ y a = Analysis.D (basis a) χ y := rfl

section Flux

variable (x : Points (n+1)) (q : Fin (n+1) → S.Tag) (χ : E4 → ℝ) (W : E4 → E4)

/-- As for `shellGrad`, for use at `Window x χ`. The B tag is included in q. -/
def fluxCore (J : S.Stress) := -(∫ y : E4, front (Points.cons y x) q 4
  (contractStress (gradVec χ y) (W y) J))

private lemma flux_eval (J : S.Stress) (y : E4) :
    front (Points.cons y x) q 4 (contractStress (gradVec χ y) (W y) J) =
      ∑ a : Axis, ∑ b : Axis, ((Analysis.D (basis a) χ y * W y b : ℝ) : ℂ) *
        S.useAt S (Points.cons y x) (Fin.cons ⟨4,J a b⟩ q) := by
  rw [contractStress_apply]
  simp only [map_sum, map_smul, smul_eq_mul, front_apply, gradVec_apply]

variable {x χ W} (hx : x ∈ conf (n+1)) (w : Window x χ) (H : S.Smooth) (hW : Continuous W)
include hx w H hW

private lemma flux_integrable_term (J : S.Stress) (a b : Axis) :
    Integrable (fun y : E4 => ((Analysis.D (basis a) χ y * W y b : ℝ) : ℂ) *
      S.useAt S (Points.cons y x) (Fin.cons ⟨4,J a b⟩ q)) := by
  simp_rw [Complex.ofReal_mul]
  exact Table.integrableShell hx w H _ a (fun y : E4 => (↑(W y b) : ℂ)) (by fun_prop)

private lemma integrable_flux (J : S.Stress) :
    Integrable (fun y : E4 => front (Points.cons y x) q 4
      (contractStress (gradVec χ y) (W y) J)) := by
  simp_rw [flux_eval]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    flux_integrable_term q hx w H hW J a b

def fluxMap : S.Stress →ₗ[ℂ] ℂ where
  toFun := fluxCore x q χ W
  map_add' J K := by
    simp only [fluxCore, map_add]
    rw [integral_add (integrable_flux q hx w H hW J) (integrable_flux q hx w H hW K), neg_add]
  map_smul' c J := by
    simp only [fluxCore, map_smul, integral_smul, smul_neg, RingHom.id_apply]

lemma flux_expansion (J : S.Stress) : fluxCore x q χ W J =
    - ∑ a : Axis, ∑ b : Axis, ∫ y : E4, ((Analysis.D (basis a) χ y * W y b : ℝ) : ℂ) *
      S.useAt S (Points.cons y x) (Fin.cons ⟨4,J a b⟩ q) := by
  unfold fluxCore
  apply congrArg Neg.neg
  simp_rw [flux_eval]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun a _ =>
      integral_finsetSum _ fun b _ => flux_integrable_term q hx w H hW J a b
  intro a _
  exact integrable_finsetSum _ fun b _ => flux_integrable_term q hx w H hW J a b
end Flux

lemma continuous_spin_vector (g : Ortho.Skew) (z : E4) :
    Continuous (fun y : E4 => M4.move g.val (y-z)) :=
  (Matrix.toEuclideanLin g.val).continuous_of_finiteDimensional.comp
    (continuous_id.sub continuous_const)

section Windows

variable {x : Points (n+1)} (hx : x ∈ conf (n+1)) {χ : E4 → ℝ} (w : Window x χ) (H : S.Smooth)
    (q : Fin n → S.Tag) (B : S.Field d)
include hx w H

theorem fluxCore_const (J : S.Stress) (u : E4) :
    fluxCore x (Fin.cons ⟨d,B⟩ q) χ (fun _ => u) J =
      ∑ b : Axis, ((u b : ℝ) : ℂ) • shellGrad S J χ b x q B := by
  rw [flux_expansion _ hx w H continuous_const, Finset.sum_comm]
  simp only [shellGrad, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp_rw [mul_comm (Analysis.D (basis a) χ _), Complex.ofReal_mul, mul_assoc,
    integral_const_mul]
  rfl

lemma fluxCore_basis (J : S.Stress) (i : Axis) :
    fluxCore x (Fin.cons ⟨d,B⟩ q) χ (fun _ => basis i) J = shellGrad S J χ i x q B := by
  rw [fluxCore_const hx w H, Finset.sum_eq_single i]
  · simp
  · intro a _ ha; simp [ha]
  · simp

lemma fluxCore_angular (J : S.Stress) (g : Ortho.Skew) :
    fluxCore x (Fin.cons ⟨d,B⟩ q) χ (fun y => M4.move g.val (y - x 0)) J =
      shellSpin S J χ g x q B :=
  flux_expansion _ hx w H (continuous_spin_vector g (x 0)) J

def translationFlux (i : Axis) : S.Stress →ₗ[ℂ] ℂ :=
  fluxMap (Fin.cons ⟨d,B⟩ q) hx w H (W := fun _ => basis i) continuous_const

def angularFlux (g : Ortho.Skew) : S.Stress →ₗ[ℂ] ℂ :=
  fluxMap (Fin.cons ⟨d,B⟩ q) hx w H (continuous_spin_vector g (x 0))

lemma translationFlux_apply (i : Axis) (J : S.Stress) :
    translationFlux hx w H q B i J = shellGrad S J χ i x q B := fluxCore_basis hx w H q B J i

lemma angularFlux_apply (g : Ortho.Skew) (J : S.Stress) :
    angularFlux hx w H q B g J = shellSpin S J χ g x q B := fluxCore_angular hx w H q B J g
end Windows

end YM.Work.A15
