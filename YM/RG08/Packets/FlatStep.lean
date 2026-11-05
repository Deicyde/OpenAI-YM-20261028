import YM.RG08.Packets.Pushed

/-!
# A precision-difference identity avoiding Fourier Lipschitz at the pole

The Schur complement precision difference between two cutoffs is the bilinear pullback of the
fine precision difference using the two (generally different) means. Thus one can propagate
*any representative modulo null directions*, choosing the canonically pulled neutral curvature
representative from the previous step for the estimate (rather than subtracting diagonal
analytic completions anew). Same exponential `Folded` norm as the perturbative vacuum recursion.
Need a separate harmonic test on the free data, constant input on all face orientations,
for continued neutrality. No assertion here about convergence of an off-curl `Bed.metric`. No
loop/kinetic recalibration either: this is the order zero unmasked quadratic germ.
-/
noncomputable section
namespace YM.RG08.Flat
open Filter Finset Pert.Bulk Laurent Lattice Bloch Stationary Function Matrix RG08.Packets RG Precision Exterior
open scoped Topology ENNReal

set_option autoImplicit false
variable {c f : Side}

/-- Exact mixed Schur identity. -/
theorem poised {S : StepData c f}
    {T W : Matrix (Body 1 f) (Body 1 c) ℝ}
    {H Y : Matrix (Body 2 f) (Body 2 f) ℝ} {H' Y': Matrix (Body 2 c) (Body 2 c) ℝ}
    (h : Inputs S T H H') (h' : Inputs S W Y Y')
    (hy : Y.transpose=Y) (hy' : Y'.transpose=Y') :
    Precision.K Y'-Precision.K H' = W.transpose*(Precision.K Y-Precision.K H)*T := by
  have he {s : Side} (A : Matrix (Body 2 s) (Body 2 s) ℝ) (hA : A.transpose=A) :
      (Precision.K A).transpose = Precision.K A := by
    unfold Precision.K; rw [transpose_mul,transpose_mul,hA,transpose_transpose,Matrix.mul_assoc]
  have hx := congr_arg Matrix.transpose h'.primal
  rw [transpose_mul,transpose_mul,he Y hy,he Y' hy',transpose_transpose] at hx
  have hu := congr_arg Matrix.transpose h'.dual
  rw [transpose_mul,transpose_sub,transpose_one,transpose_smul,he Y' hy'] at hu
  rw [Matrix.mul_sub,Matrix.sub_mul,hx, Matrix.mul_assoc, h.dual, Matrix.mul_assoc W.transpose, h.primal, ← Matrix.mul_assoc, hu, Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,Matrix.smul_mul, Matrix.mul_smul]
  abel

abbrev quadratic (H : Bed) (n : Side) := Precision.K (H.metric.acts n)

/-- Curvature representative as tested on a physical torus. -/
def Sigil (B : Packet 1 Faces) (n : Side) (X : Matrix (Body 1 n) (Body 1 n) ℝ) : Prop :=
    ∃ A : Matrix (Body 2 n) (Body 2 n) ℝ, Matches (second B) A ∧ (Exterior.d 1 n).transpose * A * Exterior.d 1 n=X

variable {B : Packet 1 Faces} {q p σ τ ω r : ℝ}

/-- Actual supplied Towers input version. Doesn't require any adjoint/curl implication already on
the density remainder. -/
theorem toward (S : StepData c f) (M N : Towers S.patch.L)
    (H Y H' Y': Bed)
    (h : M.Diagonal S H H') (g : N.Diagonal S Y Y')
    {b₁ b₂ : Clip} {e₁ e₂ a₁ a₂ i₁ i₂ j₁ j₂ : ℝ}
    (hh : Floor H b₁ f e₁ a₁) (hh' : Floor H' b₂ c e₂ a₂)
    (hy : Floor Y b₁ f i₁ j₁) (hy' : Floor Y' b₂ c i₂ j₂)
    (T U : Kernel Faces Faces) (hT : Atlas ω S.patch.L 2 T q)(hU : Atlas ω S.patch.L 2 U p)
    (ht : city S.patch.L T) (hu : city S.patch.L U)
    (htP : Matches T (carrier S.ratio N Y Y')) (huP : Matches U (carrier S.ratio M H H'))
    (h₀ : neutral B) (hP : town 1 B) (H₀ : Folded τ B r)
    (hτ : 0 < τ) (hs : 0 ≤ σ) (hw : σ ≤ ω) (ha : 2*σ ≤ S.patch.L.val*τ) (hr : 0 ≤ r)
    (hR : Sigil B f (quadratic Y f - quadratic H f)) (hU₀ : travels U) :
    let B' := push B T (fun _ _=> U)
    neutral B' ∧ town 1 B' ∧ Folded σ B' (neutralCoin S.patch.L Faces Faces τ q p * r) ∧
      Sigil B' c (quadratic Y' c - quadratic H' c) := by
  intro B'
  obtain ⟨A,H₁,H₂⟩:=hR
  refine ⟨invariant hT hU H₀ hτ.le h₀ hU₀,pass_push hP ht hu,push_null hT hU H₀ hτ hs hw ha h₀,_,town_hall S.sizes hT hU ht H₀ hτ.le hr htP huP H₁,?_⟩
  have hI' := inherited_precision Y Y' g hy hy'
  have hI := inherited_precision H H' h hh hh'
  simp only [Matrix.mul_assoc,hI]
  have hX := congr_arg Matrix.transpose hI'
  rw [transpose_mul,transpose_mul] at hX
  simp only [← Matrix.mul_assoc]
  rw [hX]
  simp only [Matrix.mul_assoc]
  rw [show (Exterior.d 1 f)ᵀ*(A*(Exterior.d 1 f * installed S.ratio M.A0))=(quadratic Y f-quadratic H f)*installed S.ratio M.A0 from by rw [← H₂]; simp only [Matrix.mul_assoc]]
  rw [← Matrix.mul_assoc]
  exact (poised h.trial g.trial hy.symmetric.1 hy'.symmetric.1).symm
end YM.RG08.Flat
