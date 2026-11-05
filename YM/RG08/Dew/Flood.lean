import YM.RG08.Dew.Dawn

/-! # Affine composition commute with heat operator.
Counting norms and corners; no invertibility of inflation. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG PertExtension PertExtension.Series GaussianScore Stationary Tensor
open Lattice Wilson Bloch Filter MeasureTheory Analysis Function Finset Matrix
open scoped Topology ContDiff Classical
variable {X Y : Type} {k n : ℕ} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable (A : Matrix Y X ℝ) (v : Y → ℝ) (M : Matrix X X ℝ)
def settler (x : X → ℝ) := A*ᵥ x + v
private def axler : (X → ℝ) →L[ℝ] (Y → ℝ) := A.mulVecLin.toContinuousLinearMap
private lemma icy (i : X) : axler A (zpk i)=∑ j,A j i • zpk j := by
  funext x; change (A*ᵥ _ ) x=_; rw [Finset.sum_apply]; simp [Matrix.mulVec,dotProduct, zpk, Pi.single_apply,mul_ite]
omit [DecidableEq X] [DecidableEq Y] in
lemma grass_settler {F : Psalm Y} (h : Grass F) : Grass (F ∘ settler A v) := by
  have he (x : Y) : Hemi 1 (fun y : X→ℝ => (A*ᵥ y) x) := start_hemi (show AnalyticAt ℝ _ _ from ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Y => ℝ) x) ∘L axler A).analyticAt _) (fun x y => by rw [Matrix.mulVec_smul]; simp)
  exact grass_comp h (fun i=> (Grass.base (he i)).sum (Grass.const _))
private lemma sonD (i : X) {F : Psalm Y} (h : ContDiff ℝ ω F) :
    Analysis.D (zpk i) (F ∘ settler A v)=∑ j,A j i • (Analysis.D (zpk j) F ∘ settler A v) := by
  funext x
  have hu : HasFDerivAt (settler A v) (axler A) x := (axler A).hasFDerivAt.add_const _
  unfold Analysis.D; rw [(((h.differentiable (by simp) _).hasFDerivAt).comp x hu).fderiv, ContinuousLinearMap.comp_apply, icy, map_sum, Finset.sum_apply]
  exact sum_congr rfl fun j _ => map_smul ..
private lemma sonDD (i j : X) {F : Psalm Y} (h : ContDiff ℝ ω F) (x : X → ℝ) : Analysis.D (zpk j) (Analysis.D (zpk i) (F ∘ settler A v)) x =
    ∑ a,∑ b,A a i*A b j *Analysis.D (zpk b) (Analysis.D (zpk a) F) (settler A v x) := by
  let G b := Analysis.D (zpk b) F
  have hc : ContDiff ℝ ω (settler A v) := (axler A).contDiff.add contDiff_const
  have hp b : ContDiff ℝ ω (G b ∘ settler A v) := (dune (zpk b) h).comp hc
  rw [sonD A v i h,Dpast, Finset.sum_apply]
  · apply sum_congr rfl; intro a _; rw [DscaleL _ _ (hp a), sonD A v _ (dune _ h),Pi.smul_apply,Finset.sum_apply]; simp [Finset.mul_sum, _root_.mul_assoc] --?
  intro a _; exact ContDiff.const_smul (R:=ℝ) _ (hp a)

lemma coming_home {F : Psalm Y} (h : ContDiff ℝ ω F) : lap (A*M*Aᵀ) F ∘ settler A v= lap M (F ∘ settler A v) := by
  funext x; unfold lap; dsimp only [Function.comp_apply]
  congr 1; simp_rw [sonDD A v _ _ h, Matrix.mul_apply,Matrix.transpose_apply, Finset.sum_mul,Finset.mul_sum]
  -- swap sums
  simp_rw [Finset.sum_comm (s:= (Finset.univ: Finset X)) (t:=(Finset.univ: Finset Y))]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
lemma dock_wick {F : Psalm Y} (h : ContDiff ℝ ω F) (n : ℕ) : wickLayer (A*M*Aᵀ) n F ∘ settler A v= wickLayer M n (F ∘ settler A v) := by
  induction n generalizing F with
  | zero=> rw [wick_zero,wick_zero]
  | succ n ih=>
    rw [wick_next,wick_next,← coming_home A v _ h,← ih (lap_prime _ h)]; rfl

variable {A v} {M}

def leaned (h : PosDef M) (μ : Measure (X→ℝ)) (A : Matrix Y X ℝ) (v : Y→ℝ) (F : Psalm Y) :=
    (crownM h).average μ (F ∘ settler A v)
theorem dock_wins {N : Matrix Y Y ℝ} (hp : N=A*M⁻¹*Aᵀ) (h : PosDef M) (μ : Measure (X→ℝ)) [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ]
    (v : Y→ℝ) {F : Psalm Y} (hf : Grass F) (u : ℕ) (hx : ∀ k,u < k → wickLayer N k F=0) :
    leaned h μ A v F= ∑ i∈range (u+1),wickLayer N i F v := by
  subst N
  rw [leaned,wick_dawns h μ (grass_settler A v hf) (l:=u) (fun k hk=>?_)]
  · apply sum_congr rfl; intro i _; rw [← dock_wick A _ M⁻¹ hf.smooth]; change wickLayer _ i F (A*ᵥ 0+v)= _; rw [Matrix.mulVec_zero,zero_add]
  rw [← dock_wick A _ _ hf.smooth k,hx k hk]; rfl
end YM.RG08
