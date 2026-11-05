import YM.Push.LOOP_COEFFICIENT.LimitRules

/-! # Cofinal algebra of pair kernels (products only through exact routed operators) -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Lattice Laurent Bloch
open scoped Topology BigOperators
variable {s : ℕ → Side} {a b c : Type} {E F J : ℕ → Type}
   [DecidableEq a] [DecidableEq b] [DecidableEq c]
   [∀ i, Fintype (E i)] [∀ i, Fintype (F i)] [∀ i, Fintype (J i)]
    {A : ∀ i, Grid (s i) (E i) a} {B : ∀ i, Grid (s i) (F i) b} {D : ∀ i, Grid (s i) (J i) c}
    {V W : Momentum → Matrix a b ℂ} {X Y : ∀ i, Matrix (E i) (F i) ℂ}
namespace Mirrors
variable (hx : Mirrors A B X V) (hy : Mirrors A B Y W)
include hx
include hy in
lemma add : Mirrors A B (fun i => X i + Y i) (fun p => V p + W p) := by intro p f k hp hf hk; simp_rw [sample_add]; exact (hx _ _ _ hp hf hk).add (hy _ _ _ hp hf hk)
lemma smul (c : ℂ) : Mirrors A B (fun i => c • X i) (fun p => c • V p) := by intro p f k hp hf hk; simp_rw [sample_smul]; exact tendsto_const_nhds.smul (hx _ _ _ hp hf hk)
lemma neg : Mirrors A B (fun i => -X i) (fun p => -V p) := by simpa using hx.smul (-1)
include hy in
lemma sub : Mirrors A B (fun i => X i - Y i) (fun p => V p - W p) := by simpa only [sub_eq_add_neg] using! hx.add hy.neg
lemma transpose : Mirrors B A (fun i => (X i).transpose) (fun p => (V (-p)).transpose) := by
  intro p f k hp hf hk
  simp_rw [← sample_transpose]; exact continuous_id.matrix_transpose.continuousAt.tendsto.comp (show Tendsto _ atTop (𝓝 (V (-p))) from
    (hx _ _ _ (by rw [star_neg,hp]) hf.neg (fun i => (hk i).neg)).congr (fun i => by rw [neg_neg]; rfl))
lemma mul_routed [Fintype b] {M : ∀ i, Matrix (F i) (J i) ℂ} {U : Momentum → Matrix b c ℂ}
    (hu : ∀ p,star p = p → ContinuousAt U p) (hM : ∀ i p k, Matches p k → Routed (B i) (D i) k k (M i) (U p)) :
    Mirrors A D (fun i => X i * M i) (fun p => V p * U p) := fun _ f _ hp hf hk => (tends_mul (hx _ _ _ hp hf hk) ((hu _ hp).tendsto.comp hf)).congr fun i =>
      (sample_mul _ _ _ _ (hM i (f i) _ (hk i))).symm
lemma routed_transpose_mul [Fintype a] {M : ∀ i, Matrix (E i) (J i) ℂ} {U : Momentum → Matrix a c ℂ}
    (hu : ∀ p,star p = p → ContinuousAt U p) (hM : ∀ i p k, Matches p k → Routed (A i) (D i) k k (M i) (U p)) :
    Mirrors D B (fun i => (M i).transpose * X i) (fun p => (U (-p)).transpose * V p) := by
  simpa only [transpose_mul,neg_neg,transpose_transpose] using! (hx.transpose.mul_routed hu hM).transpose
end Mirrors
end YM.Push.Loops
