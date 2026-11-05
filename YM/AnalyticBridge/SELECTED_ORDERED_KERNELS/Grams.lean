import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.LocalRows

/-!
# Forward input commissioning on small real affine ball

All ordinary chart assumptions except the inverse gap paid here. Assembly
follows the affine square/channel rules of BlockRate with the nonflat
receipts. Slice radius independent of mark width, field/path cuts, period
and tags (at fixed G/smoothing step/order).
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Small
open Lattice Wilson RG Precision Tree Exterior Function Filter Topology Bloch Laurent Metric Matrix FreeResolvent Affine
  Lifted View TestD Mark
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {P : Patch} {K : KernelChoices} {h : f.val=c.val*P.L.val} {n : ℕ} {S : StepData c f}
  {σ C M d : ℝ} {t : S.Choices} {B : Vec G c 1} {W : PathData G}

section bundle
variable {X Y ι κ τ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι] [Fintype κ]
  {D : Cost Y} {m : Mark τ Y} {v : τ → X} {a : ι → Y} {b : κ → Y} {x : X} {F : X → Matrix ι κ ℝ}

end bundle

abbrev Allow {ι κ : Type*} [Fintype ι] [Fintype κ] (B : Vec G c 1) (n : ℕ) (d γ C : ℝ) (a : ι → Site c) (b : κ → Site c)
    (F : Vec G c 1 → Matrix ι κ ℝ) := Bundle (ray G c) (marks G c d) (native c) a b (around B F) 0 n γ C

abbrev low (P : Patch) (G : Gauge) (σ : ℝ) (n : ℕ) (C : ℝ) := faceFoot P G (staging σ n) n C
abbrev high (P : Patch) (G : Gauge) (σ : ℝ) (n : ℕ) (C : ℝ) := noiseFoot P G (staging σ n) n C
def transportPrice (P : Patch) (G : Gauge) (σ : ℝ) (n : ℕ) (C M : ℝ) := tagPrice 1 n (longPrice G P n M σ) (low P G σ n C)
def squarePrice (P : Patch) (G : Gauge) (K : KernelChoices) (p : Clip) (σ : ℝ) (n : ℕ) (C M : ℝ) :=
  let x := low P G σ n C; let y := transportPrice P G σ n C M; let z := high P G σ n C
  p.direct * tagPrice 1 n x x + tagPrice 1 n y y + K.penalty * tagPrice 1 n z z

def tailPrice (P : Patch) (G : Gauge) (σ : ℝ) (n R : ℕ) (C M : ℝ) := let t := transportPrice P G σ n C M
  Real.exp (-(σ/4)*R) * (2*tagPrice 1 n t t)

structure Rated (S : StepData c f) (t : S.Choices) (s : Signed) (B : Vec G c 1) (σ d : ℝ) (n : ℕ) (C : ℝ) : Prop where
  face_cost : Allow B n d (staging σ n) (low S.patch G σ n C) (named S s) (home S) (response S s)
  duct_cost : Allow B n d (staging σ n) (high S.patch G σ n C) (namedCo s) (home S) (duct S s t)

variable (hs : 0 < σ) (hM : 0 ≤ M) (hc : 0 ≤ C)
include hs hM hc
lemma path_nn : 0 ≤ transportPrice P G σ n C M := tag_nn (longPrice_nn G P hs hM) (foot_nn P G (staging_pos hs n) n hc).1

lemma square_nn (K : KernelChoices) (p : Clip) : 0 ≤ squarePrice P G K p σ n C M := by
  obtain ⟨hl,hr⟩ := foot_nn P G (staging_pos hs n) n hc; have ht : 0 ≤ transportPrice P G σ n C M := path_nn hs hM hc
  exact add_nonneg (add_nonneg (mul_nonneg p.quadratic_pos.le (tag_nn hl hl)) (tag_nn ht ht)) (mul_nonneg K.penalty_pos.le (tag_nn hr hr))

variable (hW : Sheet W σ M) (hd : 0 ≤ d) (he : d ≤ tier σ n) (hb : ‖B‖ < (filePrice G)⁻¹) (s : Signed) (rated : Rated S t s B σ d n C)
include hd he hb rated hW







omit rated

section all




end all

omit hc hd he hW hb


end YM.SelectedOrderedKernels.Small
