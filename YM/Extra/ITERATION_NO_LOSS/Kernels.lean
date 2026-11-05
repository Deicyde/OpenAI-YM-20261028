import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.ITERATION_NO_LOSS.Patterns
import YM.Laurent.Art
import YM.Work.F07.Read

/-!
# Laurent tables to actual atoms with pre-L weights and paths

Use an ambient displacement for each leg (no requirement all relative layouts
actually need that many variables). For a conserved translation tensor one can
fix a final offset at zero / extend independently of the redundant momentum
in this convention. Real physical orthonormal colors, coefficient-dual sign
+ i p⋅offset as in the cover reader, inverse and basepoint changes on the
link fields by pull of the entire configuration (not sorting offsets after
assigning paths). Common translations still summed in each action by the RG
library. No finite-torus Wick/exterior lift juggling alias degree.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Kernels
open Filter Function Lattice Wilson RG Precision Tree Laurent Bloch MeasureTheory UnitAddTorus Finset
open scoped Topology BigOperators ContDiff ComplexConjugate Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {k : ℕ}

abbrev Displacement (k : ℕ) := Shift (Fin k × Axis)
abbrev Momenta (k : ℕ) := Laurent.Phase (Fin k × Axis)
abbrev Shape (k : ℕ) := Fin k → PlaqAxes
abbrev Hue (G : Gauge) (k : ℕ) := Fin k → G.ColorIndex
abbrev Kernel (G : Gauge) (k : ℕ) := Shape k → Hue G k → Displacement k → ℝ
abbrev Symbol (G : Gauge) (k : ℕ) := Shape k → Hue G k → Momenta k → ℂ

def point (z : Displacement k) (i : Fin k) : Cover := fun l => z (i,l)


def emit (K : Kernel G k) (p : Shape k × Displacement k) : Atom G k where
  leg i := slot (point p.2 i) (p.1 i)
  coeff b := K p.1 b p.2

def array (K : Kernel G k) := padded (emit K)


def install (G : Gauge) (k : ℕ) (σ : ℝ) := (Fintype.card (Shape k) : ℝ) * (Fintype.card (Hue G k) : ℝ) * Real.exp (σ*((4*k:ℕ):ℝ))

structure Priced (K : Kernel G k) (σ A : ℝ) : Prop where
  sym (i : Shape k) (z : Displacement k) (g : G.El) (x : Fin k → G.Color) : (∑ b, K i b z * ∏ j, (G.adjoint g (x j)) (b j)) =
      ∑ b,K i b z * ∏ j,x j (b j)
  cost : ∃ B : ℝ, 0 ≤ B ∧ install G k σ * B ≤ A ∧ ∀ i b, Laurent.Width σ B (K i b)

namespace Priced
variable {K : Kernel G k} {σ A : ℝ} (h : Priced K σ A)
include h

lemma symm : SymmetricAtoms (array K) := padded_sym fun p g x => h.sym p.1 p.2 g x



end Priced



def inverse (u : Symbol G k) : Kernel G k := fun i b z => (market (u i b) 0 z).re

structure Whole (u : Symbol G k) (η C : ℝ) : Prop where
  positive : 0 < η
  nonnegative : 0 ≤ C
  sym (a : Momenta k) (ha : star a = a) (i) (g : G.El) (x : Fin k → G.Color) :
      (∑ b, u i b a * ∏ j, ((G.adjoint g (x j) (b j):ℝ):ℂ)) = ∑ b, u i b a * ∏ j, ((x j (b j) : ℝ):ℂ)
  complexPrice i b a : a∈Laurent.strip η → ‖u i b a‖ ≤ C
  vane i b : Vane (u i b) η
  real a : star a=a → ∀ i b, star (u i b (-a)) = u i b a

namespace Whole
variable {u : Symbol G k} {η C : ℝ} (h : Whole u η C)
include h


def fee (η σ : ℝ) (k : ℕ) := let b := (η-σ)/2; (2*((1+b)/b))^(Fintype.card (Fin k × Axis))
lemma width {σ : ℝ} (hs : 0 ≤ σ) (he : σ < η) : ∀ i b, Laurent.Width σ (C*fee η σ k) (inverse u i b) := fun i b =>
  Work.F07.widthRealPart ((h.vane i b).issues (h.complexPrice i b) _ _ hs (by linarith) (by linarith))
lemma member (i : Shape k) (z : Displacement k) (g : G.El) (x : Fin k → G.Color) :
    (∑ b, inverse u i b z * ∏ j, (G.adjoint g (x j)) (b j)) = ∑ b, inverse u i b z * ∏ j,x j (b j) := by
  have he (x : Fin k → G.Color) : (∑ b, market (u i b) 0 z * ∏ j, ((x j (b j):ℝ):ℂ)) =
      market (fun p => ∑ b, u i b p * ∏ j, ((x j (b j) : ℝ):ℂ)) 0 z := by
    have ht (b) : Continuous (veils (u i b) 0) := ((h.vane i b).guise (Work.F07.realStrip _ h.positive (star_zero _))).continuous
    change (∑ b, (∫ t, (mFourier (-z) t)*veils (u i b) 0 t ∂globe _)*_) = ∫ t, (mFourier (-z) t)*_ ∂globe _
    have hF b : Integrable (fun t => (mFourier (-z) t)*veils (u i b) 0 t * ∏ j, ((x j (b j):ℝ):ℂ)) (globe _) :=
      (((mFourier (-z)).continuous.mul (ht b)).mul_const _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp_rw [← integral_mul_const]; rw [← integral_finsetSum _ (fun b _ => hF b)]; simp only [veils,Finset.mul_sum,mul_assoc]
  have ht := congr_arg Complex.re ((he (fun j => G.adjoint g (x j))).trans (Eq.trans ?_ (he x).symm))
  · simpa [inverse,Complex.re_sum, ← Complex.ofReal_prod] using ht
  change (∫ t, mFourier (-z) t * _ ∂globe _) = ∫ t, mFourier (-z) t * _ ∂globe _
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_); unfold veils; dsimp only
  exact congr_arg (mFourier (-z) t * ·) (h.sym _ (by ext1 v; simp [Laurent.walk]) i g x)

lemma priced {σ : ℝ} (hs : 0 ≤ σ) (he : σ < η) : Priced (inverse u) σ (install G k σ * (C*fee η σ k)) where
  sym := h.member
  cost := ⟨_,(mul_nonneg h.nonnegative (by unfold fee; have := sub_pos.mpr he; positivity)),le_rfl,h.width hs he⟩
end Whole

def pair (l : Axis) (t : ℝ) : Momenta 2 := fun j => if j.2 = l then if j.1=(1:Fin 2) then (t:ℂ) else -(t:ℂ) else 0

structure Resolved (u : Symbol G 2) : Prop where
  zeroth i b : u i b 0=0
  first i b l : HasDerivAt (fun t : ℝ => u i b (pair l t)) 0 (0:ℝ)








end YM.Extra.Iteration.Kernels
