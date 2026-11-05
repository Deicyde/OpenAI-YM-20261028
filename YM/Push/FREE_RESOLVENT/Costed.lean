import YM.Next.FOUNDATIONS.Primary
import YM.Push.FREE_RESOLVENT.Fees
import YM.Push.FREE_RESOLVENT.TensorPrice

/-!
# Root measurements for the full Tag application

Keep an **absolute** sum over all the Taylor indices, anchored at any
chosen endpoint, or even aggregated over all that visit an origin site
through a Taylor index. Charge the star cost rather than the shortest tree
through those positions. On varying a local tree tag, DO NOT pay per volume;
obtain the total sum instead. The counts include basis fields and Frobenius
normalization. Norm transfer to rolling weighted directions is later.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice RG Precision Tree Matrix Mark TestD Filter Function Set Lever Stars
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {X E τ α β : Type*}

section passages
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype α]
variable {p : τ → E} {a : α → X} {P : τ → X} {v : X} {D : Cost X} {γ d M : ℝ} {n : ℕ}
lemma restricted {A : E × ℝ → Matrix α α ℝ} (t : ℝ)
    (hp : Bundle (guides p) (park D P d v) D a a A (0,t) n γ M) :
    Bundle p (positions D P d) D a a (fun y => A (y,t)) 0 n γ M := by
  constructor
  · exact hp.smooth.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  intro l hl
  have hh := hp.bound (l.map some) (by simpa using hl)
  rw [restriction p l t (smooth_of_le hp.smooth hl)] at hh
  constructor <;> constructor <;> intro i
  · rw [← parks l D P d v]; exact hh.row.rows i
  rw [← parks l D P d v]; exact hh.col.rows i

end passages

namespace Affine
variable {G : Gauge} {c f : Side} {S : StepData c f} {u σ M A : ℝ} {W : PathData G}
variable (T : Forest S.ratio) (t : S.Choices) (p : Clip)
variable (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S) (hu : 0 ≤ u)

-- path discrepancy common for template use
def diminish (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n r : ℕ) (A σ u : ℝ) :=
  let v := earnings G P K p n A σ * drain u
  let C := phasePrice G P K n A σ
  tagPrice 1 n (tagPrice 1 n v (3*(Real.exp (-(σ/4)*r)*(2*tagPrice 1 n C C)))) v

include hs ha hW he hu




omit hs ha hW he hu

-- Per site prices without bounding output center (sup anchored, not all-pairs globally in the no-tag clause).
def together (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ) (A σ : ℝ) :=
  width G P K p n A σ / (2*(n+3:ℕ))
def totalFoot (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ) (A σ : ℝ) :=
  let e := together G P K p n A σ
  max (torusPay (Bloch.Co P.L (PAC G 1)) e) (torusPay (PAC G 1) e)



/-- Consumer type of the tensor estimations. Even for order-0 evaluations,
request n>0 for the tag difference version. -/
structure Scatter (G : Gauge) (S : StepData c f) (p : Clip) (σ A : ℝ) (j n : ℕ) (price rent : ℝ)
    (K : Forest S.ratio → Vec G c 1 → Matrix (raw G f) (raw G f) ℝ) : Prop where
  regular (T : Forest S.ratio) (w : Site c) (W : raw G f → raw G f → (Fin j → raw G c) → Bool)
    (h : ∀ i t k, W i t k=true → w=home S i ∨ w=home S t ∨ ∃ m, w=hearth (k m)) :
    Stars.NearStar j (native c) (home S) (home S) hearth w W (together G S.patch S.kernel p n A σ)
      (Stars.crowd j price (totalFoot G S.patch S.kernel p n A σ)) (fun i t k => iteratedFDeriv ℝ j (K T) 0 (ray G c ∘ k) i t)
  tag (T U : Forest S.ratio) (v : Site c) : changed S T U v →
    Stars.NearStar j (native c) (home S) (home S) hearth v (fun _ _ _ => true) (together G S.patch S.kernel p n A σ)
      (Stars.crowd j rent (totalFoot G S.patch S.kernel p n A σ)) (fun i t k =>
        iteratedFDeriv ℝ j (K U) 0 (ray G c ∘ k) i t-iteratedFDeriv ℝ j (K T) 0 (ray G c ∘ k) i t)

include hs ha


include hW he hu






end Affine
end YM.FreeResolvent
