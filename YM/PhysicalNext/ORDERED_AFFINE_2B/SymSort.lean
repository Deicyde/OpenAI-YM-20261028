import YM.PhysicalNext.ORDERED_AFFINE_2B.CompactResolvent
import YM.PhysicalNext.ORDERED_AFFINE_2B.Currency
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymFare
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymScope
/-!
# Sorting of logged and between receipt recipes, before new integration

We prove summability even across endpoint groups at fixed V/torus,
use `income` hitting rule (uniform local support) here with full
end-origin budget, while algebra operations on PRICE themselves.
All orders kept, finite grouping or Summable tsum. This result issues on
Ranks q & sector h. Does not assert all-field summability from it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Sort
open Function Filter Set Lattice RG Wilson Precision Tree Pressure Stores
open Next Next.SectorChange Whole Matrix
open Further Further.CurvedGaussianJets Jets Tracks Completion SymRows SymWhole SymFare 
open AnalyticBridge AnalyticBridge.Covariance Terrain Scope
open SectorAffine (Afford)
open MeasureTheory  Whole.Currency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {d j m q n : ℕ} {x : ℝ}

variable {α β : Type} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]

/-- Sum first per d, over ALL including erased addresses. -/
def Solid (F : ∀ d, Run α (d+j) → ℝ) := ∀ i k : α, Summable (fun d=>∑ p, ends i k p (F d p))

def together (α β : Type) (d : ℕ) : Run α d × Run β d ≃ Run (α×β) d where
  toFun x := mix x.1 x.2
  invFun p := (Prod.fst ∘ p,Prod.snd ∘ p)
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq α] [DecidableEq β] in
lemma each (F : Run (α×β) d → ℝ) : ∑ p, F p= ∑ p : Run α d, ∑ q : Run β d,F (mix p q) := by
  rw [← Equiv.sum_comp (together α β d) F,Fintype.sum_prod_type]; rfl






variable {A : Stores S} {F : Forest S.ratio} {k : S.Choices} {T : Tube G S} {V : Config G c} {J : Tab} {σ : ℝ} {l : Word G c}
    (h : J.Ships q n σ T F A k x V) (hs : 0≤σ)
include h hs

lemma tar {j : ℕ} (hj : j≤2) (w : ∀ d, Run (Thing G f) (d+j)→ℝ)
    (ha : ∀ o : Thing G f, ∃ L : ℝ, 0 ≤ L ∧ ∀ d p, p 0=o → |w d p| ≤ L * Currency.priced J q n x d p)
    (hR : ∀ d p, ¬Angle S x (Prod.fst ∘ p) → w d p=0) : Solid w := by
  intro i k
  let z := home S i; obtain ⟨L,hL,hP⟩ := ha i
  have he := (Currency.notes h hs z false hj).1
  apply Summable.of_norm_bounded (he.mul_left L)
  intro d; apply (norm_sum_le ..).trans
  unfold Currency.sent; rw [Finset.mul_sum]; refine Finset.sum_le_sum (fun p hp=>?_)
  let b := home S (G:=G); let e := Currency.priced J q n x d p
  let M := watch*rail x; let X := dots b M p
  have H : 0 ≤ L * (if Hops b M p ∧ z∈X then Real.exp (σ*coverNumber (radiusB x) X)*e else 0) := by
    split; exact mul_nonneg hL (mul_nonneg (Real.exp_pos _).le (priced_pos ..)); rw [mul_zero]
  change ‖ends _ _ _ _‖ ≤ _; dsimp only; rw [if_neg (show ¬(false:Bool) from Bool.noConfusion)]; unfold ends
  split
  swap; exact (norm_zero.le).trans H
  next hy =>
    by_cases hu : Angle S x (Prod.fst ∘ p)
    swap
    · rw [hR _ _ hu,norm_zero]; exact H
    have ht : Hops b M p := fun i=>hired hu i
    have hz' : separation (b (p 0)) z ≤ M := hy.1.symm ▸ (show separation (b i) z≤M from by change separation z z≤ M; simp)
    have hz : z ∈ X := dots_mem.mpr ⟨0,hz'⟩
    rw [if_pos (show Hops b M p ∧ z∈X from ⟨ht,hz⟩)]
    change |w d p|≤ _
    apply (hP d p hy.1).trans
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (priced_pos ..) (Real.one_le_exp (by positivity))) hL


end YM.PhysicalNext.OrderedAffine2B.Sort
