import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Push.FREE_RESOLVENT.Inverse
import YM.Push.FREE_RESOLVENT.Torus
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06


/-!
# One actual universal Row inverse for all periods

Produce exact inverse in the `Horizon` row convention from Width
of the *forward* row and genuine finite coercivity (not conditioned on an
inverse estimate). No complex-symbol coercivity needed. Pre-L when its inputs
are pre-L (watch the cardinality in the strip budget for anything with
residue rows).

Proof: intertwine *different* meshes by real convolution
on a common stencil, invert in finite dimensions at every volume, take
limit on nested tori. A single Row gives all the periodic answers *exactly*
with the same exponential width. The subsequence here is inside the proof of
a statement on ONE Fourier-independent operator, has nothing to do with the
trajectory/order, no change of calibration, etc. In particular no ISMain
assumed and uses also work with varying forward operator family and common
upper and lower widths. Avoid determinant height estimates and ignoring
rank drop at individual Fourier modes.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice RG Matrix Laurent Bloch Exterior Precision Work.F08 Filter Topology
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

namespace Universal
variable {α β : Type*} {n m : Side}

/-- Folding m -> n, including a possible anchor shift. -/
def overlay (f : Site m → Site n) (x : Co m α) : Co n α := (f x.1,x.2)

/-- Pull by true wrap. Uses this on translations too. -/
lemma law [Fintype β] (P : Row α β) (h : P.safe) (f : Site m → Site n)
    (he : ∀ x z, f (x+wrap m z) = f x+wrap n z) (u : Co n β → ℝ) :
    P.acts m *ᵥ (u ∘ overlay f) = (P.acts n *ᵥ u) ∘ overlay f := by
  funext ⟨x,i⟩
  simp only [mulVec,dotProduct]; rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Function.comp_apply, Matrix.mulVec, dotProduct]; rw [Fintype.sum_prod_type, Finset.sum_comm (s:=Finset.univ (α:=Site n))]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ∑ y, sift (P i j) m x y * u (f y,j) = ∑ y, sift (P i j) n (f x) y * u (y,j)
  rw [sift_action ((h i j).of_norm) m x (fun y => u (f y,j)), sift_action ((h i j).of_norm) n (f x) (fun y => u (y,j))]
  simp only [he]

abbrev Each [Fintype α] [Fintype β] (P : (n : Side) → Matrix (Co n α) (Co n β) ℝ) :=
  ∀ (m n : Side) (f : Site m → Site n), (∀ x z, f (x+wrap m z)=f x+wrap n z) →
    ∀ u : Co n β → ℝ, P m *ᵥ (u ∘ overlay f) = (P n *ᵥ u) ∘ overlay f

variable [Fintype α]

/-- Natural even under anchor shifts on the tori. -/
lemma inverses [DecidableEq α] {P : Row α α} (h : P.safe) (u : ℝ)
    (hi : ∀ n, IsUnit (P.acts n + u • 1).det) : Each (fun n => resolve (P.acts n) u) := by
  intro m n f he v
  let A (n : Side) := P.acts n + u • 1
  let y := resolve (P.acts n) u *ᵥ v
  apply Matrix.mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det (A m)).mpr (hi m))
  have hk : ∀ v : Co n α → ℝ, A m *ᵥ (v ∘ overlay f) = (A n *ᵥ v) ∘ overlay f := fun v => by
    simp only [A, Matrix.add_mulVec, law P h _ he,Matrix.smul_mulVec, one_mulVec]; rfl
  have hv : A n *ᵥ y = v := by unfold y resolve; rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hi n), Matrix.one_mulVec]
  change A m *ᵥ (resolve (P.acts m) u *ᵥ _) = A m *ᵥ (y ∘ _)
  rw [hk,hv,Matrix.mulVec_mulVec]; exact Eq.trans (by rw [show A m*resolve (P.acts m) u=1 from Matrix.mul_nonsing_inv _ (hi m)]) (Matrix.one_mulVec _)

-- general export test reusable for other matrix functions too; no regularity in real fields implied
variable [Fintype β] (P : (n : Side) → Matrix (Co n α) (Co n β) ℝ)

omit [Fintype β] [Fintype α] in
lemma modulo {m n : Side} (h : n.val ∣ m.val) : ∃ f : Site m →+ Site n, ∀ z, f (wrap m z) = wrap n z := by
  let g := ZMod.castHom h (Per n)
  let F : Site m →+ Site n := {
    toFun x i := g (x i)
    map_add' _ _ := funext fun i => g.map_add _ _
    map_zero' := funext fun _ => g.map_zero }
  exact ⟨F,fun z => funext fun i => map_intCast g (z i)⟩

def innate (n : Side) : Row α β := fun i j z => if lift (wrap n z)=z then P n (0,i) (wrap n z,j) else 0

omit [Fintype β] [Fintype α] in
lemma innate_point {r M : ℝ} (hm : 0 ≤ M)
    (h : ∀ n x y, |P n x y| ≤ (taxi n).weight (-r) x.1 y.1 * M) (n : Side) (i : α) (j : β) (z) :
    |innate P n i j z| ≤ Real.exp (-r*size z)*M := by
  by_cases ht : lift (wrap n z)=z
  · have hh := h n (0,i) (wrap n z,j)
    rwa [innate, if_pos ht, ← show (taxi n).weight (-r) 0 (wrap n z) = Real.exp (-r*size z) by
      change Real.exp (-r * size (lift (wrap n z-0))) = _; rw [sub_zero, ht]]
  rw [innate, if_neg ht,abs_zero]; positivity

lemma folding [DecidableEq β] (h : Each P) (m n : Side) (hv : n.val ∣ m.val) : (innate P m).acts n = P n := by
  obtain ⟨L,hL⟩ := modulo hv
  ext ⟨x,i⟩ ⟨y,j⟩
  let f : Site m → Site n := fun k => x+L k
  have he (k z) : f (k+wrap m z) = f k + wrap n z := by simp [f,hL,add_assoc]
  -- naturality with point mass at the addressed coordinate in n
  let v : Co n β → ℝ := Pi.single (y,j) 1
  have hh : P m *ᵥ (v ∘ overlay f) = (P n *ᵥ v) ∘ overlay f := h m n f he v
  let F (w : Cover) := if y=x+wrap n w then innate P m i j w else 0
  change (∑' w, F w)=_
  rw [tsum_eq_sum (s:=Finset.univ.image (@lift m))]
  · rw [Finset.sum_image ((Function.LeftInverse.injective (@wrap_lift m)).injOn)]
    calc
      _ = (P m *ᵥ (v ∘ overlay f)) (0,i) := by
        rw [Matrix.mulVec,dotProduct,Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun a _ => ?_
        have hk : f a=x+wrap n (lift a) := by rw [← hL,wrap_lift]
        by_cases hy : y=x+wrap n (lift a) <;>
          simp only [F,hy,↓reduceIte, innate, wrap_lift, v, Function.comp_apply, overlay, Pi.single_apply,
            Prod.mk.injEq,hk, mul_ite, mul_zero, mul_one] <;> simp [hy,eq_comm]
      _ = _ := by rw [hh]; simp [v, overlay,f]
  intro b hb
  unfold F innate
  split_ifs with h1 h2
  · exact False.elim (hb (Finset.mem_image.mpr ⟨_,Finset.mem_univ _,h2⟩))
  all_goals rfl

/-- Forced simultaneous support estimate on the real infinite-volume
coefficients, and export equality for ALL finite volumes. No group order
norm hiding β fibers. -/
theorem publish [DecidableEq β] {r M γ : ℝ} (hr : 0 < r) (hm : 0 ≤ M) (hγ : γ < r) (h : Each P)
    (hh : ∀ n x y, |P n x y| ≤ (taxi n).weight (-r) x.1 y.1 * M) :
    ∃ Q : Row α β, Q.strip γ (sheetPay (r-γ)*M) ∧ ∀ n : Side, Q.acts n = P n := by
  classical
  let F : ℕ → Side := fun i => ⟨Nat.factorial i,Nat.factorial_pos _⟩
  let T := fun (p : α × β × Cover) (k : ℕ) => innate P (F k) p.1 p.2.1 p.2.2
  let w (z : Cover) := Real.exp (-r*size z)*M
  obtain ⟨t,y,hy⟩ := Extraction.simultaneous (X:=fun _ => ℝ) T
    (K:=fun p => Set.Icc (-w p.2.2) (w p.2.2)) (fun _ => isCompact_Icc) (fun p =>
      Filter.Eventually.of_forall fun k => abs_le.mp (innate_point P hm hh ..))
  let Q : Row α β := fun i j z => y (i,j,z)
  have hx (i j z) : ‖Q i j z‖ ≤ w z := abs_le.mpr (hy (i,j,z)).1
  refine ⟨Q,fun i j => ?_,fun n => ?_⟩
  · let u := fun z : Cover => Real.exp (-(r-γ)*size z)
    have hp : RG.SumBudget u (sheetPay (r-γ)) := Width.compactPay _ (sub_pos.mpr hγ)
    have hw : RG.SumBudget (fun z => u z*M) (sheetPay (r-γ)*M) := ⟨fun z => mul_nonneg (hp.1 z) hm,hp.2.1.mul_right M,
      by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hp.2.2 hm⟩
    refine budget_minor hw (fun _ => by positivity) ?_
    intro z
    refine (mul_le_mul_of_nonneg_left (hx i j z) (Real.exp_pos _).le).trans_eq ?_
    unfold w u; rw [← mul_assoc,← Real.exp_add]; congr 2; ring
  -- dominated convergence (for this n only cofinally on arbitrary test n)
  have hd : ∀ᶠ i in atTop, n.val ∣ (F (t i)).val := by
    filter_upwards [t.cofinal.eventually (eventually_ge_atTop n.val)] with i hi
    exact Nat.dvd_factorial n.pos hi
  have hw : Summable w := (Width.compactPay (α:=Axis) _ hr).2.1.mul_right M
  ext i j
  let A (k : ℕ) (z : Cover) := if j.1=i.1+wrap n z then innate P (F (t k)) i.2 j.2 z else 0
  let B (z : Cover) := if j.1=i.1+wrap n z then Q i.2 j.2 z else 0
  have ht : Tendsto (fun k => ∑' z, A k z) atTop (𝓝 (∑' z, B z)) := by
    refine tendsto_tsum_of_dominated_convergence hw (fun k => ?_) (Filter.Eventually.of_forall (fun k z => ?_))
    · dsimp only [A,B]
      split
      · exact (hy (i.2,j.2,k)).2
      · exact tendsto_const_nhds
    unfold A; split
    · exact innate_point P hm hh ..
    rw [norm_zero]; unfold w; positivity
  have hb : Tendsto (fun _ : ℕ => P n i j) atTop (𝓝 (Q.acts n i j)) := by
    refine ht.congr' (hd.mono (fun k h => ?_))
    exact congr_fun (congr_fun (folding P (by assumption) _ n h) i) j
  exact tendsto_nhds_unique hb tendsto_const_nhds
end Universal
end YM.FreeResolvent
