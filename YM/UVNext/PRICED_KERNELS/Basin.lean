import YM.Next.SCHEDULE.Support
import YM.Push.PRICE_COMPILER.Post
import YM.UVNext.PRICED_KERNELS.Annuity
import YM.UVNext.PRICED_KERNELS.Echo



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Buy uniformly periodic volume sums and decay margins

Also at K-dependent θ for reading structure of flat Hessian. Prove
reverse price of tree rows (& of actual probe), optionally buy without
L knowledge (cost convention L^4 for target fine-cochains). Then can
use inside linear covariance costs needed vs Permit.tickets and path
forecast. Fixed positive rates--not a spectral inverse promise.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice RG Precision Pressure Laurent Exterior Bloch Matrix Tree
open Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace

variable {n : Side} {ι κ : Type*}

/-- Uniform cost of the exp mass (caller can of course also use Cover
polynomial radius and then use the already booked delay; here know before
considering any L or periods). -/
def basin (s : ℝ) := 16 * ∑' k, Next.Scheduling.decay 4 s k


lemma funnel {s : ℝ} (hs : 0<s) (x : Site n) : (∑ y : Site n, Real.exp (-s*separation x y)) ≤ basin s := by
  classical
  let t := separation x
  let A := Finset.univ (α:=Site n)
  let w := A.image t
  let B (k : ℕ) := A.filter fun i => t i=k
  have hh : (∑ y ∈ A, Real.exp (-s*t y)) = ∑ k ∈ w, (B k).card * Real.exp (-s*k) := by
    have he k : ((B k).card:ℝ)*Real.exp (-s*k) = ∑ y∈A, if t y=k then Real.exp (-s*k) else 0 := by
      rw [← Finset.sum_filter]; simp [B]
    simp_rw [he]
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i hi => by simp [w, Finset.mem_image_of_mem t hi]
  have hb (k) : (B k).card ≤ 16*(k+1)^4 := by
    have he : B k ⊆ halo k {x} := by
      intro i hi; obtain ⟨_,H⟩ := Finset.mem_filter.mp hi; exact halo_spec.mpr ⟨x,by simp,H.le⟩
    refine ((Finset.card_le_card he).trans (Corona.halo_size ..)).trans ?_
    rw [Finset.card_singleton, one_mul, show (16:ℕ)=2^4 by decide, ← mul_pow]; apply Nat.pow_le_pow_left; omega
  change ∑ y∈A, Real.exp (-s*t y) ≤ _
  rw [hh,basin]
  apply le_trans (Finset.sum_le_sum (g:=fun k => 16*Next.Scheduling.decay 4 s k) fun k _ => ?_)
  · rw [← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (decay_summable _ _ hs).sum_le_tsum _ (fun i _ => by unfold decay; positivity)
  · unfold decay; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb k) (Real.exp_pos _).le



/-- Enough count if addresses occupy subsets of physical torus types at
bounded multiplicity (independent of period). Use e.g. active Key addresses
charged on positive links. -/
structure Slots (p : Foot n ι) (C : ℝ) [Fintype ι] : Prop where
  pays (f : Site n → ℝ) (h : ∀ i, 0 ≤ f i) : ∑ i, f (p i) ≤ C * ∑ x, f x









section inter
variable {c f : Side} (g : Ratio c f)







end inter
end YM.UVNext.PricedKernels
