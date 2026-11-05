import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.IndexCost
import YM.Push.ABSOLUTE_SUMS.Mixed

/-!
# The operated Gaussian with all parameters

One `(T, F)` and one `A, V` determine this matrix. The mean uses frozen
link values with a *different* protection from the active broad cut,
unchanged in every word. Publish utilities for estimating that reference.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Filter Win 
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

-- r is chosen patch chart, u is frozen-shell cutoff scale inside
-- that ball (receipt to use).
structure Mint (T : Tube G S) (F : Forest S.ratio) (A : Stores S) (x : ℝ) where
  V : Config G c
  Y : F.Slice G
  q : Chi
  k : S.Choices
  r : ℝ
  u : ℝ
namespace Mint
variable {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {x : ℝ}

abbrev sheet (C : Mint T F A x) := gram T F x A C.V
abbrev D (C : Mint T F A x) := Dmat T F x A C.V

def sh (C : Mint T F A x) := fixed C.q F C.r C.u A (radiusB x) C.V C.Y
def origin (C : Mint T F A x) := zeroed T A x C.k C.V C.sh

def source (C : Mint T F A x) := (C.D.transpose) *ᵥ C.origin



def μ (C : Mint T F A x) := (eyes S G (radiusB x)).center C.sheet C.source

def actions (C : Mint T F A x) (v : ArrayR G f) := C.D *ᵥ v+C.origin

/-! Actual geometry utilities. -/

lemma roomB (S : StepData c f) (B : ℕ) : (eyes S G B).Room (dcol S) (B/4) := by
  intro i j hi
  refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _,?_⟩, mem_univ _⟩
  exact Finset.not_disjoint_iff.mpr ⟨_, pin_origin S i.1, halo_spec.mpr ⟨_,pin_origin S j.1,(separation_comm ..).trans_le hi⟩⟩

lemma travelB (S : StepData c f) (B : ℕ) (i j : Vars G f) (hp : i∈ (eyes S G B).panel j) :
    separation (dcol S i) (dcol S j) ≤ B/4+2 := by
  obtain ⟨y,hx,hy⟩ := Finset.not_disjoint_iff.mp ((Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2)
  obtain ⟨z,hz,he⟩ := halo_spec.mp hy
  rw [separation_comm]
  have hh := pin_radius _ _ hx
  rw [separation_comm] at hh
  apply le_trans (separation_triangle _ z _)
  have hp := Nat.add_le_add (pin_radius _ _ hz)
    ((separation_triangle z y _).trans (Nat.add_le_add he hh))
  exact hp.trans (by omega)

lemma activeD (C : Mint T F A x) (p : Ix G S) (i : Vars G f) (he : i.1∉activeB A F (radiusB x)) : C.D p i=0 := by
  simp [D,Dmat,he]







end Mint
open Mint Green

section Ax

variable {α β : Type*} [Fintype α] [Fintype β] (p : α → Site n) (q : β → Site n)

omit [Fintype α] in
theorem row_ball {η C s : ℝ} (A : Matrix α β ℝ) (hh : Green.Rows p q A η C) (hη : 0≤η)
    (x : β → ℝ) (hs : 0 ≤ s) (i : α) (h : ∀ j,A i j≠0 → |x j| ≤ s) : |(A *ᵥ x) i| ≤ C*s := by
  have hm := Win.mono hh hη le_rfl i
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  calc
    _ ≤ ∑ j,wt 0 (p i) (q j)*|A i j| *s := by
      apply Finset.sum_le_sum; intro j _
      rw [abs_mul,wt,zero_mul,Real.exp_zero,one_mul]; by_cases H : A i j=0
      · simp [H]
      exact mul_le_mul_of_nonneg_left (h j H) (abs_nonneg _)
    _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hm hs

lemma hold_cap (G : Gauge) (q : Chi) (r u : ℝ) (hu : 0<u) (V : G.El) : ‖hold q r u V‖ ≤ 2*u := by
  unfold hold; split
  next =>
    rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ q.innerShare u _ from (q.range _).1)]
    by_cases h : q.innerShare u ‖LocalH.snap G V‖ = 0
    · rw [h,zero_mul]; positivity
    exact (mul_le_of_le_one_left (norm_nonneg _) (q.range _).2).trans (q.chosen_lt _ u hu h).le
  next => rw [norm_zero]; positivity

variable {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {x : ℝ}
lemma fixes (C : Mint T F A x) (u : 0<C.u) (i : Bond f) : ‖lie C.sh i‖ ≤ 2*C.u := by
  unfold Mint.sh fixed; rw [lie_real]; split
  next => exact hold_cap G _ _ _ u _
  next => rw [norm_zero]; positivity
end Ax
end YM.AnalyticNext.ConnectedActivity.Aff
