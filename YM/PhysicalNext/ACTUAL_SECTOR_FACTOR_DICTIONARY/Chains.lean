import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Alphabet
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Tags
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.GridCost
import YM.Next.SCHEDULE.Post
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical
import YM.SectorNext.RECONNECTED_LOCALITY.Snug



/-!
Neumann at *relative* price q<1,
not using smallness of the full inverse kernel.

Internal colors combined
at each chain (no claiming symmetries of scripts from orientation
blind editing).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Notify
open Function Filter Set Matrix MeasureTheory Lattice RG Wilson
open Next.SectorChange Gaussian Schur FreeResolvent
open AnalyticBridge.RelativeLogdet
open SectorNext.Reconnect
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

abbrev Sequence (J : Type) := Σ n : ℕ, Fin (n+1) → J

/-- One ordered ratio-chain entry, for combining on the two ends. -/
def forward {J : Type} [Fintype J] [DecidableEq J] (A C : Gaussian.Table J) (i j : J) (u : Sequence J) :=
  road A (1-C*A) i j u.2

section issue
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A C : Gaussian.Table ι} {m q : ℝ}
    {D : Type*} {p : ι → D} {d : Cost D} {μ : ℝ}

private def nullmeter (ι : Type) : Ice.Radar ι where
  d := fun _ _=>0
  down := by simp
  same := by simp
  back := by simp
  chain := by simp

private lemma issued {M : Square ι} {u : ℝ} (h : d.Schur p p μ u M) (hμ : 0≤μ) : Ice.Deck (nullmeter ι) M 0 u := by
  have he := h.mono hμ (le_refl u)
  constructor <;> intro i
  · simpa [Ice.bill_zero,d.weight_zero] using he.rows.bound i
  simpa [Ice.bill_zero,d.weight_zero] using he.cols.bound i

private lemma cumulative {H E : Square ι} (h : Ice.Deck (nullmeter ι) H 0 m) (he : Ice.Deck (nullmeter ι) E 0 q)
    (hq : 0≤q) (n : ℕ) (i j : ι) :
    (∑ w : Fin n → ι, ‖road H E i j w‖) ≤ m*q^n := by
  induction n generalizing H m i with
  | zero => simpa [road,Ice.bill_zero] using h.each i j
  | succ n ih =>
    rw [sum_cons]; simp_rw [road_succ,norm_mul,← Finset.mul_sum]
    refine (Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (ih he j) (norm_nonneg _)).trans ?_
    rw [← Finset.sum_mul,pow_succ']
    exact mul_le_mul_of_nonneg_right (show (∑ j, ‖H i j‖)≤m from by simpa [Real.norm_eq_abs,Ice.bill_zero] using h.1 i)
      (mul_nonneg hq (pow_nonneg hq _))

/-- Absolute paths, not just powers. Works even for empty ι. Inputs
from Certified. Entries tested in the same completion. -/
theorem chain_receipt (h : d.Schur p p μ m A) (hc : d.Schur p p μ q (A*C-1))
    (hμ : 0 ≤ μ) (hm : 0 ≤ m) (hq : 0 ≤ q) (hy : q < 1) (hA : A.PosDef) (hC : C.PosDef) (i j : ι) :
    Summable (fun w => ‖forward A C i j w‖) ∧
      HasSum (forward A C i j) ((C⁻¹-A) i j) := by
  have hs : (d.Schur p p μ q (1-A*C)) := by convert hc.neg using 2; abel
  have ht : (d.Schur p p μ q (1-C*A)) := by
    have hv := hs.transpose
    rwa [Matrix.transpose_sub,Matrix.transpose_one,Matrix.transpose_mul,(Matrix.isHermitian_iff_isSymm.mp hC.isHermitian).eq,
      (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian).eq] at hv
  let L:=nullmeter ι
  have hdA := issued h hμ; have hd := issued hs hμ; have hd' := issued ht hμ
  have hp : Summable (fun w=> ‖forward A C i j w‖) := by
    refine (summable_sigma_of_nonneg (fun _=>norm_nonneg _)).mpr ⟨fun n => Summable.of_finite,?_⟩
    simp_rw [tsum_fintype]
    refine (((summable_geometric_of_lt_one hq hy).comp_injective (i:=fun n:ℕ=>n+1) (fun i j hh=>Nat.add_right_cancel hh)).mul_left m).of_nonneg_of_le
      (fun _ => Finset.sum_nonneg (fun i _=> norm_nonneg _)) (fun n => cumulative hdA hd' hq (n+1) i j)
  refine ⟨hp, hp.of_norm.hasSum_iff.mpr ?_⟩
  rw [hp.of_norm.tsum_sigma]; simp_rw [tsum_fintype,forward,sums_road]
  have he : ∀ n:ℕ,A*(1-C*A)^n=(1-A*C)^n*A := fun n=>by
    induction n with
    | zero=>simp
    | succ n ih=>
      have hx : A*(1-C*A)=(1-A*C)*A := by rw [mul_sub,sub_mul,mul_one,one_mul,Matrix.mul_assoc]
      rw [pow_succ',←Matrix.mul_assoc,hx,Matrix.mul_assoc,ih,pow_succ',Matrix.mul_assoc]
  simp_rw [he]
  exact (Ice.backlog A C L hd hdA hq hy hm ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
    ((Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit) i j).tsum_eq
end issue

section group
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def strand (A C : Gaussian.Table (ι × κ)) (i j : ι × κ) (s : Sequence ι) :=
    ∑ k : Fin (s.1+1)→κ, forward A C i j ⟨s.1,fun l=>(s.2 l,k l)⟩

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
def unwind : Sequence (ι×κ) ≃ Σ z : Sequence ι, Fin (z.1+1) → κ where
  toFun z := ⟨⟨z.1,fun l => (z.2 l).1⟩,fun l => (z.2 l).2⟩
  invFun z := ⟨z.1.1,fun l=>(z.1.2 l,z.2 l)⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma strands {A C : Gaussian.Table (ι×κ)} {D : Type*} {p : ι × κ → D} {d : Cost D} {μ m q : ℝ}
    (h : d.Schur p p μ m A) (hc : d.Schur p p μ q (A*C-1))
    (hμ : 0 ≤ μ) (hm : 0 ≤ m) (hq : 0 ≤ q) (hy : q < 1) (hA : A.PosDef) (hC : C.PosDef) (i j : ι×κ) :
    HasSum (strand A C i j) ((C⁻¹-A) i j) := by
  have ht := unwind.symm.hasSum_iff.mpr (chain_receipt h hc hμ hm hq hy hA hC i j).2
  have hx : ∀ n, HasSum (fun (l:Fin ((n:Sequence ι).1+1)→κ)=> (forward A C i j ∘ unwind.symm) ⟨n,l⟩) (strand A C i j n) :=
    fun n=>hasSum_fintype _
  exact ht.sigma hx
end group
end YM.PhysicalNext.Dictionary.Notify
