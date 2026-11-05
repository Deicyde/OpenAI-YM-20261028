import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Packets

/-!
# Consumer of altered exponential factor within a compulsory packet

For working even with `earn * leftOver` bills. This removes an EXPENSIVE
assessed energy, not a routine small Taylor factor or eligibility thinning.
From the annulus estimate pay also this case (which doesn't require the
assessed lower bound again). Use only at the named O,Q,J,F etc with protections.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp.Drain
open Filter Function Lattice RG Pressure Pressure.Stores Wilson Tree MeasureTheory
open Next.Fluctuations.Sector Next.SectorChange SectorNext.Vacuum.ReLog
open YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented Finset Inventory Almanac Presented
open Precision SectorNext.Remainder SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius YM.Push.SectorMeasure

variable {c f : Side} {G : Gauge} {x W : ℝ} {S : StepData c f} {T : Tube G S} {P : Teller G}
  {R : Rep G f} {D : Allocation G S x W} {F : Forest S.ratio} {V : Config G c}
variable {κ : ℝ}

def promote (T : Tube G S) (β x κ : ℝ) (O : Stores S) (V : Config G c) (k : S.Choices) (U : Config G f) :=
    Real.exp (β*meanEnergy O T x U k V - seed G S.patch.L x κ β O.shares)

-- useful also for probing absolute values at the Reader
lemma funded (h : Fits T R x) (hS : S.patch.Branches S.kernel G) (O : Stores S) (k : S.Choices)
    (hp : ∀ U, 0≤R.eval U) (a : F.Slice G) :
    touch F D R.beta V O (fun k U => promote T R.beta x κ O V k U * R.eval U) k a =
    earn S G x κ R.beta O.shares * sieve T R.beta x V *
      D.portion O F V (fun k a => ‖exposed R (till x) (F.drape a)‖ * leaves O T R.beta x k V (F.drape a)) k a := by
  let β := R.beta
  let U := F.drape a
  let B := D.bill O k U V
  let u := promote T β x κ O V k U
  let E := exposed R (till x) U
  have he : 0≤E := by unfold E; exact (expel R (till x) U).symm ▸ mul_nonneg (Real.exp_pos _).le (hp U)
  let f := sieve T R.beta x V
  change B * (taggedKernel S β k U V * (u * R.eval U)) = earn S G x κ β O.shares * f * (B * (‖E‖ * leaves O T β x k V U))
  rw [mul_left_comm (taggedKernel ..),show taggedKernel S β k U V * R.eval U = f * (E * enters T β x k V U) from use_gap h U k V,
    Real.norm_of_nonneg he,enters_eq hS O]
  have ht : u*Real.exp (-β*meanEnergy O T x U k V) = Real.exp (-seed G S.patch.L x κ β O.shares) := by
    unfold u promote; rw [← Real.exp_add]; ring_nf
  unfold earn
  rw [show -β*(κ*(fiery G x S.patch.L)^2*O.shares) = -seed G S.patch.L x κ β O.shares by unfold seed; ring,
    ← ht]; ring



lemma scale (h : Fits T R x) (hS : S.patch.Branches S.kernel G) (O : Stores S)
    (hp : ∀ U, 0≤R.eval U) :
    earn S G x κ R.beta O.shares * leftOver D F T R O V =
      amount F D R.beta V O (fun k U => promote T R.beta x κ O V k U * R.eval U) := by
  unfold leftOver Allocation.column tagTotal amount
  simp_rw [funded h hS _ _ hp, integral_const_mul]; rw [← mul_assoc, mul_sum]




end YM.AnalyticBridge.Sharp.Drain
