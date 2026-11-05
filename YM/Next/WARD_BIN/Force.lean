import YM.Next.WARD_BIN.Rays
import YM.Next.WARD_BIN.Stencils
import YM.Work.G06.TurnSlot


/-!
# A genuine Euler cylinder family before calibration

Multilinear version. Two panels, one (recall) with complete linear response on radial
connection data, the other with the divergence samples. Take a difference of powers on
these nonlinear readouts. Pay scalar products and charge each *positive* edge before
any translations; at the pole the response will be block-triangular in the desired
weighted projections (see separate projection analysis). Here we build the X coefficients
and prove the *exact* Wilson law relation it affords (not dropping partners,
and even the unit correlations). Next to ``.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Work.G07 Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {H : Hol G} {d j : ℕ}

lemma Affordable.clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {S : Finset Cover} {k : ℤ} (x : CoverConfig G → E →L[ℝ] F) (h : ∀ e, Affordable S k fun U => x U e) :
    Affordable S k x := by
  classical
  let b := Module.finBasis ℝ E
  let I := Fin (Module.finrank ℝ E)
  let f := fun i : I => (ContinuousLinearMap.smulRightL ℝ E F ((b.coord i).toContinuousLinearMap))
  have he (U) : x U = ∑ i:I,f i (x U (b i)) := by
    ext1 q; rw [sum_apply]
    conv_lhs => rw [← b.sum_repr q]
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => map_smul ..
  rw [funext he]; exact Affordable.sum _ (fun i U => f i (x U (b i)))
    fun i _ => (h (b i)).postcomp _

lemma Affordable.array {I F : Type*} [Fintype I] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Finset Cover} {k : ℤ} (x : I → CoverConfig G → F) (h : ∀ i, Affordable S k (x i)) :
    Affordable S k fun U i => x i U := by
  classical
  let v := fun i : I => ContinuousLinearMap.single ℝ (fun _ : I => F) i
  have he (U : CoverConfig G) : (∑ i : I, v i (x i U)) = fun i => x i U := by
    funext i; rw [Finset.sum_apply]; exact Fintype.sum_pi_single i _
  rw [← funext he]; exact sum _ (fun i U => v i (x i U)) fun i _ => (h i).postcomp _

namespace Rays
variable (R : Rays G d H)

/-- Slot and Euler panels. -/
def guess (U : CoverConfig G) := R.read (Bid.mapped R.slots U)
def gap (U : CoverConfig G) := R.lifts fun e => sample e.val U
def origin (A : Snap G d) := fun i => A i - R.T i (A i)

lemma guess_gauge (t : Cover → G.El) (U : CoverConfig G) : R.guess (Lattice.gauge t U) = Cast (t 0) (R.guess U) := by
  unfold guess
  rw [← R.cov]; apply congr_arg R.read; exact funext (fun i => Work.G06.slot_gauge ..)

lemma gap_gauge (t : Cover → G.El) (U : CoverConfig G) : R.gap (Lattice.gauge t U) = Cast (t 0) (R.gap U) := by
  unfold gap; simp_rw [sample_gauge]; exact R.eqv _ _

/-- Send the positive bond force through transport and resolution. -/
def pays (U : CoverConfig G) (e : R.edg) : G.Color →L[ℝ] Snap G d :=
  (R.lifts.comp (ContinuousLinearMap.single ℝ (fun _ : R.edg => G.Color) e)).comp
    (G.adjoint (toBond e.val U)).toContinuousLinearMap

lemma pays_rule (U : CoverConfig G) (e : R.edg) (a) : R.pays U e a = R.lifts (Pi.single e (G.adjoint (toBond e.val U) a)) := rfl

lemma pays_gauge (t : Cover → G.El) (U : CoverConfig G) (e : R.edg) (a) :
    R.pays (Lattice.gauge t U) e (G.adjoint (t e.val.1) a) = Cast (t 0) (R.pays U e a) := by
  simp only [pays_rule,← R.eqv,toBond,travel_gauge,route_end,← G.adjoint_mul, inv_mul_cancel_right]
  apply congr_arg R.lifts; funext i
  by_cases h : i=e
  · subst i; simp [G.adjoint_mul]
  simp [h]

lemma payGap (U : CoverConfig G) : (∑ e:R.edg, R.pays U e (euler U e.val)) = R.gap U := by
  simp_rw [pays_rule,← map_sum]
  apply congr_arg R.lifts; funext i; rw [Finset.sum_apply]
  exact Fintype.sum_pi_single i _
end Rays

section multi
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def phased (x y : E) (m : ℕ) (i : Fin j) : E := if i.val < m then x else y

def factor (M : Tensor.T E F j) (x y : E) (i : Fin j) := M.toContinuousLinearMap (phased x y i.val) i

lemma factor_apply (M : Tensor.T E F j) (x y : E) (i : Fin j) (z) : factor M x y i z=M (update (phased x y i.val) i z) := rfl

lemma factor_total (M : Tensor.T E F j) (x y : E) :
    (∑ i:Fin j,factor M x y i (x-y)) = Tensor.diagonal M x - Tensor.diagonal M y := by
  let p := fun i : ℕ => M (phased x y i)
  have hh (i : Fin j) : factor M x y i (x-y) = p (i.val+1) - p i.val := by
    rw [factor_apply,M.map_update_sub]; unfold p
    rw [show update (phased x y i.val) i y = phased x y i.val by
      funext k; by_cases h:k=i
      · subst k; simp [phased]
      exact update_of_ne h ..]
    congr 2; funext k; by_cases h:k=i
    · subst k; simp [phased]
    rw [update_of_ne h]; unfold phased
    simp only [show k.val < i.val+1 ↔ k.val < i.val by have h := Fin.val_ne_of_ne h; omega]
  simp_rw [hh]
  rw [Fin.sum_univ_eq_sum_range (fun t => p (t+1)-p t), Finset.sum_range_sub]; unfold p Tensor.diagonal
  rw [show phased x y j = (fun _ : Fin j => x) from funext fun i => if_pos i.isLt,
    show phased x y 0 = (fun _ : Fin j => y) from funext fun i => if_neg (by omega)]
end multi

namespace Rays
variable (R : Rays G d H)
variable (M : Tensor.T (Snap G d) ℂ (j+1))

def coField (e : R.edg) (U : CoverConfig G) : Covector G :=
  ∑ i : Fin (j+1), (factor M (R.guess U) (R.guess U-R.gap U) i).comp (R.pays U e)

def force (U : CoverConfig G) := Tensor.diagonal M (R.guess U) - Tensor.diagonal M (R.guess U-R.gap U)

def compression (U : CoverConfig G) := ∑ e : R.edg, divergence e.val (R.coField M e) U

def unpaid (β : ℝ) (U : CoverConfig G) := R.force M U - (β:ℂ)⁻¹ * R.compression M U

lemma force_eq (U : CoverConfig G) : R.force M U = ∑ e:R.edg, R.coField M e U (euler U e.val) := by
  classical
  let x := R.guess U; let y := R.guess U-R.gap U
  change Tensor.diagonal M x-Tensor.diagonal M y= _
  rw [← factor_total]
  unfold coField; simp only [sum_apply, ContinuousLinearMap.comp_apply]; rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ (α:=Fin (j+1)))]
  apply Finset.sum_congr rfl; intro i _
  rw [show x-y = ∑ e:R.edg, R.pays U e (euler U e.val) by rw [R.payGap]; unfold x y; abel, map_sum]

lemma unpaid_eq (β : ℝ) (U) : R.unpaid M β U = ∑ e:R.edg,equation β e.val (R.coField M e) U := by
  simp_rw [unpaid, R.force_eq,compression,equation,Finset.mul_sum,Finset.sum_sub_distrib]

/-- Invariance of the tensor contraction (complex coefficients; act on real inputs). -/
def covariantTensor (M : Tensor.T (Snap G d) ℂ (j+1)) := ∀ (u : G.El) a,M (fun i => Cast u (a i))=M a

lemma coField_gauge (h : covariantTensor M) (e : R.edg) : Covariant e.val (R.coField M e) := by
  intro a t U
  unfold coField; simp only [sum_apply, ContinuousLinearMap.comp_apply, R.pays_gauge, factor_apply, R.guess_gauge, R.gap_gauge]
  apply Finset.sum_congr rfl; intro i _
  refine Eq.trans (congr_arg M ?_) (h (t 0) _)
  let x := R.guess U; let y := R.gap U
  have he : Cast (t 0) (x-y)=Cast (t 0) x-Cast (t 0) y := funext (fun j => map_sub _ (x j) (y j))
  funext j; by_cases h : j=i
  · subst j; simp
  rw [update_of_ne h, update_of_ne h]; unfold phased; split
  · rfl
  exact he.symm
end Rays
end YM.WardBin
