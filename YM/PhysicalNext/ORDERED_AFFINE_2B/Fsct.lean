import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Confirmed
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Currency
import YM.Extra.MULTISOURCE_TRAJECTORIES.Hangers
import YM.PhysicalNext.ORDERED_AFFINE_2B.Arrivals
import YM.PhysicalNext.ORDERED_AFFINE_2B.TellerBook

/-!
# Issue Fsct on the ActualScalar page, as ordered letters

Includes relative scalar prefactor (keep the SAME common tag decision and
precisions, and the subtraction order). Integrated tails of LOG A pair
spend separately, local-log entries paired on the true address/window in
both tables. Line test of Track.Record on the WHOLE alphabet, not only
active loops and not multiplying by the COMMON-sector labels more than
required. Calls Cargo's true invoice on each `p`; cover exponent paid in
output currency. Frozen counts over original hold addresses, not padded
by fictitious charges independent of the tree/free card. Region and tag
locality before this file; this is an extensive identity not a global
support/rate bound on the torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Whole.Fsct
open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree
open AnalyticBridge AnalyticBridge.ResetIncome SectorTools.ActualScalar SectorNext.Vacuum
open Next Next.Foundations Next.SectorChange
open ProjectorNext.Equivariance (HasOrderAt)
open Further Further.CurvedGaussianJets Jets ChangeV Tracks MeasureTheory Set
open Push.SectorMeasure Matrix Book
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {V : Config G c} {k : S.Choices}
  {T : Tube G S} {x σ : ℝ} {J : Tab} {n q : ℕ} {l : Word G c} {e : Plate G S}

lemma any_due (S : StepData c f) (l : Word G c) (q : ℕ) : ∃ z : ℝ, 0 ≤ z ∧ ∀ i∈l,Due S.ratio.embed 0 q z i := by
  induction l with
  | nil => exact ⟨1,zero_le_one,by simp⟩
  | cons i l ih =>
    obtain ⟨z,hz,he⟩ := ih
    refine ⟨‖i‖+z,add_nonneg (norm_nonneg _) hz,?_⟩
    intro j hj p; unfold cap; rcases List.mem_cons.mp hj with rfl|hj
    · apply le_trans (norm_le_pi_norm _ p)
      refine le_trans (le_add_of_nonneg_right hz) (le_mul_of_one_le_right (add_nonneg (norm_nonneg _) hz) (one_le_pow₀ ?_)); simp
    apply le_trans (he j hj p); unfold cap; gcongr; exact le_add_of_nonneg_left (norm_nonneg _)

def wage (e : Plate G S) (R : Rep G f) (A : Stores S) := -(Fintype.card (Frozen A e.x e.forest) : ℝ) * Real.log (Next.SectorChange.spare e.chart R.beta)

-- Ordered left reads at one station; not commuting charts.
section entries
variable {I : Type*} [Fintype I] [DecidableEq I] (W : Windows I) (X : Jets.Field G c I) (J : Tab)
  (l : Word G c) (V : Config G c) (i : I)
def localLap := leftDerivs (fun v=> W.tollLine (X v) J.v.mass i) l V

def resumed := ∑' d, ∑ p : Run I (d+2), ends i i p (leftDerivs (mailed W X p) l V)
def pushed := ∑' d, ∑ p : Run I (d+1), ends i i p (leftDerivs (pushLog W X p) l V)
end entries

/-- Apply to the residual minus and plus priceLine contributions.
Keep general f for using with literal terms on a lift. -/
private theorem composed {B : Type} [Fintype B] [DecidableEq B] (W : Windows B) (C : Bool → Jets.Field G c B) (J : Tab)
    (wage' : ℝ) {F : Config G c → ℝ} {a : B → Site f} {P : Directions G c → Prop} {M K : ℝ} {N}
    {s : Weights a} (h : ∀ y : Bool, ∀ᶠ U in 𝓝 V, Street J.v s n P (C y) U M)
    (hb : W.Includes a N) (he : Port J.v s n M K N)
    (hg : ∀ᶠ U in 𝓝 V, F U = wage' -(1/2:ℝ)*(Real.log (C true U).det - Real.log (C false U).det)+
      (1/2:ℝ)*(Real.log (C true U).det+Real.log (Jets.covariance W (C true) U).det))
    (hl : l.length ≤ n) (hp : ∀ i∈l,P i) :
    leftDerivs F l V = (if l=[] then wage' else 0) + ∑ i,
      ((-(1/2)) * ((localLap W (C true) J l V i-resumed W (C true) l V i) - (localLap W (C false) J l V i-resumed W (C false) l V i)) + (1/2) * pushed W (C true) l V i) := by
  have hs y := (h y).eventually_nhds.mono fun U hh=> he.read hh hb
  let t := price (C true) J.v; let b := price (C false) J.v; let r i (v : Config G c) := Round.onLine (Jets.coeff W (C true) v) i
  let I := Unit ⊕ (B ⊕ (B ⊕ B)); let lot : I → Config G c → ℝ := Sum.elim (fun _ _=> wage') (Sum.elim t (Sum.elim b r))
  let a : I → ℝ := Sum.elim (fun _=> 1) (Sum.elim (fun _=>-(1/2)) (fun _=>1/2))
  have ht (i : I) : Within P n (lot i) V := by
    have hh (y : Bool) (i : B) := Book.payroll hb he (h y) i
    rcases i with _|i|i|i
    · exact Book.allowed contDiffAt_const
    · exact (hh true i).1
    · exact (hh false i).1
    exact (hh true i).2.2
  have hx := (Within.coin a lot ht hl hp)
  have hu : F =ᶠ[𝓝 V] (fun U=> ∑ i, a i*lot i U) := by
    filter_upwards [hg,hs true,hs false] with U hu hA hB
    rw [hu,hA.reference,hA.precision,hB.precision]
    unfold lot I; simp_rw [Fintype.sum_sum_type]; unfold a r b t
    simp only [one_mul,Fintype.sum_unique,Sum.elim_inl,Sum.elim_inr,← Finset.mul_sum]; ring
  rw [Jets.left_on hu,hx]
  have hE (i : B) := ((hs true).self_of_nhds).assemble l hl hp i i
  have hF (i : B) := ((hs false).self_of_nhds).assemble l hl hp i i
  -- finite linearity of left-word; use per-leg TRUE integral deriv prices
  unfold I lot; simp only [Fintype.sum_sum_type,a,Sum.elim_inl,Sum.elim_inr,one_mul,Fintype.sum_unique, Work.G07.left_const]
  unfold t b r; unfold localLap resumed pushed
  simp_rw [(hE _).1, (hE _).2.1, (hF _).1,← Finset.sum_add_distrib]; congr 1
  refine Finset.sum_congr rfl fun i _=> ?_
  ring

namespace Plate
variable (hd : Delivery J q n σ e) (he : Doors e) (h : J.Ships q n σ e.tube e.forest A k e.x V) (R : Rep G f)
include h

private lemma receipt : let W := windows S G e.x h.tall; let C:=stack e.tube e.x A e.forest k
    ∀ᶠ U in 𝓝 V, Real.log (e.Cov A U k).det = Real.log (Jets.covariance W (C true) U).det ∧
      Real.log (e.Gram A U k).det = Real.log (C true U).det ∧
      Real.log (1+(e.Gram A U k*e.Cov A U k-1)).det = Real.log (C true U).det+Real.log (Jets.covariance W (C true) U).det := by
  intro W C
  filter_upwards [h.retained,h.receiving true 0 zero_le_one] with U hu hU
  have hx : e.Cov A U k = Fixed.covariance e.tube e.x A e.forest k U := rfl
  have hC : (e.Cov A U k).det=(Jets.covariance W (C true) U).det := Eq.trans (det_back _ _ _ _).symm (congr_arg _ hu.1.symm)
  have hA : (e.Gram A U k).det=(C true U).det := (det_back e.x A e.forest (e.Gram A U k)).symm.trans (congr_arg _ (plinth ..).symm)
  rw [show 1+(e.Gram A U k*e.Cov A U k-1) = e.Gram A U k * e.Cov A U k by abel, Matrix.det_mul,hC,hA,
    Real.log_mul hU.full.pos.det_pos.ne' hU.positive.det_pos.ne']
  exact ⟨rfl,rfl,rfl⟩



include he hd

/-- Exact derivative read in any directions l (incl empty list). Apply
Currency to cover-normalized applications. Grouping a Run in `∑'
ℕ` with all positions at that length; `sent` bounds even absolute
hit-normalized entries ungrouped at each length, so not proposing a
compiler based on conditionally convergent log sums. In the enclosing
consumer THEN use `Bought.windows` etc. at legal data with exact
`chargeOut`. Uses true CGJ prices J.v per line, not naming a `nearby`
expense with incompatible parameters.
-/
theorem epoch (hl : l.length ≤ n) :
    let W:=windows S G e.x h.tall; let C:=stack e.tube e.x A e.forest k
    leftDerivs (fun U => e.cost R A U k) l V = (if l=[] then wage e R A else 0)+ ∑ i,
      ((-(1/2)) * ((localLap W (C true) J l V i-resumed W (C true) l V i) - (localLap W (C false) J l V i-resumed W (C false) l V i)) + (1/2) * pushed W (C true) l V i) := by
  intro W C
  obtain ⟨z,hz,hp⟩ := any_due S l q
  apply composed (W:=W) (C:=C) J (wage e R A) (h:=fun y=> h.street_cost y 0 hz) (spent S G e.x h.tall).1 (h.port 0 hz) _ hl hp
  filter_upwards [receipt h] with U hu
  have hh : Real.log e.Flat.det=Real.log (C false U).det := congr_arg _ (price_reference hd he k).symm
  unfold AnalyticBridge.ResetIncome.Plate.cost; rw [hu.2.1,hh,hu.2.2]; rfl
end Plate
end YM.PhysicalNext.OrderedAffine2B.Whole.Fsct
