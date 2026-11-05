import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Current
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Prescription
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Scroll
import YM.UVNext.COUPLING_RESET.Regular



/-!
# Keeping the precise scalar as E and K are manufactured

This is where `β` **stays** on the coarse base term. Keep a second perspective of K
using the very same conjoined addresses and τ, to handle also the `quadraticMask` API
(mask discrepancy is real, with its own attaching contribution). Nothing fitted to a value
of an evaluator or a trial β.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas.Hangar
open RG Lattice Wilson Function Filter Finset SectorNext.Reconnect
open AnalyticBridge.CouplingShape AnalyticBridge.VerifiedReset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {ι κ : Type} [Countable ι] [Countable κ]

inductive Reading
| returnMask
| shapeMask

def Reading.invoice (s : Reading) (α : ℝ) := match s with
  | .returnMask => 0
  | .shapeMask => α

variable (p : BudgetPoint) (M : Pane G n ι κ) (R : PathData G) (c : Clip)

def Reading.scope (R : PathData G) (c : Clip) (p : BudgetPoint) (V : Config G n) (s : Reading) : ℝ := match s with
  | .returnMask => Collection.receipt R c p V
  | .shapeMask => quadraticMask R c p V

def atrium : Plate n := (Scroll.upcoming M).combine (Prescription.stock n R p)

variable (F : Palette G n ι κ)
def imprint (β α : ℝ) : (atrium p M R).Ink G :=
  Sum.elim (Scroll.up M F) (Prescription.desire n R c p β α)

/-- True per-coarse-site normalization including the offset from every log cluster.
On the unforced gas this uses real signed cluster coefficients. -/
def earnings (r : ℝ) := (Real.log r + ∑' i, Scroll.star M F i) / (Fintype.card (Site n))

variable {p M R} {Q : Plate n} (T : Tape G p (atrium p M R) Q)

/-- Even the dormant perspective-change labels are exposed in BOTH. -/
def errors := T.signed.combine (TwoMasks.slips R p n)

def receipts (s : Reading) (β α : ℝ) : (errors T).Ink G :=
  Sum.elim (T.bill (imprint p M R c F β α)) (TwoMasks.ticket R c p (s.invoice α))

def printed := (Scroll.lowland p M).combined (errors T) p

def marked (s : Reading) (β α : ℝ) : (printed T).Ink :=
    (Scroll.lowland p M).filled (errors T) p (Scroll.still p M F) (receipts c F T s β α)

def pooled (β α : ℝ) : Q.Ink G := T.finalPlate (imprint p M R c F β α)

def fair (s : Reading) (β α τ : ℝ) (V : Config G n) : ℝ :=
  τ*Fintype.card (Site n) - R.inChannels c p β V - α*s.scope R c p V -
    ∑' i,Q.maskedLog p (pooled c F T β α) V i

variable {c F} {σ C Λ : ℝ} (h : R.Bounds c σ C Λ)
    (hs : OriginalLight p M F) {b : BidLog ι κ} (he : b.Negative p M F)
include h hs he

omit he [Countable κ] in
lemma safe (β α : ℝ) : (atrium p M R).sound (imprint p M R c F β α) p := by
  rintro (i | i)
  · exact Scroll.wellLit hs i
  exact Prescription.permits h β α i

omit hs in
lemma settled (β α : ℝ) : (atrium p M R).Pattern (imprint p M R c F β α) p := by
  let v := Scroll.fuel M b
  let u := Prescription.stamps n R c ‖β‖ ‖α‖
  have hc : (Scroll.upcoming M).ward (Scroll.up M F) p v := Scroll.log_cap he
  have hh : (Prescription.stock n R p).ward (Prescription.desire n R c p β α) p u :=
    fun i V _ => Prescription.desires le_rfl le_rfl i V
  exact ⟨_,Plate.ward_combine hc hh,Summable.sum _ (Scroll.summation he.offers).1 (Prescription.stamp_income h ..)⟩

omit hs h in
lemma paired (V : Config G n) (r : ℝ) (hr : 0<r) (R : PathData G) (c : Clip) (β : ℝ) :
    let u := (Scroll.upcoming M).maskedLog p (Scroll.up M F) V
    let income := earnings M F r * Fintype.card (Site n) - β * hub R c p V
    Real.exp (-β*hub R c p V)*r*(∑' i,M.initial p F V i) = Real.exp (income - ∑' i,u i) *
      ∑' i,(Scroll.lowland p M).sell p (Scroll.still p M F) V i := by
  intro u income
  have ht := (Scroll.lifted he V).2.2.2
  rw [ht,← mul_assoc]; congr 1
  -- factors from Return.rate include r>0
  unfold income earnings
  rw [div_mul_cancel₀ _ (by positivity)]
  conv_lhs => arg 1; arg 2; rw [← Real.exp_log hr]
  rw [← Real.exp_add,← Real.exp_add]; unfold u; ring_nf

omit hs in
lemma summarize (β α : ℝ) (V : Config G n) :
    let u := (Scroll.upcoming M).maskedLog p (Scroll.up M F) V
    ∑' i,(atrium p M R).maskedLog p (imprint p M R c F β α) V i =
      (∑' i,u i) + (β * hub R c p V - R.inChannels c p β V - α * Collection.receipt R c p V) := by
  intro u
  obtain ⟨hi,ht⟩ := Prescription.quoted (p:=p) h V β α
  have hh := (Scroll.lifted he V).2.1
  rw [← ht]
  exact Summable.tsum_sum
      (f:=fun i : (Scroll.upcoming M).letter ⊕ (Prescription.stock n R p).letter =>
        (atrium p M R).maskedLog p (imprint p M R c F β α) V i) hh.of_norm hi.of_norm

omit h he in
lemma shield (s : Reading) (β α : ℝ) (H : (atrium p M R).sound (imprint p M R c F β α) p) :
    Q.sound (pooled c F T β α) p ∧
    (errors T).Lands p (receipts c F T s β α) ∧
    (printed T).Tenants p (marked c F T s β α) := by
  obtain ⟨ha,hb,hc⟩ := T.shielded H
  refine ⟨ha,Slip.Lands.append hb (TwoMasks.spends R c p (s.invoice α)),?_⟩
  exact (Scroll.lowland p M).sheltered _ _ (Scroll.verified hs)
    (Slip.Vouched.append hc (TwoMasks.routes R c p (s.invoice α)))


end YM.PhysicalNext.PreAtlas.Hangar
