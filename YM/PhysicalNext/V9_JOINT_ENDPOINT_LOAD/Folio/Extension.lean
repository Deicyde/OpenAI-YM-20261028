import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Parlour
import YM.UVNext.COUPLING_RESET.Survival

/-! # Withdrawing the same-law support currency in the actual Clearance budget

Depth factors of paths charged PER OCCURRENCE. Remaining ancestor/log/row
costs are real operands' bills, not small by fiat. Needs the complete
physical dictionary, geometry and ancillary orders on this step/domain to
actually build a component. Doesn't discard tag/address metadata to reprice
an unindexed multiplier. No assumption of linear bound of path length by
a cover cost or growth-smallness of optional terms on unchecked V fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix Finset
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure
open AnalyticBridge.LocalGaussian Spot Spot.Programme Notice Reading Tariff
open MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {Q : Kiosk} {k n : ℕ} {θ E : ℝ} {d : Desk G S} {u : Spot d}
    {A : Stores S} {F : Forest S.ratio} {κ : S.Choices}
    {H R ι α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R]
    {X : Support c} {l : Viewport u X H R ι} {D : u.Slices} {b : Finset ℕ} {q : Programme D b} {z : q.Run α β γ}
    {a : Notice l} {B : Reading a z} {s : Seats l z} {M : Income α β γ (H⊕R)} {o : Site c} {j r : ℕ} {V : Config G c} {Ω : Set (Config G c)}

def commission (G : Gauge) := Real.exp 2*2^(2*Fintype.card G.ColorIndex)
def audited (v : Charges) (d : Desk G S) (k r : ℕ) (u : Paper f) := commission G * premiums v G d.betaHat (home S) (4*k) r u


def ancillary (s : Seats l z) (M : Income α β γ (H⊕R)) :=
  (∏ i,M.gate i) * (∏ i ∈ s.bigᶜ, M.wages i*Real.exp (M.wages i)) * Real.exp (M.yen + ∑ i∈M.bodyᶜ,M.spend i)

omit [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R] in
lemma ancillary_nn (s : Seats l z) (M : Income α β γ (H⊕R)) : 0 ≤ ancillary s M := mul_nonneg
    (mul_nonneg (Finset.prod_nonneg fun _ _=>M.gate_nn _) (Finset.prod_nonneg fun _ _=>mul_nonneg (M.wages_nn _) (Real.exp_pos _).le)) (Real.exp_pos _).le

namespace SeatsInvoice
omit [Fintype R] [DecidableEq β] [Fintype α] [Fintype β] in
lemma letter (s : Seats l z) (h : Limits Q.v S.patch G Q.cap d.betaHat) (j : s.big) : let T := hire s Q.v M o Q.L k θ Q.cap
    T.rents.wage j.val * (2:ℝ)^(T.sit j.val).card * (1+steps (s.issued j):ℝ)^(4*k) ≤ audited Q.v d k r (glyph s j) := by
  intro T; let x := s.stipend Q.v M j.val
  have he : x ≤ 1 := s.stipend_le Q.v M h j
  have hv : 0≤x := s.stipend_nn Q.v M j.val
  have hw : T.rents.wage j.val = x*Real.exp (x+x^2) := if_pos j.property
  have ht := mul_le_mul_of_nonneg_left (Real.exp_monotone (show x+x^2 ≤ 2 by nlinarith)) hv
  let C:=Fintype.card G.ColorIndex
  have hl : (T.sit j.val).card ≤ 2*C := by
    rw [show T.sit j.val=s.sits j.val from rfl,s.sits_big j,card_product,card_univ]; gcongr; exact card_le_two
  have hy : award Q.v G (home S) d.betaHat (glyph s j) = x := (reprint ..).trans
    (show award Q.v G site d.betaHat (s.issued j)=_ from (award_pay (s.issued j)).symm.trans (s.stipend_big Q.v M j).symm)
  have hz : (1+steps (s.issued j):ℝ) ≤ (plan (home S) r (glyph s j):ℕ) := by
    unfold plan; have hz : steps (glyph s j)=steps (s.issued j) := by unfold glyph upwards; cases s.issued j <;> rfl
    exact_mod_cast (by rw [hz,add_comm]; exact Nat.le_mul_of_pos_right _ (by omega) : 1+steps (s.issued j) ≤ _)
  rw [hw]; unfold audited commission premiums; rw [hy]
  calc
    _ ≤ (x*Real.exp 2) * 2^(2*C) * ((plan (home S) r (glyph s j):ℝ)^ (4*k)) := by gcongr; norm_num
    _ = _ := by unfold C; ring




end SeatsInvoice
end YM.PhysicalNext.JointLoad.Folio
