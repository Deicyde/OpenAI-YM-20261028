import YM.Next.WARD_BIN.Deposit
import YM.Next.WARD_BIN.Wake
import YM.Next.WARD_BIN.Wheels

/-!
# Snapshot of real singleton at its ancestry

Use template for compiling each *individual* repetition. High data have no
choice in these slots: populate from true step-to-step signals, with all
required rotations and star. Regular charge/canonical stamp always on THEIR
supports, unit alone outside at each level. No Pi/transport hypotheses on
Duet silently inferred: accompany solo with its actual shipment receipts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Finset MeasureTheory Lattice Wilson RG Source Gas Wheels Lies
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {n : Side} {l k m p d N : ℕ} {X Y F : Type*} {W : History G} {R : Rep G n} {o b : Site n} {bp : BudgetPoint} {S : Support n} {s : Signed} {c u v w a d' κ' : ℝ}

lemma purse_unit {g : X → ℝ} (hv : 0≤v) (hf : SumBudget g u) : SumBudget (fun i => v*g i) (v*u) :=
  ⟨fun i => mul_nonneg hv (hf.1 i),hf.2.1.mul_left _, by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hf.2.2 hv⟩
lemma purse_mono {g : X → ℝ} (hv : u ≤ v) (hf : SumBudget g u) : SumBudget g v := ⟨hf.1,hf.2.1,hf.2.2.trans hv⟩
lemma purse_roll (e : X ≃ Y) {f : Y → ℝ} {g : X → ℝ} (hg : SumBudget g v) (ht : f ∘ e=g) : SumBudget f v := by
  subst g; exact ⟨fun i => (e.apply_symm_apply i) ▸ hg.1 (e.symm i), e.summable_iff.mp hg.2.1,
    (e.tsum_eq _).symm.trans_le hg.2.2⟩
lemma purse_low {f g : X→ℝ} (hg : SumBudget g v) (hv : ∀ i, 0 ≤ f i) (hh : ∀ i,f i≤g i) : SumBudget f v :=
  let h:=hg.2.1.of_nonneg_of_le hv hh; ⟨hv,h,(h.tsum_le_tsum hh hg.2.1).trans hg.2.2⟩

section Linear
variable {f g : Config G n → ℂ}








end Linear

structure Rib (G : Gauge) (n : Side) where
  head : ℂ
  root : Site n
  annals : ℕ → Support n
  body : ℕ → Config G n→ℂ
  band : ℕ → Config G n → ℂ

namespace Rib
variable {F : Labels.Frame G d} (Q : Rib G n)

structure Pitched (R : Rep G n) : Prop where
  supports i : Q.root∈Q.annals i
  color i : R.p.Regular (Q.annals i) (Q.body i)
  tails i : Kept R.p (R.activities.forced i) {Q.root} (Q.band i)

/-- Evaluate budgets at the actual radius, κ remains explicit. -/
structure Rents (R : Rep G n) (w c κ : ℝ) : Prop where
  unit : w*‖Q.head‖ ≤ c
  width : ∃ e : ℕ → ℝ,(∀ i,R.p.supBounds Q.root (Q.annals i) (Q.body i) (e i)) ∧
    SumBudget (fun i => w*R.p.mass (Q.annals i) (e i)) c
  bead : ∃ e : ℕ → ℝ,(∀ i,0≤e i ∧ ∀ U, ‖Q.band i U‖ ≤ e i) ∧
    SumBudget (fun i => w*R.p.mass (R.activities.forced i).support (e i)) (κ*c)

def fares (R : Rep G n) (U : Config G n) := Q.head + ∑' i, masked R.p.threshold (Q.annals i) (Q.body i) U



variable {H : Hol G} {D : SectionData F} (P : Coefficient F n)

def single (P : Coefficient F n) (o : Site n) (D : SectionData F) (bp : BudgetPoint) : Rib G n :=
  { head := P.x 0, root := o, annals := fun i => match i with
    | 0 => D.footprint o
    | i+1 => P.support i,
    body := fun i => match i with
    | 0 => D.places (F.scaled bp.threshold⁻¹ (F.core P.x)) o
    | i+1 => P.regular i,
    band := P.forced }







def cross {A : Activities G n} (Q : Rib G n) {s : Signed} {b} (J : A.Moves s b) (r : Bool) : Rib G n :=
  { head := turn r Q.head, root := affine s b Q.root
    annals := fun i => (Q.annals i).image (affine s b)
    body := fun i => turn r ∘ Q.body i ∘ pull s b
    band := fun i => turn r ∘ Q.band (J.kp.symm i) ∘ pull s b }

variable (J : R.activities.Moves s b) (r : Bool)







end Rib
end YM.WardBin
