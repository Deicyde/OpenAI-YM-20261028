import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Span
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Instruments
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Embassy

/-!
# Split of the actual career. All veterans (atoms length at least 3,
 or ANY packet seed) keep their extension, including across reprojection.
 Supply F-fusion from the full kernel. `veteran` does not read any field,
 or (along Curve) change with β: we use the units identity, not a
 nontrivial permutation through the numerical buys.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i γ : ℝ} {k j n ℓ : ℕ}
    (p : BudgetPoint) (H : Cash W s μ L Q o α T I) {J : Cash W s μ L Q o α T R} (X : Alliance H J 1 0)
    (χ : Chi)

def senior (A : Magazine H) : Prop := A.elim (fun z => veteran H z) fun _=>False
-- filter before orbit average

def suitably (t : Magazine H) : Config G c→ℝ := t.elim (fun z=>if veteran H z then sequence H X χ z else 0) fun _=> 0

def spent (γ : ℝ) (t : Magazine H) := if senior H t then 0 else opus H X χ γ t
lemma pure (γ : ℝ) (t : Magazine H) : suitably H X χ t = if senior H t then opus H X χ γ t else 0 := by
  rcases t with t|t
  · dsimp only [Sum.elim_inl,senior,suitably]; split <;> simp [*,opus]
  exact (if_neg (fun h=> h : ¬ senior H (.inr t))).symm -- rewrite simpl


variable (N : Captain J j C' d v Y A b r B q k χ) (hp : p.threshold=Pressure.temp s) (hj : p.order ≤ j) (ht : p.B=radiusB s) (hz : preExponent p ≤ a)
    (hx : X.units=Equiv.refl _) {β : ℝ}
include hx hp hj ht hz N


-- price kept exactly early Local reserve. Available *on same p,post*. Receipt
-- still from original Listing. Does not claim replacing by itself gives integral.
omit hj N ht hx hz hp
def retain : Collection.Source G c := ⟨choir (suitably H X χ) ∘ pennant H,(plusone H X χ 0).hardRead⟩
def rest (γ : ℝ) : Collection.Source G c := ⟨choir (spent H X χ γ) ∘ pennant H,(plusone H X χ 0).hardRead⟩
lemma shade (γ : ℝ) (i : ℕ) :
    let t:=senior H (pennant H i).2; let f:= plusone H X χ γ
    (retain H X χ).logRead i=(if t then f.logRead i else 0) ∧
      (rest H X χ γ).logRead i=(if t then 0 else f.logRead i) := by
  intro t f
  unfold retain rest f plusone choir
  dsimp only [comp_apply];
  rw [pure H X χ γ,spent]; split_ifs <;> first | exact ⟨rfl,rfl⟩ | simp_all -- zero
end YM.PhysicalNext.Repeat.Height
