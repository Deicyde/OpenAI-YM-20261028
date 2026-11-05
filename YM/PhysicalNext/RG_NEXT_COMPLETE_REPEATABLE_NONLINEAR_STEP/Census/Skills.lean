import YM.Further.STRONG_STARTUP_CREDIT.Launch
import YM.PhysicalNext.FLAT_PUSH_RESPONSE.GaussianTarget
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Instruments
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Embassy
import YM.PhysicalNext.UNMASKED_THROUGH_LAUNCH.Dome
import YM.Planned.ATOM_GUARDED_LAYOUT.Orbit
import YM.Planned.RECIPE_STARTUP_PORT.Horizon


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

variable (U : H.fragrances → Prop)
def chosen (A : Magazine H) : Prop := A.elim (fun z => U z) fun _=>False
-- filter before orbit average

def skilled (t : Magazine H) : Config G c→ℝ := t.elim (fun z=>if U z then sequence H X χ z else 0) fun _=> 0

def lower (γ : ℝ) (t : Magazine H) := if chosen H U t then 0 else opus H X χ γ t
lemma pivot (γ : ℝ) (t : Magazine H) : skilled H X χ U t = if chosen H U t then opus H X χ γ t else 0 := by
  rcases t with t|t
  · dsimp only [Sum.elim_inl,chosen,skilled]; split <;> simp [*,opus]
  exact (if_neg (fun h=> h : ¬ chosen H U (.inr t))).symm -- rewrite simpl

variable (N : Captain J j C' d v Y A b r B q k χ) (hp : p.threshold=Pressure.temp s) (hj : p.order ≤ j) (ht : p.B=radiusB s) (hz : preExponent p ≤ a)
    {β : ℝ}
include U hp hj ht hz N


-- price kept exactly early Local reserve. Available *on same p,post*. Receipt
-- still from original Listing. Does not claim replacing by itself gives integral.
omit hj N ht hz hp
def serve : Collection.Source G c := ⟨choir (skilled H X χ U) ∘ pennant H,(plusone H X χ 0).hardRead⟩
def sleeping (γ : ℝ) : Collection.Source G c := ⟨choir (lower H X χ U γ) ∘ pennant H,(plusone H X χ 0).hardRead⟩
lemma bolted (γ : ℝ) (i : ℕ) :
    let t:=chosen H U (pennant H i).2; let f:= plusone H X χ γ
    (serve H X χ U).logRead i=(if t then f.logRead i else 0) ∧
      (sleeping H X χ U γ).logRead i=(if t then 0 else f.logRead i) := by
  intro t f
  unfold serve sleeping f plusone choir
  dsimp only [comp_apply];
  rw [pivot H X χ U γ,lower]; split_ifs <;> first | exact ⟨rfl,rfl⟩ | simp_all -- zero
end YM.PhysicalNext.Repeat.Height
