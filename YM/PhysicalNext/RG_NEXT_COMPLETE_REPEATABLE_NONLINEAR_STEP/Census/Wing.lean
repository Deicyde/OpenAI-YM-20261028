import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Revenue
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Tryouts

/-! # Extra grades on Career: the hull. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i n' : ℝ} {k j n ℓ : ℕ}
    {H : Cash W s μ L Q o α T I} {J : Cash W s μ L Q o α T R} (χ : Chi)
    {hp : I.path=R.path} {hα : I.activities.reg=R.activities.reg} {hA : I.activities.forced=R.activities.forced}
    (u : Alliance H J 1 0)
include hp hα hA
lemma odors (p : Molecule S) : H.shapeW p=J.shapeW p := by
  change setPrice H.supportP _ _ _=setPrice J.supportP _ _ _
  have hB : I.p.B=R.p.B := H.laws.intake.sizes.trans J.laws.intake.sizes.symm
  have he : Mixed.lengths S H.faresP (ConnectedActivityE6.lengths T I) = Mixed.lengths S J.faresP (ConnectedActivityE6.lengths T R) := by
    funext i; rcases i with i|i; · rfl
    change ConnectedActivityE6.lengths T I i=ConnectedActivityE6.lengths T R i
    unfold ConnectedActivityE6.lengths
    rw [show forcedExtra I=forcedExtra R from funext fun v=> by unfold forcedExtra; rw [hA,hB]]
    suffices he:exCharge T I=exCharge T R by rw [he]
    unfold exCharge Raw.extra; rw [hp,show regularExtra I=regularExtra R from funext fun v=> by unfold regularExtra; rw [hα,hB]]
  rw [he,same_area (J:=J) hp hα hA]
lemma stilled (hz : u.units=Equiv.refl _) (p : H.fragrances) : tired H p↔tired J (u.furrow p) := by
  rcases p with ⟨m,k⟩
  have hx i : ((u.furrow ⟨m,k⟩).snd i).val=(k i).val:= by change u.units _=_; rw [hz]; rfl
  unfold tired degree depth acme breadth overlap; simp only [hx, odors (J:=J) (H:=H) (hp:=hp) (hα:=hα) (hA:=hA)]; exact Iff.rfl

variable (p : BudgetPoint)


-- actual remaining case. Every surviving u vertex neighborhood excludes seeds in Z
-- and patches not in δ cost. U= log letters with no ratio or tail. E can only stand
-- alone. Prove as a finite cardinal/shape certificate without assuming birth.
omit hp hα hA
structure Novice (J : Cash W s μ L Q o α T R) (z : J.fragrances) : Prop where
  enter : trio J z
  length : depth J z < Pressure.Stores.till s
  arity : degree J z ≤ 2

lemma novices (z : J.fragrances) (V : Config G c) (h : stream J χ V z ≠ 0) (he : ¬ tired J z) : Novice J z := by
  obtain ⟨hy,hx,hd⟩ := (and_congr Iff.rfl not_or |>.1 (not_or.mp he))
  have hz: ¬veteran J z:= not_or.mpr ⟨fun hp=>hy (hp.trans (Nat.le_add_left ..)),hx⟩
  exact ⟨excited χ z hz V h,lt_of_not_ge hd,Nat.le_of_lt_succ (lt_of_not_ge hy)⟩

include hp hα hA

end YM.PhysicalNext.Repeat.Height
