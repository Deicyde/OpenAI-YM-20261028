import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Jets
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.LocalLedger
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Rainy
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Bingo

/-!
# Deformation of sector inside integral along real β

Scaling **all** Air f including inactive, no changing Measure gadget without Jacobian. Keeps worldZ physical U point, Atmos & μ, β(C/R') ratio follows pay roots. This is fixed period comparison registration only, not quantitative seam Hessian/G estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {u d p β ε A W : ℝ} {R R' : RG.Rep G f} {x : Coat T F}
structure Facing (R R' : RG.Rep G f) : Prop where
  params : R.p=R'.p
  clip : R.clip=R'.clip
  path : R.path=R'.path
  forced : R.activities.forced=R'.activities.forced
  reg : R.activities.reg=R'.activities.reg
  pos : 0<R.beta
  pos' : 0<R'.beta
variable (P : Facing R R')
def low (R R' : RG.Rep G f) := Coat.gStep R.beta* (Coat.gStep R'.beta)⁻¹
local notation "L" => low R R'
local notation "A₁" => Coat.gStep R.beta
local notation "A₂" => Coat.gStep R'.beta
include P
lemma uplift : 0<A₁ ∧ 0<A₂ ∧ 0 < L ∧ A₂*L=A₁ ∧ L*A₁⁻¹=A₂⁻¹ := by
  have he : 0<A₁:= (Fare.gS _ P.pos).1; have ht :0<A₂:=(Fare.gS _ P.pos').1
  unfold low; refine ⟨he,ht,?_,?_,?_⟩<;> first| positivity| field_simp
lemma pledge : R.beta*L^2=R'.beta:= by
  obtain ⟨ha,hb,hc,hr,h⟩:=uplift P; apply mul_left_cancel₀ (show A₂^2 ≠ 0 from pow_ne_zero _ hb.ne') (b:=R.beta*L^2)
  rw [(Fare.gS R'.beta P.pos').2 ]
  calc _ = (A₂*L)^2*R.beta := by ring
       _ = 1 := hr ▸ (Fare.gS _ P.pos).2
lemma moving (X : Coat T F) (z : Air f G) : worldZ X R'.beta (L • z) = worldZ X R.beta z:= by
  unfold Vine.worldZ; rw [show X.atmos (L • z)=L • X.atmos z from rfl, ← mul_smul,uplift P|>.2.2.2.1]
lemma lifting (X : Coat T F) (z : Air f G) : X.liftA R'.beta (L • z)=X.liftA R.beta z := by
  unfold liftA; rw [show X.atmos (L • z)=L • X.atmos z from rfl, ← mul_smul,uplift P|>.2.2.2.1]

lemma coursing (X : Coat T F) (d : ℝ) (V : Config G c) (z : Air f G) : course X d R'.beta (L • z) V=L • course X d R.beta z V := by
  unfold course; rw [moving P, ← (uplift P).2.2.2.2,mul_smul]; rfl
omit P
section area
open Set
variable {Z : Config G c}
variable (X : Coat T F) (I : Finset (Bond f))
 -- names

lemma temper {ι : Type} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ) (x: Poll.Body ι) (r : ℝ) : lens₀ Q (r • x)=lens₀ Q x*Real.exp ((1-r^2)*dotProduct x.ofLp (Q⁻¹ *ᵥ x.ofLp)/2) := by
  unfold lens₀; rw [mul_assoc,← Real.exp_add]; apply congr_arg; apply congr_arg; rw [show WithLp.ofLp (r • x) = r • x.ofLp from rfl, Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul]; simp_rw [smul_eq_mul]; ring
local notation "Y" => lensS I G
def draftI (X : Coat T F) (I : Finset (Bond f)) (β d : ℝ) (V : Config G c) (z : Air f G) :=
    let ZA := circuit (lensS I G) (vary X V).relating
    let w := swim (lensS I G) (Silica.course X d β z V)
    dotProduct w.ofLp (ZA⁻¹ *ᵥ w.ofLp)/2
include P
lemma sail (z:Air f G) (Z : Config G c) (d : ℝ) (Q' : ℝ) (h : Canary G d Q') :
    let s:=scalp I X Z R.beta d z
    scalp I X Z R'.beta d (L • z)=s * Real.exp ((1-L^2)*(draftI X I R.beta d Z z-draftI X I R.beta d X.V z)) := by
  intro s; unfold s scalp draftI; dsimp only
  rw [jacL,jacL,moving P, coursing P, show vary X X.V=X from rfl, Silica.home X h z P.pos]
  rw [show Pond.swim _ (L • course X d R.beta z Z)=L • swim Y (course X d R.beta z Z) from rfl, temper, show swim Y (L • z)=L • swim Y z from rfl, temper]; rw [mul_sub,Real.exp_sub]; simp_rw [← mul_div_assoc]; ring
end area
end YM.PhysicalNext.Repeat.Alabaster
