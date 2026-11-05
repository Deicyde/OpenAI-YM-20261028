import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Acquiesce
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Fact
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Vapour

/-!
# Value of assembled dictionary -- pointwise

At form `refPMass`. This verifies the literal multipliers (including
remainder, tails, eta,c signs, covers/frame mask powers) in the basis for
which `Weaving` charges. Meas/applications afterwards. K selection kept
from actual R.Lives; do NOT sum guesses about missing K. RStone is
true distinguished factor adjacent budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Presented LabelSum Sector
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ μ C : ℝ} {L : Side} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (X : Coat T F) (k : Finset ℕ) (D : Cash W X.x μ L Q o C T R)

/-- On a vector in full relative chart with Y held, even ill-formed tags at
nonselected paths. Pre-value includes full Haar factors (relative when later
using full-dimensional measure map). -/
def tangible (R : Rep G f) (W : ℝ) (Y : F.Slice G) (l : Finset ℕ) : ℝ :=
    let U:= F.drape Y
    sieve T R.beta X.x X.V * X.χ.distribute X.seeds X.x W U X.k X.V * LabelSum.separate R X.R l U *
      Oriented.enters T R.beta X.x X.k X.V U

def ticketK (R : Rep G f) (W a : ℝ) (Ñ : ChartRatio G) (z : Air f G) (l : Finset ℕ) :=
    let U := X.liftA R.beta z
    X.tangible R W (X.view U) l * X.ribbons z Ñ R.beta a * X.enforce a U X.tier

def cross_link (z : Air f G) := -(Real.log X.relating.det)/2-dotProduct z.ofLp (X.relating⁻¹ *ᵥ z.ofLp)/2

/-- Inhaled from Census. -/
theorem unified_exp (D : Cash W X.x μ L Q o C T R) (h : X.manifest) (hk : X.width=o.K) (z : Air f G) :
    let β:=R.beta; let u:=X.liftA β z; let U:=X.input u; let P:=measure_g Q.table β
    X.χ.distribute X.seeds X.x W U X.k X.V≠0 → S.likelihood U X.k≠0 → X.enforce o.a u X.tier≠0 →
    (∑' j, Raw.expo T X.x R U X.V j)+ (-β*(wholeGap T X.x U X.V+∑ i, monetary S (S.prediction U X.k) X.V i))+
      (-(X.pens X.seeds).card*Real.log P+(-X.ghost z+∑ i∈X.tier,X.gentry Q.table o.a u i)) =
      -(Real.log X.blank.plate.det)/2+X.steamLog R Q.table o.a X.seeds u+
        (∑' j,X.farLog R o.a Q.table z j)+X.cross_link z := by
  intro β u U P hA hz hF
  have he := D.laws.data
  have hr := D.laws.intake
  have ht := he.room.fiery
  have hU i : X.inhale R o.a u i = Raw.expo T X.x R U X.V i := by
    unfold inhale; rw [X.underfoot (mul_pos o.large ht) hF, mul_one]
  let f := X.farLog R o.a Q.table z
  let v := ∑' i, Raw.expo T X.x R U X.V i
  have H : (∑' i,X.farLog R o.a Q.table z i)=v+( (∑ i,X.Short u Q.table β o.a i)+X.flowFood β z) := by
    have hx : HasSum (X.inhale R o.a u) v := by
      rw [funext hU]; exact (Raw.income hr U X.V).summable.hasSum
    exact (HasSum.sum (f:=f) hx (HasSum.sum (hasSum_fintype (X.Short u Q.table β o.a)) (X.fueled D h hk z hF))).tsum_eq
  have hv : Seeded X.seeds U X.k X.V X.x W := (X.χ.profiles G S X.x W he.W_pos ht).actual _ _ _ _ hA
  have hp := (he.localP F X rfl hk h).sails
  have hh := X.speckle u he.room β o.a W o.large hF hv (show Alive S U X.k from
    lt_of_le_of_ne (S.likelihood_pos ..) (Ne.symm hz))
  rw [H,show wholeGap T X.x U X.V+_=_ from X.covers_paths hr.ready u, Short]
  unfold Miniature; rw [Fintype.sum_sum_type]; dsimp only [Sum.elim]; rw [Fintype.sum_sum_type]
  change _ + _ + _ = _+_+(v+ ( ((∑ i, X.speck u β o.a i)+((∑ i,X.undercurrent i)+∑ i,X.solo u Q.table o.a i))+_))+_
  unfold flowFood cross_link steamLog; dsimp only
  have ht := X.glowing u o.a Q.table
  have hl := X.mglows
  have hθ := X.correcting hr.positive hp z
  rw [mul_add,add_assoc]
  unfold v β P
  unfold U u at *
  linarith only [ht,hh,hl,hθ]

/-- Expanded on a literal K list (sum it only once) and the fixed
nondefaults from X. Pin factor X.χ.distribute still actual full. V
normalization unnormalized. Count tree/F held fixed. -/
def summedUp (R : Rep G f) (Ñ : ChartRatio G) (W a : ℝ) (z : Air f G) (l : Finset ℕ) (Y : Finset (Stores S)) :=
    let u:= X.liftA R.beta z
    ((∏ A∈Y,X.Pack R Ñ l W a A u)*(∏ i∈l,X.bag R a u i)*
      (∏ p : WarningAt c f,(1+X.detect u W a R l p))) * Real.exp (∑' p,X.farLog R a Ñ z p)

include D in
theorem consolidated (h : X.manifest) (hk : X.width=o.K) (z : Air f G) {Y : Finset (Stores S)}
    (hp : Layout X.seeds Q.halo X.B Y) (hL : Contract.sealed R k) :
    X.ticketK R W o.a Q.table z k = X.levy R * X.deducted Q.table R.beta *
      ((Fintype.card S.Choices:ℝ)⁻¹*X.summedUp R Q.table W o.a z k Y)*X.thetaRef z := by
  let F₀:=D.laws.data
  let u := X.liftA R.beta z; let U:= X.input u
  have he : 0<o.a*X.t := mul_pos o.large F₀.room.fiery
  have hx := X.precip R Q.table u W o.a k h he
  let K' : ℝ := (Fintype.card S.Choices:ℝ)⁻¹
  let g := X.enforce o.a u X.tier
  let C₁ := X.χ.distribute X.seeds X.x W U X.k X.V
  let t := X.cross_link z
  let w := Contract.order R k univ U
  let L := S.likelihood U X.k
  have hy : K'*X.summedUp R Q.table W o.a z k Y=
      Real.exp (X.steamLog R Q.table o.a X.seeds u)*(C₁*L*w)*g*
       (∏ i∈k,X.bag R o.a u i)*Real.exp (∑' p,X.farLog R o.a Q.table z p) := by
    let f' := X.steam R Q.table k W o.a X.seeds u
    let b := ∏ p : WarningAt c f, (1 + X.detect u W o.a R k p)
    rw [show Real.exp (X.steamLog R Q.table o.a X.seeds u)*(C₁*L*w)*g=K'*(f'*b) from hx.symm]; unfold summedUp
    dsimp only
    rw [X.vents hp Q.buys u F₀.room.sight.1 R Q.table k W o.a h]; unfold f' b; ring
  rw [hy]; change X.tangible R W _ _* _ *g=_
  by_cases hf : g=0
  · rw [hf,mul_zero,mul_zero]; ring
  have hr := D.laws.intake
  let p:=prefactor S G R.beta
  have hv : X.tangible R W (X.view u) k = X.levy R * (C₁ * L*w) * (∏ i∈k,X.bag R o.a u i) *
      Real.exp ( (∑' i,Raw.expo T X.x R U X.V i) +
        (-R.beta*(wholeGap T X.x U X.V + ∑ i, monetary S (S.prediction U X.k) X.V i))) := by
    unfold tangible; unfold levy Coat.R; dsimp only; rw [Raw.fused T hr.ready, mul_right_comm (sieve ..),Raw.estate hr,Contract.release hr,if_pos hL]
    unfold C₁ L w U
    have ht i : X.bag R o.a u i=R.activities.K i (X.input u) := by unfold bag; rw [X.underfoot he hf, mul_one]
    simp_rw [ht, Real.exp_add]; unfold input; ring
  rw [hv]
  by_cases he : C₁=0
  · rw [he]; ring
  by_cases hu : L=0
  · rw [hu]; ring
  have hZ := unified_exp X D h hk z he hu hf
  unfold ribbons deducted thetaRef
  rw [X.payment Q.table hr.positive Q.table_exists]
  have hz := congr_arg Real.exp hZ
  simp_rw [Real.exp_add] at hz
  simp_rw [Real.exp_add]
  unfold U u; unfold cross_link at hz
  linear_combination X.levy R * (C₁*L*w) * (∏ i∈k, X.bag R o.a (X.liftA R.beta z) i) *g*
    (bell ^ Fintype.card (Tubular f G))⁻¹ * measure_g Q.table R.beta ^ Fintype.card F.Free * hz
end YM.ConnectedActivityE6.Coat
