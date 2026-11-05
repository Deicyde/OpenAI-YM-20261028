import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Highway
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Rent

/-!
# Year Budget with arbitrary veterans room after L

Cheap in EACH forecast BOTH K and E. Note source-faithful residual is not
 simply proof that `Local` E of `Song.plusone` improves further, since
 several standalone lines necessarily cost too much. The low-genealogy
 species and the Path subtraction still need to be rearranged along with
 reattachment of differences to `K`. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration   Time Supply Input Testing
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D}
    {E : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage} {f r b : Return.Wages}
    {q : UVNext.CouplingReset.ResetPrices} {η : ℕ → ℝ} {A : Scouts (F:=F)} {hL : ℕ→ℝ}
    {Q : Targets s K} {p : Expenses Q} {c c' : ℝ} (B : Directed G I Z K P) (R : Register D p f hL)
    {N m n : ℕ}

def away (p' : RG.Stage) := Push.Local.turnCost p'.order p'.power
def heap (G : Gauge) (s : RG.Stage) (c : ℝ) := c*Time.credit G s / away s
lemma heap_pos (G : Gauge) (s : RG.Stage) (h : 0<c) : 0<heap G s c := div_pos (mul_pos h (Time.credit_pos ..)) (by unfold away Push.Local.turnCost; positivity)
-- gate relative all. For any q Stage schedule
structure Rich (c : ℝ) (W : Delays Θ) : Prop where
  large j i (h : StepStages j i) (x) (he : W.betaEntry j ≤ x) :
    let M:=p j i; let L:=D.L j; let S:=Q j i; let μ:=R.μ j i; let X:=grow G L x; let k:=(s.profile i).order; let n:=(s.profile i).power; let y:=asset M
    1≤X ∧ X^3≤Real.exp (S.mark L μ x) ∧ degreePrice (radiusB x) (X*(S.costs L μ 1 x 0).rootHit) S.δ≤1/2 ∧
      ∀ A i' l, Armada S L μ M.earn x i' A k l → 0 ≤ A →
        collars G i' x k n*(salary S L μ A x k l*(1-1/2)⁻¹) ≤ betaF G x L^M.wanting →
        Armada S L μ M.earn x y A k l ∧ degreePrice (radiusB x) (X*salary S L μ A x k l) y≤1/2 ∧
          (X^3)⁻¹*collars G y x k n*(X*salary S L μ A x k l*(1-1/2)⁻¹) ≤ heap G (s.profile i) c* δE x

lemma season (hh : ∀ j i, StepStages j i → (p j i).wanting < -(3/8:ℝ)) (hp : 0 < c) (V : Delays Θ) :
    ∃ W : Delays Θ, DelayLe V W ∧ ∀ Y : Delays Θ, DelayLe W Y → Rich R c Y := by
  obtain ⟨v,-,hv,H⟩ := collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ fun i (hi: StepStages j i)=> cruising _ (p j i) _ (R.consumes j i hi).2.1 (s.profile i).order (s.profile i).power (hh j i hi) _ (heap_pos G (s.profile i) hp))
  exact ⟨{V with betaEntry:=v},⟨hv,le_rfl,le_rfl,le_rfl⟩, fun W h=>⟨fun j i hi x hx=> H _ _ ((h.beta _).trans hx) _ hi⟩⟩

variable (hm : m<N) (hr : Receiving R A W c') (h : ∀ N m n,m≤N → Bid.Sworn (B.M.H N m) n G)
    (hQ : ∀ j i:ℕ, StepStages j i → (s.profile i).supportExponent+3≤(p j i).earn) (hu : Rich R c W)
    {X X' : RG.Rep G (B.a.S.side (m+1) n)}

include hm h hr hu hQ

end YM.PhysicalNext.Repeat.Height
