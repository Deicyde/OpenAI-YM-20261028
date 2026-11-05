import YM.AnalyticNext.CUBIC_MATCH.Handover
import YM.AnalyticNext.CUBIC_MATCH.Region.Channels
import YM.AnalyticNext.CUBIC_MATCH.Region.Prediction
import YM.AnalyticNext.CUBIC_MATCH.Region.Relative



set_option warningAsError false

/-!
# Cubic remainder cost and path lifting on the actual Shape

Prove it as a `TotalRep` with a sup kernel
(hence pays geometric mass at any smaller positive width). Remainder
means the cubic part after removing `baseline`; not a price claim on
`thermal`, contour support or a finite-scale Taylor error. **Order receipts**
and consuming `StationaryScenes.first_jets` in next module. θ small and
uniform in shape invoicing, scales paying incoming σ AFTER the conservative
requirements; no losses depending on the period or replacing an exact tag
by a spectral fit. Wrappers at top also reading actual finite Wilson.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Tensor Bid Lift
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {μ : Type*} {n : Side} {c f : μ → Side} {P : Patch} {K : KernelChoices}
  {W Z : PathData G} {η θ C A B α σ Λ δ D E υ U v σ' Λ' d e a : ℝ}
  {T : Towers P.L} {b q : Clip}

def expense (G : Gauge) (θ B δ d : ℝ) := shaped G ((Fintype.card G.ColorIndex:ℝ)*(Real.exp θ+1)) δ θ B d







def crestPrice (G : Gauge) (θ B δ d : ℝ) := summitFee G ((Fintype.card G.ColorIndex:ℝ)*(Real.exp θ+1)) θ + expense G θ B δ d






def phaseReserve (C θ : ℝ) := C*Real.exp (θ*4)

/-- E C_J for just the baseline+predictor+output base. -/
def preCover (G : Gauge) (θ C D E δ υ d e k : ℝ) (J : ℕ) :=
    let u := phaseReserve C θ
    shaped G u δ θ D d + subsidy G (journey G J u θ) θ k + expense G θ E υ e

def fineCap (C θ : ℝ) := pathSurcharge θ (phaseReserve C θ)





section irrelevance
variable {n m : Side} {S : StepData n m} (t t' : S.Choices) {F R : Forest S.ratio} {r : Dir G n → AxisChart G F}
    {r' : Dir G n → AxisChart G R}




end irrelevance

/-- Constants for conversion from remainder budget to paid cubic atoms.
LocalRep cost needs no Norm estimates on clipped heights; Uses 0/1/2 results
 supplied at this step, even if W baseline alone. -/
theorem invoice (G : Gauge) {θ : ℝ} (he : 0<θ) : ∃ η K : ℝ, 0<η ∧ 0<K ∧
    ∀ (n : ℕ → Side) (_ : Tendsto (fun i => (n i).val) atTop atTop) (q : Clip) (P : PathData G) (b v z : ℝ),
    P.Bounds q b v z → ∀ F : ∀ i, Dir G (n i) → ℝ, (∀ i,Checks (n i) (F i)) →
    (∀ i, SameJet 1 (F i) (baseline q P)) → (∀ i, SameJet 2 (F i) (baseline q P)) →
    ∀ C : ℝ, TotalRep n 3 θ C (fun p x => term 3 (fun t : ℝ => (F p-baseline q P : Dir G (n p) → ℝ) (t • x))) →
      ∃ R : ℕ → Atom G 3, Flies η (K*C) R ∧ ∀ σ B Λ (T : PathData G), T.Bounds q σ B Λ → T.row=P.row → T.cubic=R →
        ∀ i, SameJet 3 (F i) fun x => mainTerm q T (represent x) := by
  obtain ⟨η,K,hη,hK,H⟩ := earn G (show 0<θ/4 by positivity)
  have hz := exitFee_nonneg G θ
  refine ⟨η,K*exitFee G θ+1,hη,by positivity,fun n hn q P b v z h F hf h₁ h₂ C hC => ?_⟩
  obtain ⟨A,-,hα,ha,ht⟩ := hC.relative (fun i => ((Checks.inherited (hf i) (aware h)).analytic.of_le le_top))
  obtain ⟨R,hr,hx⟩ := H n hn q P b v z h F hf h₁ h₂ _ (mul_nonneg hz hα) A ha ht
  exact ⟨R,⟨⟨hr.1.1,hr.1.2.1,hr.1.2.2.trans (by rw [add_mul,one_mul,mul_assoc]; linarith)⟩,hr.2⟩,hx⟩
end YM.CubicMatch
