import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Jets
import YM.PhysicalNext.ORDERED_AFFINE_2B.Journeys
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Charges

/-!
# Non-vacuous finite linear readings of the ordered book

This part uses the integral and series addresses already priced in CGJ,
including justifying actual derivatives for the terms INTEGRATED in the
spectral u coordinate. No inter-exchange of Y,Z or V-field sector chart
integrals here. Applying these formulas at equality of sector flag V tests
is on the smooth extension (matrix/spectral calculations, geometry & all
selection frozen). We assert the indicated requisite ordered directional
derivatives; not certifying some additional analyticity of the spectral
integral as a function on a complex strip. Total and underlying finite
fields of interest can ask for `HasOrderAt` from the matrix ports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Whole.Book
open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree
open AnalyticBridge.LocalGaussian (add_parts per_step increment_germ identical)
open Next Next.Foundations Next.SectorChange SectorNext.Vacuum
open ProjectorNext.Equivariance (HasOrderAt)
open Further Further.CurvedGaussianJets Jets ChangeV Tracks MeasureTheory Set
open Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {c n : Side} {G : Gauge} {F H : Config G c → ℝ} {k : ℕ} {P : Directions G c → Prop}
    {V : Config G c} {l : Word G c}

def Charged (P : Directions G c → Prop) (k : ℕ) (f : Config G c → ℝ) (u : Config G c) :=
  ∀ a l, (a::l).length ≤ k → (∀ i∈a::l,P i) → HasDerivAt (fun t : ℝ => leftDerivs f l (increment u (t • a))) (leftDerivs f (a::l) u) 0

-- Require validity also near V (not merely derivative of value on
-- the set of valid flags; flags may have equality boundaries).
def Within (P : Directions G c → Prop) (k : ℕ) (f : Config G c → ℝ) (V : Config G c) := ∀ᶠ U in 𝓝 V,Charged P k f U

lemma allowed {H : Config G c → ℝ} (h : HasOrderAt H V k) : Within P k H V := by
  let A (U : Config G c) : Matrix Unit Unit ℝ := Matrix.of (fun i j=> H U)
  exact ((Good.near (A:=A) (k:=k) (U:=V) (fun i j=>h))).mono fun U hv a l hl ht => left_has a hl (hv () ())
lemma Within.presence (h : Within P k F V) : Charged P k F V := h.self_of_nhds

/-- Read finite combinations integrated with charged neighborhoods. -/
theorem Within.coin {ι : Type} [Fintype ι] (c' : ι → ℝ) (f : ι → Config G c → ℝ)
    (hF : ∀ i, Within P k (f i) V) (hk : l.length ≤ k) (hl : ∀ i∈l,P i) :
    leftDerivs (fun v => ∑ i,c' i*f i v) l V = ∑ i,c' i * leftDerivs (f i) l V := by
  induction l generalizing V with
  | nil => rfl
  | @cons i l ih =>
    have he := HasDerivAt.fun_sum (u:=Finset.univ) (fun j _=> ((hF j).presence i l hk hl).const_mul (c' j))
    have hr := (per_step V i).eventually (eventually_all.mpr fun i => (hF i).eventually_nhds)
    exact (he.congr_of_eventuallyEq (f₁:=fun t : ℝ => leftDerivs (fun v=> ∑ j,c' j*f j v) l (increment V (t • i)))
      (hr.mono fun t ht=> ih ht (Nat.le_of_succ_le hk) (fun i hi=>hl _ (by simp [hi])))).deriv
section charges
variable {I : Type*} [Fintype I] [DecidableEq I] {o : I → Site n}
    {s : Weights o} {X : Jets.Field G c I} {M C : ℝ} {p : CurvedGaussianJets.Prices} {W : Windows I} {N d : ℕ}
    (hW : W.Includes o N) (hM : Port p s k M C N) (h : ∀ᶠ U in 𝓝 V, Street p s k P X U M)
include h hM hW
lemma payroll (i : I) :
    Within P k (price X p i) V ∧ Within P k (fun u=> W.tollLine (X u) p.mass i) V ∧
    Within P k (fun u=> Round.onLine (coeff W X u) i) V := by
  refine ⟨h.eventually_nhds.mono (fun U hv a l hl hx=> (paid_dose hv hl hx i).2.2 a l rfl),
    h.eventually_nhds.mono (fun U hv a l hl hx => (paid_dose (hv.mono (fun U h'=>h'.slab W i)) hl hx (W.center i)).2.2 a l rfl),?_⟩
  let g d U := Round.ripple (coeff W X U) d i i
  let F := total Measure.count g
  let Gcost m d := qr p s k M N*((1/2:ℝ)^d)*s.τ i^m
  have hG m (_:m≤k) : Integrable (Gcost m) Measure.count := integrable_count_iff.mpr (by
    have hs := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num))
    exact ((hs.mul_left (qr p s k M N)).mul_right _).norm)
  have hs := (h.and h.eventually_nhds).mono fun U hv=>hv.1.bead_terms W hW hM.adjInv i i (hv.2.mono fun _ hu=> hu.base.symm)
  have he : ∀ᵐ x : ℕ ∂Measure.count,x∈ @Set.univ ℕ := Eventually.of_forall fun _=> trivial
  have hk : ∀ᶠ U in 𝓝 V,F U = Round.onLine (coeff W X U) i := hs.mono fun U hu=> by
    have hy : Integrable (fun d=>g d U) Measure.count := hu.integrable he hG (l:=[]) (by simp) (by simp)
    unfold F Jets.total; rw [integral_countable hy]; simp [Measure.real,Round.onLine,g]
  filter_upwards [hk.eventually_nhds,hs.eventually_nhds] with U hu hU
  intro a l hl hQ
  have hx := live_total he hG hU (l:=l) hl (fun i hi=> hQ _ (by simp [hi])) (hQ a (by simp))
  rw [← Jets.left_on hu]
  refine hx.congr_of_eventuallyEq ?_
  filter_upwards [(per_step U a).eventually hu.eventually_nhds] with t ht
  exact (Jets.left_on ht l).symm

end charges
end YM.PhysicalNext.OrderedAffine2B.Whole.Book
