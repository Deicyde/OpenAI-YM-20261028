import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Binding
import YM.Next.PHASE.Roots
import YM.Next.RANK.ParticleMoment
import YM.Next.RANK.Tilt
import YM.Next.ROTATIONS.Sources
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Coeff
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Rounds
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Stein
import YM.Push.FREE_RESOLVENT.Atlas
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Marginal



/-!
# Produce the formal uncut Rank integral from Genuine cloud

Even on curled data which retains singularity! Use in real PSD
normalization only; not an interpretation of general sh blends as an
integral. Reuse paid Gaussian calculus and multiplicity rules without
rebuilding Wick. This file bridges the `VMeasure` integration-by-parts
receipt. No estimate claims on other atlas sheets, or Step funds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Issue
open Function Finset Matrix MeasureTheory Filter Primitives Next Next.SectorChange Next.SectorChange.Gaussian
open YM.Multi.Vacuum.Gauss Rank SectorTools Rank.Normal MvPolynomial
open scoped BigOperators Classical MatrixOrder Topology

section moves
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Read a polynomial after a real linear change steering Z. -/
def lenses (M : Matrix I I ℝ) (p : poly I) (z : Row I) := peval p (M *ᵥ z)
-- `slit` true directional variation, requires real direction

omit [DecidableEq I] in
lemma derives (M : Matrix I I ℝ) (p : poly I) (w : Row I) : Differentiable ℝ (lenses M p) ∧
    ∀ z, fderiv ℝ (lenses M p) z w = lenses M (slit (fun i => ((M*ᵥw) i:ℂ)) p) z := by
  let b i := ((M*ᵥw) i:ℂ)
  have hx (i : I) z : HasFDerivAt (lenses M (X i)) (Complex.ofRealCLM.comp (Primitives.GCC.plane (M i))) z := by
    have he := Complex.ofRealCLM.hasFDerivAt.comp z (GCC.crossed_deriv (M i) z)
    have hh : lenses M (X i) = Complex.ofRealCLM ∘ crossed (M i) := funext fun z => aeval_X _ i
    rw [hh]; exact he
  have hF (p q : poly I) : lenses M (p*q) = lenses M p * lenses M q := funext fun _ => map_mul (aeval _) _ _
  have hG (p q : poly I) : lenses M (p+q) = lenses M p + lenses M q := funext fun _ => map_add (aeval _) _ _
  have hH (v : ℂ) z : lenses M (C v) z=v := aeval_C ..
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show lenses M (C c)=fun _ => c from funext (hH c)]; simp [lenses,peval]
  | add p q hp hq =>
    rw [hG]
    exact ⟨hp.1.add hq.1,fun z => by simp only [fderiv_add (hp.1 z) (hq.1 z),_root_.add_apply,hp.2,hq.2,map_add,hG]; rfl⟩
  | mul_X p i hp =>
    rw [mul_comm p,hF]; have hd : Differentiable ℝ (lenses M (X i)) := fun z => (hx i z).differentiableAt
    refine ⟨hd.mul hp.1, fun z => ?_⟩
    rw [fderiv_mul (hd z) (hp.1 z),_root_.add_apply,_root_.smul_apply,_root_.smul_apply,
      (hx i z).fderiv,hp.2 z,slit_prod,hG,hF,hF,ContinuousLinearMap.comp_apply,GCC.plane_read]
    change lenses M (X i) z * lenses M (slit b p) z + lenses M p z * b i = _+lenses M (C (b i)) z * lenses M p z
    rw [hH,mul_comm (lenses M p z)]; rfl

lemma lenses_int (p : poly I) (M : Matrix I I ℝ) : Integrable (lenses M p) (standard I) := by
  let q:=Sweep.pullPoly M 0 p
  have hh : lenses M p=peval q := funext fun z => by unfold lenses q; rw [Sweep.peval_pulled, zero_add]
  rw [hh,GCC.standard_cloud]
  let A : Matrix I I ℝ:=1
  have hA : Billed A 1 := fun i j => by by_cases he : i=j <;> simp [A,he]
  let k:=Fintype.card I
  have he : Hot k 1 (cloud A) := by
    rw [← PhysicalGaussianSwitch.centered]
    apply shifted_heat zero_le_one (le_refl _) Matrix.PosDef.one hA
    rw [norm_zero]; exact centerBill_nonneg _ zero_le_one
  exact (he.costed zero_le_one (poly_price q (le_refl q.totalDegree) zero_le_one)).first

/-- Prescribe the EXACT real counting cloud of the Rank symmetry,
include the orientation certificate before casting. -/
def realRank (P : Matrix I I ℝ) (h : P.IsSymm) : Normal.Symmetric I where
  cov i j:= P i j
  symm i j:= congr_arg ((↑):ℝ→ℂ) (congr_fun (congr_fun h j) i)

lemma fullGlyph (P : Matrix I I ℝ) (hp : P.PosSemidef) (hs : P.IsSymm) :
    Tapes.VMeasure (Row I) I (cloud P) id (realRank P hs) := by
  let M := CFC.sqrt P
  have hM : M*M=P := CFC.sqrt_mul_sqrt_self P hp.nonneg
  have he : M.IsSymm := Matrix.isHermitian_iff_isSymm.mp (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  have hP : MeasurePreserving (M *ᵥ ·) (standard I) (cloud P) := ⟨Gaussian.acts_meas _,Gaussian.paid P⟩
  have hQ (p : poly I) := PhysicalGaussianSwitch.pay_pull hP (peval p) ((poly_price p (le_refl p.totalDegree) (K:=1) (E:=1) zero_le_one).borel.aestronglyMeasurable)
  have hv (p : poly I) : Integrable (peval p) (cloud P) := (hQ p).1.mp (lenses_int p M)
  refine ⟨inferInstance,hv,fun y i => ?_⟩
  let v:=slit ((realRank P hs).cov i) y
  change (∫ z, peval (X i*y) z ∂cloud P)=∫ z,peval v z ∂cloud P
  rw [← (hQ _).2, ← (hQ _).2]
  let W:=lenses M y; let w:=M i
  have hh : (fun x => crossed w x • W x)=lenses M (X i*y) := by
    funext x; unfold lenses peval W; rw [_root_.map_mul,aeval_X]; rfl
  obtain ⟨hb,hx⟩ := derives M y w
  have hs : (fun i=> ((M *ᵥ w) i:ℂ))=(realRank P hs).cov i := by
    funext j; change _ =(P i j:ℂ)
    rw [← hM]; apply congr_arg ((↑):ℝ→ℂ)
    unfold mulVec dotProduct; rw [Matrix.mul_apply]; apply Finset.sum_congr rfl
    intro k _; change M j k*M i k = _; rw [show M k j = _ from congr_fun (congr_fun he j) k]; ring
  have hg : (fun x => fderiv ℝ W x w)=lenses M v := by
    funext x; unfold W; rw [hx x,hs]
  have hi := GCC.weighted_stein w W hb (lenses_int y M) (show Integrable _ (standard I) from hh.symm ▸ lenses_int _ M)
    (show Integrable _ (standard I) from hg.symm ▸ lenses_int _ M)
  rw [hh,hg] at hi; exact hi


end moves
end YM.PhysicalNext.WeightedGaussianMarginal45C.Issue
