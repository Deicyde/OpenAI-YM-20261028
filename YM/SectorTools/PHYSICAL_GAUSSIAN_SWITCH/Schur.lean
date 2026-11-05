import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Local
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Marginal

/-!
# Covariance confinement: reduce on the Schur residual, NOT the raw support coords

E includes chosen support indices into all indices. Suppose h supported
there and A-D=E B Eᵀ. D*=(EᵀD⁻¹E)⁻¹ (analogously A*) are the conditional
or Schur covariances. Use R=D* EᵀD⁻¹. On actual z this is z_s plus a linear
combination of complement coordinates (independence from complement
under cloud D, though expected since cross-covariances vanish, not needed or formalized here). RE = 1; on ker R the density change is translation
invariant. Prove exactly using both actual pushed measures (we never need
a construction of a kernel of regular conditional probabilities). -/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch
open Function Filter Set Matrix MeasureTheory
open Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment.Relative (trade)
open FreeResolvent (insertion)
open scoped Topology BigOperators ENNReal
local notation "Covar" => Next.SectorChange.Gaussian.Table
open Support

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {A D : Covar I} {e : J ↪ I} {a d h : Vec I}

def schurCov (e : J ↪ I) (D : Covar I) := ((D⁻¹).submatrix e e)⁻¹
def residual (e : J ↪ I) (D : Covar I) := schurCov e D * (put e).transpose * D⁻¹

lemma schurCov_pos (e : J ↪ I) (hD : D.PosDef) : (schurCov e D).PosDef := (hD.inv.submatrix e.injective).inv
lemma residual_right (e : J ↪ I) (hD : D.PosDef) : residual e D * put e = 1 := by
  unfold residual schurCov put
  simp_rw [Matrix.mul_assoc,← Matrix.mul_assoc (insertion e).transpose]
  rw [insertion.compress,nonsing_inv_mul _ (unit_det (hD.inv.submatrix e.injective))]
lemma residual_cancel (e : J ↪ I) (hD : D.PosDef) : residual e D * D = schurCov e D * (put e).transpose := by
  rw [residual,Matrix.mul_assoc (_*_),D.nonsing_inv_mul (unit_det hD),Matrix.mul_one]
lemma residual_cancel' (e : J ↪ I) (hD : D.PosDef) : D * (residual e D).transpose = put e * schurCov e D := by
  have he := congr_arg Matrix.transpose (residual_cancel e hD)
  rwa [transpose_mul,transpose_mul,(symm_pos hD).eq,(symm_pos (schurCov_pos e hD)).eq,transpose_transpose] at he

lemma residual_cov (e : J ↪ I) (hD : D.PosDef) : covView (residual e D) D = schurCov e D := by
  rw [covView,Matrix.mul_assoc,residual_cancel' e hD,← Matrix.mul_assoc,residual_right e hD,Matrix.one_mul]
lemma residual_law (e : J ↪ I) (hD : D.PosDef) (a : Vec I) :
    MeasurePreserving (view (residual e D)) (shift D a) (shift (schurCov e D) (view (residual e D) a)) :=
  residual_cov e hD ▸ view_shift hD.posSemidef (residual e D) a

lemma residual_ker (e : J ↪ I) {x : Vec I} (hD : D.PosDef) (he : view (residual e D) x=0) : pick e (D⁻¹ *ᵥ x)=0 := by
  let T := D⁻¹.submatrix e e
  have hT : T.PosDef := hD.inv.submatrix e.injective
  unfold view residual schurCov at he
  rw [← mulVec_mulVec,← mulVec_mulVec,pick_mul] at he
  have hi := congr_arg (T *ᵥ ·) he
  rw [mulVec_zero,mulVec_mulVec,show T * _ = 1 from Matrix.mul_nonsing_inv _ (unit_det hT),one_mulVec] at hi
  exact hi

/-- Now different! Confining the *covariance* (not precision) perturbation
and the SHIFT itself (not the precision applied to the shift). -/
structure ConfinedCovariance (e : J ↪ I) (A D : Covar I) (h : Vec I) : Prop where
  block : SquareOn e (A-D)
  center : VectorOn e h

namespace ConfinedCovariance
variable (hA : A.PosDef) (hD : D.PosDef)
include hA hD

lemma same_residual (H : SquareOn e (A-D)) : residual e D = residual e A := by
  let E := put e; let B := (A-D).submatrix e e
  let T := schurCov e D; let g := residual e D
  have he : A=D+E*B*E.transpose := by unfold B E; rw [retrieve e H]; abel
  have hg : g*A=(T+B)*E.transpose := by
    rw [he, Matrix.mul_add, residual_cancel e hD, ← Matrix.mul_assoc g, ← Matrix.mul_assoc g, residual_right e hD, Matrix.one_mul,Matrix.add_mul]
  have h3 : g=(T+B)*E.transpose*A⁻¹ := by
    rw [← hg,Matrix.mul_assoc,A.mul_nonsing_inv (unit_det hA),Matrix.mul_one]
  -- thus (T+B) left-inverts A⁻¹_ss
  let M := A⁻¹.submatrix e e; have hM : M.PosDef := hA.inv.submatrix e.injective
  have hv : g*E=(T+B)*M := calc
    _ = ((T+B)*E.transpose*A⁻¹)*E := by rw [h3]
    _ = _ := by simp_rw [Matrix.mul_assoc,← Matrix.mul_assoc E.transpose]; unfold E put M; rw [insertion.compress]
  have h5 : T+B=M⁻¹ := by
    rw [show T+B=(T+B)*M*M⁻¹ from ?_,←hv,residual_right e hD,Matrix.one_mul]
    rw [Matrix.mul_assoc,M.mul_nonsing_inv (unit_det hM), Matrix.mul_one]
  change g=_; rw [h3,h5]; rfl

-- v in ker R is invisible to the trade, even though reading raw support
-- positions without this regression would not suffice.
lemma invisible (H : SquareOn e (A-D)) (hu : VectorOn e h) {v : Vec I}
    (hv : view (residual e D) v=0) :
    (A⁻¹-D⁻¹) *ᵥ v=0 ∧ (A⁻¹ *ᵥ h) ⬝ᵥ v=0 := by
  have hd := residual_ker e hD hv
  have ht : (A-D) *ᵥ (D⁻¹ *ᵥ v) = 0 := by
    rw [← retrieve e H,← mulVec_mulVec,pick_mul,hd,Matrix.mulVec_zero]
  have he : A *ᵥ (D⁻¹ *ᵥ v)=v := by
    rw [sub_mulVec,mulVec_mulVec v D D⁻¹,D.mul_nonsing_inv (unit_det hD),one_mulVec] at ht
    exact sub_eq_zero.mp ht
  have ha : A⁻¹ *ᵥ v = D⁻¹ *ᵥ v := calc
    _ = A⁻¹ *ᵥ (A *ᵥ (D⁻¹ *ᵥ v)) := congr_arg _ he.symm
    _ = _ := by rw [mulVec_mulVec (D⁻¹ *ᵥ v), A.nonsing_inv_mul (unit_det hA), one_mulVec]
  refine ⟨by rw [sub_mulVec,ha,sub_self],?_⟩
  rw [dotProduct_comm,turn (symm_pos hA.inv) v h,ha,vector_pick e hu,hd,dotProduct_zero]

lemma held (H : ConfinedCovariance e A D h) (z v : Vec I) (hv : view (residual e D) v=0) :
    trade A D h (z+v)=trade A D h z := by
  obtain ⟨he,hi⟩ := invisible hA hD H.block H.center hv
  rw [trade_as_potential hA,trade_as_potential hA]; unfold kernel exponent
  have hs : (A⁻¹-D⁻¹).IsSymm := by unfold Matrix.IsSymm; rw [transpose_sub,(symm_pos hA.inv).eq,(symm_pos hD.inv).eq]
  rw [quad_add hs, he,dotProduct_zero, dotProduct_add,neg_dotProduct _ v,hi, show quad (A⁻¹-D⁻¹) v=0 from ?_]; ring_nf
  unfold quad; rw [he,dotProduct_zero]

lemma factor (H : ConfinedCovariance e A D h) (z : Vec I) :
    let u := put e *ᵥ view (residual e D) z
    trade A D h z=trade A D h u := by
  intro u; let v:=z-u; apply (show z=u+v from by unfold v; abel) ▸ held hA hD H u v ?_
  unfold view v u; rw [Matrix.mulVec_sub,mulVec_mulVec (view (residual e D) z),residual_right e hD,one_mulVec]
  exact sub_self _

theorem reduces (H : ConfinedCovariance e A D (d-a)) :
    Sufficient (view (residual e D)) A a D d (schurCov e A) (schurCov e D) := by
  refine ⟨hA,hD,schurCov_pos e hA,schurCov_pos e hD,
    ?_, residual_law e hD _,?_⟩
  · rw [same_residual hA hD H.block]; exact residual_law e hA _
  refine ⟨(fun y => trade A D (d-a) (view (put e) (y-view (residual e D) d))),
    (trade_cont ..).measurable.comp ((view_cont _).measurable.comp (measurable_id.sub measurable_const)),
    fun _ => (trade_pos hA hD ..).le,?_⟩
  funext z; rw [likelihood,factor hA hD H]; unfold Function.comp view; rw [Matrix.mulVec_sub]

omit hA in
lemma marks (H : VectorOn e (d-a)) :
    view (residual e D) d - view (residual e D) a = pick e (d-a) := by
  unfold view; rw [← mulVec_sub]
  nth_rw 1 [← restore e H]
  rw [mulVec_mulVec,residual_right e hD,one_mulVec]


end ConfinedCovariance
end YM.SectorTools.PhysicalGaussianSwitch
