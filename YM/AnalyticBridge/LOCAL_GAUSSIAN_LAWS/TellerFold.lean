import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Flux
import YM.Push.FREE_RESOLVENT.GaugeProjection

/-!
Don't choose phase-local gauges or diagonal components to follow coarse
conditional variables. `trial` stationarity together with SAME free
crossings:
```
  Q_full W_tree = κ R^T
  d Cov Q_full = d     (roots relevant, keep constant!)
  d Cov d^T = d Z - Ψ d' R Z
  d' R Z = P_c Ψ^T     (test the trial equations backwards)
```
Applies for actual issued Wired+Larger below. Works EVEN if Wired
changes its actual H route, and subcase reused by algebraic M carriers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Current
open Function Lattice Wilson RG Precision Exterior Tree Matrix
open Bid FreeResolvent Bloch Laurent
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} (S : StepData c f)

def psi (H B : Bed) (T : Towers S.ratio.count) :=
  H.dual_diag.acts f*installed S.ratio T.T*B.diagonal.acts c

section Routes
variable (F : Forest S.ratio) (H B : Bed) (T : Towers S.patch.L) (h : Towers.Diagonal S H B T) {a v : ℝ} {k : Clip}

-- actual coarse link→slice column

def neuron := extracted S F (installed S.ratio T.A0)

include h
lemma spins (hg : Floor H k f a v) : d 1 f * neuron S F T=psi S H B T*d 1 c := by
  have he := h.stays
  have hh := mul_eq_one_comm.mp hg.diagonalInv
  unfold neuron extracted
  rw [Matrix.mul_add, ← Matrix.mul_assoc (d 1 f) (d 0 f),closed 0 f,Matrix.zero_mul,add_zero]
  unfold psi
  symm
  rw [Matrix.mul_assoc _ (B.diagonal.acts c),Matrix.mul_assoc,← Matrix.mul_assoc _ (B.diagonal.acts c),he,← Matrix.mul_assoc _ _ (installed S.ratio T.A0),← Matrix.mul_assoc, hh, Matrix.one_mul]

lemma fires :
    baseMatrix S H.metric * neuron S F T=S.kernel.penalty • (probe S).transpose := by
  let w := neuron S F T
  let R := probe S
  let K' := K (B.metric.acts c)
  obtain ⟨hb,he⟩ := stationed F (installed S.ratio T.A0) (H.metric.acts f) (B.metric.acts c) h.trial
  let p:= S.kernel.penalty; have hp : p ≠ 0 := S.kernel.penalty_pos.ne'
  change (K _ + p • (R.transpose*R))*w=p • R.transpose
  change R * w = 1 - p⁻¹ • K' at hb
  change K _ * w = R.transpose*K' at he
  rw [Matrix.add_mul,Matrix.smul_mul,he,Matrix.mul_assoc,hb,Matrix.mul_sub, Matrix.mul_one,Matrix.mul_smul,smul_sub, smul_smul, mul_inv_cancel₀ hp,one_smul,add_sub_cancel]

include h
include F
/-- E stationarity is enough to calibrate cross covariance even when the
meters of H were obtained via .metric/ellipse repair rather than pure
.diagonal. -/
lemma crossed (hg : Floor H k f a v) (ha : 0<a) {m u : ℝ} {l : Clip}
    (hb : Floor B l c m u) (hm : 0<m) :
    d 1 c*probe S * holder (d 1 f) (H.metric.acts f)=
      learned B c*(psi S H B T).transpose := by
  let d' := d 1 c; let q := d 1 f
  let M := H.metric.acts f; let C:= B.metric.acts c
  let Y := K M; let K' := K C
  let Z := holder q M; let U := holder d' C
  let J:=psi S H B T
  have ha' : Gap M a := ⟨fun v => (hg.uniform.1 v).1⟩
  have hm' : Gap C m := ⟨fun v => (hb.uniform.1 v).1⟩
  have hv : Y*Z=q.transpose := holder_value q M ha' ha
  have hw : K'*U=d'.transpose := holder_value d' C hm' hm
  have ht : Y.transpose=Y := by unfold Y Precision.K M; simp only [transpose_mul,transpose_transpose,hg.symmetric.1,Matrix.mul_assoc]
  have ht' : K'.transpose=K' := by unfold K' Precision.K C; simp only [transpose_mul,transpose_transpose,hb.symmetric.1,Matrix.mul_assoc]
  let w := neuron S F T; let r:=probe S
  have hj : d'.transpose*J.transpose=w.transpose*q.transpose := by rw [← Matrix.transpose_mul, ← Matrix.transpose_mul,show J*d 1 c=d 1 f*w from (spins S F H B T h hg).symm]
  obtain ⟨_,hx⟩ := stationed F (installed S.ratio T.A0) M C h.trial
  change Y*w=r.transpose*K' at hx
  have hx' : w.transpose*Y=K'*r := by rw [← ht, ← Matrix.transpose_mul,hx,Matrix.transpose_mul,transpose_transpose,ht']
  have he' : U.transpose*K'=d' := by rw [← ht',← Matrix.transpose_mul,hw,transpose_transpose]
  have hs : U.transpose*d'.transpose=d'*U := by rw [← Matrix.transpose_mul]; exact flux_symm d' C hm' hm hb.symmetric.1
  have hr : K' * r * Z=d'.transpose * J.transpose := by rw [← hx', Matrix.mul_assoc,hv,hj]
  change d'*r*Z=(d'*U)*J.transpose
  conv_lhs => lhs; lhs; rw [← he']
  calc
    _ = U.transpose*(K'*r*Z) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hr,← Matrix.mul_assoc,hs]
end Routes

section Slices
variable (F : Forest S.ratio) (H : Bed) (h : Larger (G:=G) S) {a v : ℝ} {k : Clip} (hg : Floor H k f a v) (ha : 0<a)

include h hg ha
/-- The constitutive equation on actual curls, requiring no full
pseudoinverse and no spatial constancy of trees. -/
lemma through :
    tensor G (d 1 f)*FreeResolvent.covariance G S F H.metric * fullMatrix G S H.metric=tensor G (d 1 f) := by
  let q := tensor G (d 1 f)
  let X := FreeResolvent.covariance G S F H.metric
  let Y := fullMatrix G S H.metric
  have he i : X *ᵥ (Y *ᵥ i)=representative S F i := block_solve F H.metric h ha (Gap.mk (fun v => (hg.uniform.1 v).1)) i
  have hz : q*tensor G (d 0 f)=0 := by rw [show q=tensor G (d 1 f) from rfl,← tensor_mul,closed 0 f,tensor_nil]
  change q*X*Y = q
  apply Matrix.ext_of_mulVec_single; intro i
  rw [← Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,he,representative, Matrix.mulVec_add,gradient,Matrix.mulVec_mulVec,hz, Matrix.zero_mulVec,add_zero]

def fConditional (B : Bed) (T : Towers S.patch.L) :=
  learned H f-psi S H B T*learned B c*(psi S H B T).transpose

def plane := tensor G (d 1 f)*insertion (plant F)

/-- Gaussian curvature covariance of the ideal free head (color identity)
on centered slice coordinates. Handles any tag-consistent tree, harmonic
transport noise is not assumed to vanish in the precision.
-/
theorem cutHead {B : Bed} (T : Towers S.patch.L) {m u : ℝ} {l : Clip}
    (hh : Floor B l c m u) (hm : 0<m) (HB : Towers.Diagonal S H B T) :
    plane (G:=G) S F * treeInverse G S F H.metric 0 * (plane (G:=G) S F).transpose=
      tensor G (fConditional S H B T) := by
  let i := insertion (plant F (G:=G))
  let b := d 1 f; let z := holder b (H.metric.acts f); let r := probe S
  let M := (H.metric.acts f); let w := neuron S F T; let J := psi S H B T
  let D := tensor G b; let X:=FreeResolvent.covariance G S F H.metric
  let k₀:= S.kernel.penalty
  have HD : tensor G b*FreeResolvent.covariance G S F H.metric * tensor G (baseMatrix S H.metric)=tensor G b := through S F H h hg ha
  have Hi : D*X*tensor G (k₀ • r.transpose) = tensor G (b*w) := by
    rw [show k₀ • r.transpose= baseMatrix S H.metric*w from (fires S F H B T HB).symm,tensor_mul,← Matrix.mul_assoc,show D*X*tensor G (baseMatrix S H.metric)=D from HD,← tensor_mul]
  have ht : K M*z=b.transpose := holder_value b M ⟨fun v => (hg.uniform.1 v).1⟩ ha
  have he : (baseMatrix S H.metric)*z=b.transpose+(k₀ • r.transpose)*(r*z) := by
    change (K M + k₀ • (r.transpose * r))*z = _
    simp only [Matrix.add_mul,ht,← Matrix.mul_assoc,Matrix.smul_mul]
  have hd : D*X*tensor G b.transpose+D*X*(tensor G (k₀ • r.transpose)*tensor G (r*z))=D*tensor G z :=
    calc
      _ = D*X*(tensor G (b.transpose+(k₀ • r.transpose)*(r*z))) := by rw [tensor_add,← tensor_mul,Matrix.mul_add]
      _ = _ := by rw [← he,tensor_mul,← Matrix.mul_assoc, show D*X*tensor G (baseMatrix S H.metric)= D from HD]
  rw [← Matrix.mul_assoc (D*X) (tensor G (k₀ • r.transpose)),Hi,← tensor_mul,show D = tensor G b from rfl,← tensor_mul] at hd
  change D*i* _*(D*i).transpose=_
  calc
    _ = D*X*tensor G b.transpose := by
      change D*i*_*(D*i).transpose=D*(i*_ * i.transpose)*_
      rw [transpose_mul, ← tensor_transpose]; simp only [Matrix.mul_assoc,D]
    _ = tensor G (b*z)-tensor G ((b*w)*(r*z)) := eq_sub_of_add_eq hd
    _ = _ := by rw [← tensor_sub]; congr 2; change (b*w)*(r*z)=J*learned B c*_; rw [show b*w=J*d 1 c from spins S F H B T HB hg];
                         rw [Matrix.mul_assoc _ (d 1 c),← Matrix.mul_assoc (d 1 c),show d 1 c*r*z=learned B c*J.transpose from crossed S F H B T HB hg ha hh hm,← Matrix.mul_assoc]

include F
theorem conditional_psd {B : Bed} (T : Towers S.patch.L) {m u : ℝ} {l : Clip}
    (hh : Floor B l c m u) (hm : 0<m) (HB : Towers.Diagonal S H B T) :
    (tensor G (fConditional S H B T)).PosSemidef := by
  rw [← cutHead S F H h hg ha T hh hm HB]
  have he : (treeMatrix G S F H.metric).IsSymm := IsSymm.submatrix
    (show (fullMatrix G S H.metric).IsSymm from full_symmetric _ hg.symmetric.1) _
  have hp := gap_positive he (tree_gap S F H.metric h ha ⟨fun v => (hg.uniform.1 v).1⟩) (treeFare_pos _ _ _ ha)
  simpa [treeInverse,resolve] using hp.inv.posSemidef.mul_mul_conjTranspose_same (plane (G:=G) S F)
end Slices
end YM.AnalyticBridge.LocalGaussianLaws.Current
