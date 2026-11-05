import YM.Push.FREE_RESOLVENT.GaugeProjection
import YM.WilsonBulk.Spectral.Backing

/-! Exact projection along the augmented gauge in counting coordinates.

`collapse` sends (fine links, coarse frames) ∈ Bodies in pre-root gauge to fine links
with frame gauge FIXED (i.e. for use with probe, not the unrooted mean). Full Gram is the full
form BEFORE restriction to the tree. We work in the Period geometries of Precision;
no measure estimate. -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Finset Precision Exterior Stationary Audience Matrix FreeResolvent
open scoped Topology BigOperators Matrix

variable {c f n : Side} {G : Gauge} {α β : Type} [Fintype β] [DecidableEq β]
lemma matSeen {A B : Matrix α β ℝ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A=B := by
  apply Matrix.toLin'.injective; apply LinearMap.ext; exact h

variable (G)

lemma match_tensor {r t} (P : Matrix (Body r c) (Body t n) ℝ) : patron G P=tensor G P := by
  apply matSeen; intro v; rw [patron_fee]; ext1 ⟨x,i,j⟩
  change (P *ᵥ component v j) (x,i) = component (tensor G P *ᵥ v) j (x,i)
  rw [component_mul]
lemma patron_0 (r t : ℕ) (c f : Side) : patron G (0 : Matrix (Body r c) (Body t f) ℝ)=0 := by
  rw [match_tensor]; ext; simp [tensor]
lemma patron_plus {r t} (P Q : Matrix (Body r c) (Body t f) ℝ) :
    patron G (P+Q)=patron G P+patron G Q := by
  rw [match_tensor,match_tensor,match_tensor]; ext i j; unfold tensor
  simp only [Matrix.add_apply,of_apply]; split <;> simp
lemma patron_weight {r t} (P : Matrix (Body r c) (Body t f) ℝ) (v : ℝ) : patron G (v • P)=v • patron G P := by
  rw [match_tensor,match_tensor]; ext i j; unfold tensor
  simp only [Matrix.smul_apply,of_apply]; split <;> simp
lemma wired_full (S : StepData c f) (B : Bed) :
    fullMatrix G S B.metric =
      patron G (K (B.metric.acts f)) + S.kernel.penalty • ((patron G (probe S))ᵀ * patron G (probe S)) := by
  rw [fullMatrix,baseMatrix,← match_tensor,patron_plus,patron_weight,patron_mul,patron_star]

variable (S : StepData c f)

def sitesCopy : Matrix (Body 0 f) (Body 0 c) ℝ := Matrix.of fun a b =>
  if b=(S.ratio.parent a.1,a.2) then 1 else 0
lemma sites_at (v : form 0 c) (a) : (sitesCopy S *ᵥ v) a=v (S.ratio.parent a.1,a.2) := by
  simp [sitesCopy,mulVec,dotProduct,ite_mul]
lemma center_copy (v : form 0 c) : Precision.centered S (sitesCopy S *ᵥ v)=v := by
  ext1 a; simp [Precision.centered,sites_at,S.ratio.embed_parent]
lemma probe_roots : probe S*(d 0 f*sitesCopy S)=d 0 c := matSeen fun v=> by
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,root_gradient,center_copy]
lemma power_kills (B : Bed) : patron G (K (B.metric.acts f))*patron G (d 0 f)= 0 := by
  rw [← patron_mul,K_kills,patron_0]
lemma power_sym (B : Bed) (h : (B.metric.acts f).transpose = B.metric.acts f) :
    (patron G (K (B.metric.acts f)))ᵀ = patron G (K (B.metric.acts f)) := by
  rw [← patron_star]; simp [K,h,Matrix.mul_assoc]

-- discharge exact ratio gauge, no scaling of v in root test
abbrev HGrad (S : StepData c f) := d 0 f * sitesCopy S
def collapse : Matrix (Lines G f 1) (Bodies G c f) ℝ :=
  butt G c f - patron G (HGrad S)*(brim G c f + patron G (fixRoot S)*butt G c f)
lemma collapse_test : patron G (probe S) * collapse G S = -fortune G S := by
  let R:= probe S; let Y:= butt G c f
  unfold collapse fortune bondsM
  rw [Matrix.mul_sub,←Matrix.mul_assoc (patron G (probe S)), ← patron_mul, probe_roots];
  rw [probe,patron_plus,Matrix.add_mul, Matrix.mul_add, patron_mul, Matrix.mul_assoc]
  simp only [Matrix.neg_mul]; abel
lemma collapse_charge (B : Bed) : patron G (K (B.metric.acts f))*collapse G S =
    patron G (K (B.metric.acts f))*butt G c f := by
  rw [collapse,Matrix.mul_sub,← Matrix.mul_assoc _ (patron G (HGrad S)), HGrad, patron_mul,
    ← Matrix.mul_assoc (patron _ (K _)),power_kills,Matrix.zero_mul,Matrix.zero_mul,sub_zero]
lemma collapse_equal (B : Bed) (h : (B.metric.acts f).transpose = B.metric.acts f) :
    frontR G S B = (collapse G S)ᵀ * fullMatrix G S B.metric * collapse G S := by
  let D:= collapse G S; let U:= butt G c f; let q:= patron G (K (B.metric.acts f)); let p:= patron G (probe S)
  have he : Dᵀ*q=Uᵀ*q:= by
    have h' := congrArg Matrix.transpose (collapse_charge G S B)
    simp only [transpose_mul, power_sym G B h] at h'; exact h'
  rw [wired_full]
  change Uᵀ*q*U+S.kernel.penalty • ((fortune G S)ᵀ*fortune G S) = Dᵀ * (q+ S.kernel.penalty • (pᵀ*p))*D
  rw [Matrix.mul_add,Matrix.add_mul,he]
  congr 1
  · rw [Matrix.mul_assoc Uᵀ, Matrix.mul_assoc, show q*D=q*U from collapse_charge ..]
  rw [Matrix.mul_smul, Matrix.smul_mul];
  rw [← Matrix.mul_assoc Dᵀ pᵀ, Matrix.mul_assoc (Dᵀ*_)]
  rw [← Matrix.transpose_mul, show p*D=_ from collapse_test G S]; simp

-- the augmentation spreadM exactly kills this Gram (all off-real assertions independent)
lemma mean_curry (z) : patron G (Precision.mean S)*ᵥ (gradientA G f z)=
    patron G (d 0 c)*ᵥ (curryG G S*ᵥ z) := by
  rw [first_uniform, ← patron_fee]
  simp_rw [match_tensor]
  ext1 ⟨x,i,j⟩
  change component (tensor _ (mean S)*ᵥ (tensor G (d 0 f) *ᵥ z)) j (x,i)=component (tensor _ (d 0 c) *ᵥ (curryG G S *ᵥ z)) j (x,i)
  simp_rw [component_mul]; rw [Precision.mean_site]; obtain ⟨s,rfl⟩:=axisEquiv.surjective i
  rw [coord_map,d_sites]
  dsimp only [component,ix]; simp_rw [curry_at, mul_sub,Finset.sum_sub_distrib]
  rw [← coord_map,axisEquiv.symm_apply_apply] --?
lemma lie_kernel (B : Bed) : frontR G S B * spreadM (G:=G) S=0 := by
  have hl (z : BaseSites G f) : (butt G c f * spreadM (G:=G) S) *ᵥ z=-(gradientA G f z) := by
    rw [← mulVec_mulVec,parliament,helmet_ear,helmet_butt,sliceX]; rfl
  have hu (z : BaseSites G f) : (brim G c f * spreadM (G:=G) S) *ᵥ z=-(curryG G S *ᵥ z) := by
    rw [← mulVec_mulVec,parliament,helmet_ear,helmet_brim,sliceY]; rfl
  have hf : fortune G S * spreadM (G:=G) S=0 := by
    apply matSeen; intro v
    rw [fortune, Matrix.add_mul,Matrix.mul_assoc, Matrix.mul_assoc,add_mulVec,
      ← mulVec_mulVec,hl, ← mulVec_mulVec,hu,bondsM,Matrix.neg_mulVec,mulVec_neg,mulVec_neg,
      ← mean_curry,Matrix.zero_mulVec]; abel
  rw [frontR, Matrix.add_mul,Matrix.smul_mul,Matrix.mul_assoc ((fortune G S)ᵀ),hf,Matrix.mul_zero,
    smul_zero,add_zero,posting,Matrix.mul_assoc _ _ (spreadM (G:=G) S)]
  apply matSeen; intro v; rw [← Matrix.mulVec_mulVec,hl,Matrix.mulVec_neg,← Matrix.mulVec_mulVec,first_uniform,
    ← patron_fee,mulVec_mulVec _ (patron G _), power_kills,Matrix.zero_mulVec,Matrix.mulVec_zero,
    neg_zero, Matrix.zero_mulVec]

end YM.WilsonBulk
