import YM.WilsonBulk.Trees.Transfer

/-! Full conditional tree propagator at flat and deterministic mean, not only Green's functions
of an unrooted gauge. The bounds use Γ at THAT coupling level and precision; relation to pre-L
A0 supplies follows finite mesh. Also contains identity to the solution of the normal equations
for the formal Wick coefficients. Mean here is in *fine log* coordinates (the formula of
Precision.tested has relative tree coordinates; see chart adapter later).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Finset Precision Exterior Stationary Audience Matrix FreeResolvent Tree
open Work.F08 Lifted
open scoped Topology BigOperators Matrix Classical

section flat
variable {c f n : Side} {P : Patch} {K : KernelChoices} {G : Gauge}
  {η σ C W : ℝ}

variable {S : StepData c f}

def flare (G : Gauge) (P : Patch) := transRows (marketColor G (probeRow P))
lemma Stamped.flare : Stamped (flare G P) := (Stamped.painted _ _ _ _ (show Stamped (probeRow P) from FreeResolvent.probe_ready P)).opposite

def beams (G : Gauge) (T : Model P K) (B : Bed) := scaleRows K.penalty (composeRows (fluct G T B) (flare G P))
lemma charge (T : Model P K) (B : Bed) (hσ : 0≤σ)
    (he : (fluct G T B).strip σ W) (ht : (flare G P).strip σ C) :
    (beams G T B).strip σ (‖K.penalty‖*(Fintype.card (Co P.L (Loc G 1))*(W*C))) := strip_scale (strip_compose hσ he ht) _

lemma hanging (T : Model P K) (B : Bed) (hσ : 0≤ σ) (h : Serves G T B σ C) (v : f.val=c.val*P.L.val)
    (he : Bid.Larger (G:=G) (data v K)) :
    let S:= data v K; let Q:= spreadForest T v
    Seen c (splitCo S.ratio _) (Equiv.refl _) (beams G T B)
      (K.penalty • (covariance G S Q B.metric*(patron G (probe S)).transpose)) := by
  intro S Q
  exact ((h.covers v he).chain (Seen.trans (Seen.fromFine G (show Seen c (Equiv.refl (Co c _)) _ _ _ from block_probe S)))
    h.width ((Stamped.flare (G:=G) (P:=P)).bound σ).choose_spec.2 hσ).weight _

lemma stucco (P Q : Bed) (T : Forest S.ratio) (U : Matrix (Body 1 f) (Body 1 c) ℝ)
    (h : Precision.Inputs S U (P.metric.acts f) (Q.metric.acts c)) :
    baseMatrix S P.metric * extracted S T U = S.kernel.penalty • (probe S).transpose := by
  let E:= extracted S T U; let k:= S.kernel.penalty; let y:= Precision.K (Q.metric.acts c)
  let p:= probe S; let x := p.transpose
  obtain ⟨hc,hq⟩:= stationed T _ _ _ h
  rw [baseMatrix,Matrix.add_mul]; rw [hq, Matrix.smul_mul, Matrix.mul_assoc (probe S).transpose, hc];
  change x*y + k • (x*(1-k⁻¹ • y))= _
  rw [Matrix.mul_sub,Matrix.mul_one, smul_sub,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ S.kernel.penalty_pos.ne', one_smul,add_sub_cancel]

lemma holo (G : Gauge) (P Q : Bed) (T : Forest S.ratio) (U : Matrix (Body 1 f) (Body 1 c) ℝ)
    (h : Precision.Inputs S U (P.metric.acts f) (Q.metric.acts c)) :
    fullMatrix G S P.metric * patron G (extracted S T U) = S.kernel.penalty • (patron G (probe S)).transpose := by
  rw [fullMatrix, ← match_tensor, ← patron_mul,stucco P Q T U h, patron_weight, patron_star]

lemma beams_exact (G : Gauge) (P Q : Bed) (T : Forest S.ratio) (U : Matrix (Body 1 f) (Body 1 c) ℝ)
    (h : Precision.Inputs S U (P.metric.acts f) (Q.metric.acts c)) (hS : Bid.Larger (G:=G) S)
    (ha : 0 < η) (hg : Gap (P.metric.acts f) η) :
    patron G (extracted S T U) = S.kernel.penalty • (covariance G S T P.metric * (patron G (probe S)).transpose) := by
  rw [← Matrix.mul_smul, ← holo G P Q T U h]
  let X := patron G (extracted S T U)
  have hx v : Vanishes (S:=S) T (X *ᵥ v) := by
    intro i; unfold X; rw [match_tensor,component_mul]; exact Precision.stays T U _
  apply matSeen; intro v
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec, block_solve T _ hS ha hg, fixes T (hx v)]

lemma painted_copy (G : Gauge) (A : Cross S.patch.L (TypeFace 1) (TypeFace 1)) :
    Seen c (splitCo S.ratio _) (Equiv.refl _) (bondColor G A)
      (patron G (installed S.ratio A)) := Seen.coarse G (show Seen _ _ _ _ _ from rfl)

-- pay Ward replacements. Any pre-block request on σ in coarse units supported by `Stamped`
-- rows; prices of these exact paths and stubs are *post*-block. They are used only when
-- multiplied by earlier degrees, not for the unchanged rank estimates. Φ = hike*A -
-- sitesCopy (fixRoot*A).
lemma straighten_exact (T : Forest S.ratio) (U : Matrix (Body 1 f) (Body 1 c) ℝ) :
    straighten S T U=(hiking G S T- sitesCopy S *fixRoot S)*U := by
  apply matSeen; intro v; ext1 i; rw [books,←Matrix.mulVec_mulVec,sub_mulVec,_root_.Pi.sub_apply,←Matrix.mulVec_mulVec,
    hiking,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,sites_at,vac_only i.2]

variable (G)
def phiPart (T : Model P K) := fineColor G (minusRows (hikeRows T) (composeRows (copyRow P.L) (rootRow P)))
lemma Stamped.phi (T : Model P K) : Stamped (phiPart G T) := Stamped.painted _ _ _ _
  ((Stamped.hikeRows T).sub ((Stamped.site _).product (fun s _ =>ready_rootRow P s)))

lemma flower (T : Model P K) (v : f.val=c.val*P.L.val) :
    let S:=data v K; Seen c (splitCo S.ratio _) (splitCo S.ratio _) (phiPart G T)
      (patron G (hiking G S (spreadForest T v)-sitesCopy S * fixRoot S)) :=
  Seen.fine G ((hike_seen G T v).minus
    ((copy_acts (data v K)).chain' (show Seen _ (Equiv.refl _) _ (rootRow P) _ from FreeResolvent.block_root (data v K))
      (Stamped.site _) (fun s _ => ready_rootRow P s))
    (Stamped.hikeRows T) (Stamped.product (Stamped.site _) (fun s _ => ready_rootRow P s))) -- let reduces

def removeGauge (T : Model P K) (A : Cross P.L (TypeFace 1) (TypeFace 1)) := composeRows (phiPart G T) (bondColor G A)
lemma refreeze (T : Model P K) (v : f.val=c.val*P.L.val) (A : Cross P.L (TypeFace 1) (TypeFace 1))
    (hσ : 0≤σ) (hp : (bondColor G A).strip σ C) :
    let S:=data v K; Seen c (splitCo S.ratio _) (Equiv.refl _) (removeGauge G T A)
      (patron G (straighten S (spreadForest T v) (installed S.ratio A))) := by
  intro S; rw [straighten_exact (G:=G),patron_mul]; exact (flower G T v).chain (painted_copy (S:=S) G A)
    ((Stamped.phi G T).bound _).choose_spec.2 hp hσ
end flat
end YM.WilsonBulk
