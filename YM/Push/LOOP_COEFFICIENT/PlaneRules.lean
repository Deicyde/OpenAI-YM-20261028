import YM.Push.LOOP_COEFFICIENT.Grids
import YM.Push.LOOP_COEFFICIENT.Orientation

/-!
# Exact gauge, spin and real-vs-complex rules for link waves
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Lattice Matrix Set Precision RG Bloch Laurent Exterior Wilson Complex
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff ComplexConjugate
variable {G : Gauge} {n : Side} {p : Momentum} {k : Site n}






def longitudinal (G : Gauge) (p : Momentum) : Matrix (Axes G) G.ColorIndex ℂ :=
    of fun i j => if i.2=j then -(q p i.1) else 0

lemma R_zero_read (G : Gauge) (v : CSpace (SiteKey G n)) (i : BondKey G n) :
    (cmat (R_g (1:Config G n)) *ᵥ v) i = v (i.1.1,i.2) - v (i.1.1+step i.1.2,i.2) := by
  let f := LinearMap.proj (R:=ℂ) (φ:=fun _ : SiteKey G n => ℂ) (i.1.1,i.2) - LinearMap.proj (i.1.1+step i.1.2,i.2)
  refine DFunLike.congr_fun (complex_ext (L:=(LinearMap.proj i).comp (cmat (R_g 1)).mulVecLin) (T:=f) fun v => ?_) v
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply,cmat_mulVec, R_g,LinearMap.toMatrix'_mulVec]
  change ((paint G _ (brace 1 v) i.1 i.2 : ℝ):ℂ) = _
  rw [paint_brace,Pi.one_apply,G.adjoint_one]; simp [f,cvec]

lemma R_zero_routed (hp : Matches p k) : Routed (linksGrid G n) (nodesGrid G n) k k (cmat (R_g 1)) (longitudinal G p) := by
  refine Routed.of_vector fun v => ?_
  funext ⟨⟨x,j⟩,i⟩; rw [plane_apply,R_zero_read,plane_apply,plane_apply]
  change cell k x * v i - cell k (x+step j) * v i = _
  rw [cell_add, hp.step]; simp [linksGrid, Matrix.mulVec, dotProduct,longitudinal,q,ite_mul]; ring

def corner (s : Signed) (p : Momentum) (i : Axis) : ℂ := if s.flip i then -(Complex.exp (Complex.I * p (s.perm i)))⁻¹ else 1

def orbitSymbol (G : Gauge) (s : Signed) (p : Momentum) : Matrix (Axes G) (Axes G) ℂ := of fun i j =>
    if (s.perm i.1,i.2)=j then corner s p i.1 else 0
lemma orbit_apply (s : Signed) (p : Momentum) (v : CSpace (Axes G)) (i j) :
    (orbitSymbol G s p *ᵥ v) (i,j) = corner s p i * v (s.perm i,j) := by simp [orbitSymbol,Matrix.mulVec,dotProduct,ite_mul]

lemma real_flip (s : Signed) (v : CSpace (BondKey G n)) (i : BondKey G n) :
    (cmat (linkSpin s (1:Config G n)) *ᵥ v) i = if s.flip i.1.2 then -v (sendEdge s 0 i.1,i.2) else v (sendEdge s 0 i.1,i.2) := by
  let e : _ →ₗ[ℂ] ℂ := LinearMap.proj (φ:=fun _ : BondKey G n => ℂ) (sendEdge s 0 i.1,i.2)
  let f := if s.flip i.1.2 then -e else e
  suffices (LinearMap.proj i).comp (cmat (linkSpin s (1:Config G n))).mulVecLin = f by
    conv_lhs => change (LinearMap.proj i).comp (cmat (linkSpin s (1:Config G n))).mulVecLin v
    rw [this]; unfold f; split <;> rfl
  apply complex_ext; intro v
  simp only [LinearMap.comp_apply, LinearMap.proj_apply,Matrix.mulVecLin_apply,cmat_mulVec]
  change ((paint G _ (direct _ _ *ᵥ v) _ _ : ℝ):ℂ) = _
  rw [paint_direct,spins]; unfold f; split <;> simp [*, e, cvec]

lemma orbit_routed (hp : Matches p k) (s : Signed) :
    Routed (linksGrid G n) (linksGrid G n) (s⁻¹.act k) k (cmat (linkSpin s 1)) (orbitSymbol G s p) := by
  refine Routed.of_vector fun v => ?_; funext ⟨⟨x,j⟩,i⟩; rw [plane_apply]
  change _ = cell (s⁻¹.act k) x * (orbitSymbol G s p *ᵥ v) (j,i)
  rw [real_flip,orbit_apply,plane_apply,sendEdge,Step.rotate,Step.used,posDir,corner,affine,add_zero,Bool.false_xor]
  split
  next he =>
    simp only [linksGrid,Equiv.prodAssoc_apply,sub_eq_add_neg,cell_add,cell_inverse,hp.step,← cell_dual s (s⁻¹.act k) x, s.act_inv]; ring
  next he =>
    simp only [linksGrid,Equiv.prodAssoc_apply,one_mul, ← cell_dual s (s⁻¹.act k) x, s.act_inv]

def fiberColor (G : Gauge) (u : G.El) := cmat (adjoints (fun _ : Axis => u))
lemma colorLink (u : G.El) (x : Site n) (v : CSpace (BondKey G n)) (i : Axes G) :
    (cmat (linkAdj (constantGauge u)) *ᵥ v) ((x,i.1),i.2) = (fiberColor G u *ᵥ fun j => v ((x,j.1),j.2)) i := by
  let f : (CSpace (BondKey G n)) →ₗ[ℂ] CSpace (Axes G) := LinearMap.pi fun j => LinearMap.proj ((x,j.1),j.2)
  refine DFunLike.congr_fun (complex_ext (L:=(LinearMap.proj _).comp (cmat (linkAdj (constantGauge u))).mulVecLin) (T:=(LinearMap.proj i).comp ((fiberColor G u).mulVecLin.comp f)) fun v => ?_) v
  simp only [LinearMap.comp_apply,LinearMap.proj_apply, Matrix.mulVecLin_apply, cmat_mulVec, fiberColor,
    show f (cvec v) = cvec (fun j => v ((x,j.1),j.2)) from rfl]
  change Complex.ofReal (paint G (Bonds n) (adjoints _ *ᵥ _) _ _) = Complex.ofReal (paint G Axis (adjoints _ *ᵥ _) _ _)
  rw [paint_adjoints,paint_adjoints]; rfl

lemma fiberColor_routed (u : G.El) (k : Site n) : Routed (linksGrid G n) (linksGrid G n) k k (cmat (linkAdj (constantGauge u))) (fiberColor G u) := by
  apply Routed.of_vector; intro v; funext ⟨⟨x,i⟩,j⟩; rw [show (cmat _ *ᵥ _) ((x,i),j) = _ from colorLink u x _ (i,j),plane_apply,
    show (fun j => (plane (linksGrid G n) k *ᵥ v) ((x,j.1),j.2)) = cell k x • v from funext (fun j => (plane_apply ..).trans (by rfl)), Matrix.mulVec_smul]; rfl
end YM.Push.Loops
