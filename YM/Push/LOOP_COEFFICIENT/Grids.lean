import YM.Push.LOOP_COEFFICIENT.Alias
import YM.Push.LOOP_COEFFICIENT.BondGradient
import YM.Push.LOOP_COEFFICIENT.Vertex


/-!
# Colored grids and projections for physical position matrices
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Bloch Lattice Laurent RG Wilson Precision Exterior
open scoped Topology BigOperators ComplexConjugate
variable {G : Gauge} {n c f L : Side} {g : Ratio c f}

abbrev Axes (G : Gauge) := Axis × G.ColorIndex
abbrev FaceKey (G : Gauge) (n : Side) := Point G (Face (Per n))
abbrev Sides (G : Gauge) := PlaqAxes × G.ColorIndex
abbrev JointType (G : Gauge) (L : Side) := (Co L (Axes G)) ⊕ G.ColorIndex

def linksGrid (G : Gauge) (n : Side) : Grid n (BondKey G n) (Axes G) := Equiv.prodAssoc ..
def faceGrid (G : Gauge) (n : Side) : Grid n (FaceKey G n) (Sides G) := Equiv.prodAssoc ..
def nodesGrid (G : Gauge) (n : Side) : Grid n (SiteKey G n) G.ColorIndex := Equiv.refl _
def coarseLinks (G : Gauge) (g : Ratio c f) : Grid c (BondKey G f) (Co g.count (Axes G)) := (linksGrid G f).trans (splitCo g _)
def coarseNodes (G : Gauge) (g : Ratio c f) : Grid c (SiteKey G f) (Co g.count G.ColorIndex) := (nodesGrid G f).trans (splitCo g _)
def jointGrid (G : Gauge) (g : Ratio c f) : Grid c (JointKey G c f) (JointType G g.count) :=
  (Equiv.sumProdDistrib ..).trans (((coarseLinks G g).sumCongr (nodesGrid G c)).trans (Equiv.prodSumDistrib ..).symm)

def paintSymbol (G : Gauge) (M : Matrix (TypeFace 1) (TypeFace 1) ℂ) : Matrix (Axes G) (Axes G) ℂ := of fun i j =>
    if i.2=j.2 then M (coord i.1) (coord j.1) else 0

lemma liftMatrix_entry (G : Gauge) (M : Matrix (Body 1 c) (Body 1 f) ℝ) (x y) :
    liftMatrix G M x y = if x.2=y.2 then M (x.1.1,coord x.1.2) (y.1.1,coord y.1.2) else 0 := by
  have h := liftMatrix_apply M (G:=G) (Pi.single y 1) x
  rw [Matrix.mulVec_single_one] at h; rw [show liftMatrix G M x y = _ from h, mulVec,dotProduct,Fintype.sum_prod_type]
  conv_lhs => arg 2; ext i; rw [← Equiv.sum_comp axisEquiv]
  rcases y with ⟨⟨y,j⟩,k⟩
  simp only [coord_map,layer_coord, Pi.single_apply,Prod.mk.injEq,mul_ite,mul_one,mul_zero]
  split
  next he => simp [he,ite_and]
  next he => simp [he]

def axisProfile (G : Gauge) (A : Cross L (TypeFace 1) (TypeFace 1)) : Loops.Profiles L (Axes G) (Axes G) :=
    fun p k => paintSymbol G (profile A p k)

lemma lift_plane (G : Gauge) (M : Matrix (Body 1 f) (Body 1 c) ℝ) (i : BondKey G f) (k : Site c) (j : Axes G) :
    (cmat (liftMatrix G M) * plane (linksGrid G c) k) i j =
      if i.2=j.2 then (cmat M * plane (Equiv.refl (Body 1 c)) k) (i.1.1,coord i.1.2) (coord j.1) else 0 := by
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,cmat_apply,approached,Matrix.map_apply,liftMatrix_entry,
    apply_ite ((↑):ℝ→ℂ),Complex.ofReal_zero,plane,Matrix.of_apply,linksGrid,Equiv.prodAssoc_apply,Equiv.refl_apply]
  conv_rhs => rw [if_ctx_congr Iff.rfl (fun _ => Finset.sum_congr rfl fun x _ => (Equiv.sum_comp axisEquiv _).symm) (fun _ => rfl)]
  rcases j with ⟨j,r⟩; simp [coord_iff,Prod.mk.injEq,ite_and, ite_mul,mul_ite]

lemma lift_routed (G : Gauge) (M : Matrix (Body 1 f) (Body 1 f) ℝ) {k i S}
    (h : Routed (Equiv.refl _) (Equiv.refl _) k i (cmat M) S) : Routed (linksGrid G f) (linksGrid G f) k i (cmat (liftMatrix G M)) (paintSymbol G S) := by
  ext x j; rw [lift_plane,h,plane_mul,plane_mul]; simp only [linksGrid,Equiv.prodAssoc_apply,Equiv.refl_apply,paintSymbol,Matrix.of_apply,mul_ite,mul_zero]

lemma A0_projects (A : Cross g.count (TypeFace 1) (TypeFace 1)) (h : Row.safe A) : Projects g (linksGrid G f) (linksGrid G c)
    (cmat (liftMatrix G (installed g A))) (axisProfile G A) := by
  intro z; ext i j
  rw [lift_plane,aliasProject A h z, Matrix.sum_apply,Matrix.sum_apply]
  simp_rw [plane_mul]; unfold axisProfile paintSymbol linksGrid; simp only [Matrix.of_apply, Equiv.prodAssoc_apply,Equiv.refl_apply]; split <;> simp_all

def kineticSymbol (G : Gauge) (H : Row (TypeFace 2) (TypeFace 2)) (p : Momentum) :=
  paintSymbol G ((symbol 1 (-p)).transpose * H.read p * symbol 1 p)

lemma kinetic_routed (G : Gauge) (H : Row (TypeFace 2) (TypeFace 2)) (h : H.safe) {p i} (hp : Matches (n:=n) p i) :
    Routed (linksGrid G n) (linksGrid G n) i i (cmat (liftMatrix G (Precision.K (H.acts n)))) (kineticSymbol G H p) := by
  have hd (p i) (hp : Matches p i) : Routed (Equiv.refl _) (Equiv.refl _) i i (cmat (d 1 n)) (symbol 1 p) := reading p 1 ▸ acts_routed _ (cobound_safe 1) hp
  have he : Routed (Equiv.refl _) (Equiv.refl _) i i (cmat (d 1 n)).transpose (symbol 1 (-p)).transpose := by
    simpa only [add_zero] using (Synced.routed_transpose (p:=0) (fun k => ⟨_,by rw [add_zero]; exact hd _ _ (mon_matches k)⟩) (by simpa only [add_zero] using hd _ _ hp.neg))
  apply lift_routed; rw [Precision.K,cmat_mul,cmat_mul]; exact (he.mul (acts_routed _ h hp)).mul (hd _ _ hp)
end YM.Push.Loops
