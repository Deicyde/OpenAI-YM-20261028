import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Covers
import YM.Next.RANK.Herald
import YM.Next.RANK.Tilt
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Issue.Cut.Scissors


/-!
# Lifted curvature columns with perturbation (read-out distances)

Q on the covariance of the *retained* d-Z head-and-tree calculation,
read in `PAC` orientation, before orientations of marker paths, from the
actual SAME high H; μ on newly called Ψ columns (all cochain indexes).
Give the Z cover explicitly. No support-choices inferred on Γ nor
changes in label assemblies. Allows post-L spectral prices for additional
kernel bounds ON THIS H and T, not loaning them from sector hypotheses
alone. Covers' Z witness is earned even with arbitrary compatible tree
because of projection identity of onePlateau. Reversal at Z (for symmetry
of cut covariance) is lifted with *negated* displacement. For the
comparison no other normalization of sh operators needed (but this does
not assert signed frame or channel invariance if elsewhere required!).
End-point kernels read on base cells, caller to check all canonical face
moves of its cut. Psi/Spectrum takes compatible inputs in E unfolding
(including crossing alias costs in Column proofs).
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.Cut
open AnalyticBridge.LocalGaussianLaws Sweep Arc 
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Laurent Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent Remote Lift Extra.Iteration.Scales MeasureTheory Local Work.F08
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

section span

-- Same orientation across all levels/steps calling this H version.

def publish (G : Gauge) (P : Patch) {c f : Side} (S : StepData c f) (h : S.patch=P) :=
  let X := splitCo S.ratio (PAC G 2)
  let b1 : S.ratio.count = P.L := congr_arg Patch.L h
  X.trans (Equiv.prodCongr (Equiv.refl (Site c)) (Equiv.cast (congr_arg (fun L => Co L (PAC G 2)) b1)))

abbrev veilCut (G : Gauge) (P : Patch) := Row (dial P G) (dial P G)

def laid (G : Gauge) (P : Patch) {c f : Side} (S : StepData c f) (h : S.patch=P) (Z : veilCut G P) :=
    (Z.acts c).submatrix (publish G P S h) (publish G P S h)

-- hH supplied separately for this stamp; Z persists across all
-- admitted levels/periods on H. Real `cutHead` orientation.
structure Figure (G : Gauge) (P : Patch) (K : KernelChoices) (t C : ℝ) (H : Bed) (Z : veilCut G P) : Prop where
  buys : Z.strip t C
  flip : transRows Z=Z
  transfer : ∀ {c f : Side} (S : StepData c f) (h : S.patch=P) (B : Bed) (q : Clip)
      (T : Towers S.patch.L) {v N : ℝ}, S.kernel=K → 0<v → Floor B q c v N → Towers.Diagonal S H B T → Larger (G:=G) S →
      ∀ (_ : 3≤c.val), laid G P S h Z=tensor G (fConditional S H B T)

theorem summon (G : Gauge) (P : Patch) (Pt : Teller G) (h : P.Branches Pt.bind G)
    (s M a : ℝ) (ha : 0<a) (hs : 0<s) (hM : 0≤M) :
    ∃ t C : ℝ, 0<t ∧ 0<C ∧ ∀ H : Bed, H.metric.strip s M → (∀ n, Floor H Pt.top.clip n a M) →
      ∃ Z : veilCut G P, Figure G P Pt.bind t C H Z := by
  obtain ⟨t,A,ht,hA,H0⟩ := onePlateau P Pt.bind G s M a P.odd_side h ha hs hM
  refine ⟨t,A,ht,hA,?_⟩; intro H hU hP
  obtain ⟨Z,hZ,H1,-⟩ := H0 hU hP
  refine ⟨fixedPoint Z,(completeFixed (I:=Unit) hZ ht.le).1,fixed_stencil Z,?_⟩
  intro c f S h B q T v N hs hv hb HD hS hC
  have ht' : laid G P S h Z=tensor G (fConditional S H B T) := H1 S h hs hS hC B T q v N hv hb HD
  have Hs : (laid G P S h Z).IsSymm := by
    rw [ht']; let F := Classical.choice (Tree.select S.ratio S.patch.odd_side)
    exact Matrix.isHermitian_iff_isSymm.mp (conditional_psd S F H hS (hP f) ha T hb hv HD).isHermitian
  exact ((completeFixed hZ ht.le).2 c (publish G P S h) Hs).trans ht'

lemma Figure.joints {G : Gauge} {P : Patch} {K : KernelChoices} {t A : ℝ} {H : Bed} {Z : veilCut G P} (hz : Figure G P K t A H Z)
    {x : ℝ} (ht : 0<t) (q : ShapeCut (dial P G) (dial P G) x) (h : swizzles q)
    {c f : Side} (S : StepData c f) (hP : S.patch=P) :
    let v:=laid G P S hP (q.draw Z); let b:=laid G P S hP Z
    v.IsSymm ∧ ∀ i j, |b i j-v i j| ≤ cheque (dial P G) t A x := by
  intro v b; let E:= publish G P S hP
  refine ⟨ticketMatch c _ hz.flip _ h,?_⟩
  intro i j; let m k := |(Z.acts c-(q.draw Z).acts c) (E i) k|
  exact (single_le_sum (f:=m) (fun _ _ => abs_nonneg _) (mem_univ (E j))).trans (order_exp hz.buys ht.le q c (E i)).2
end span

section columns
-- Mean charge: do not combine cross *output* data from κ estimator
-- choice with psi data unless same H & exact Roll, even if numerical
-- bands in Layered sink match.

abbrev veilPsi (L : Side) := Cross L (TypeFace 2) (TypeFace 2)
abbrev pathPsi (L : Side) := Co L (TypeFace 2)
def coverPsi {L : Side} (H B : Bed) (T : Towers L) : veilPsi L := Extra.Iteration.psi H B T none

def panePsi (G : Gauge) {c f : Side} (S : StepData c f) (M : veilPsi S.patch.L) := tensor G (installed S.ratio M)

def psiBudget (a : ℝ) :=
    (Fintype.card (TypeFace 2):ℝ)*((Fintype.card (TypeFace 2):ℝ)*(a*a)*a)
lemma psiBudget_nn (a : ℝ) (ha : 0≤a) : 0≤psiBudget a := by unfold psiBudget; positivity



private lemma everyColor {G : Gauge} {c f : Side} (A : Matrix (Body 2 f) (Body 2 c) ℝ)
    (i : FreeResolvent.Slot G f 2) :
    (∑ j, |tensor G A i j|) = ∑ j:Body 2 c, |A (i.1,i.2.1) j| := by
  simp only [tensor, Matrix.of_apply,Fintype.sum_prod_type,apply_ite abs,abs_zero]; simp

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}
lemma contour_uses (A : veilPsi S.patch.L) {s M : ℝ} (hs : 0<s) (hp : A.strip s M)
    (P : ShapeCut (pathPsi S.patch.L) (TypeFace 2) x) (i : FreeResolvent.Slot G f 2) :
    let c0:=panePsi G S A; let y:=panePsi G S (P.draw A)
    (∑ j, |y i j|) ≤ ticket (TypeFace 2) M ∧
      (∑ j, |c0 i j - y i j|) ≤ cheque (TypeFace 2) s M x ∧ ∀ j,
        lastHem x < separation (seat S 2 i) j.1 → y i j=0 := by
  intro c0 y; let z := (i.1,i.2.1); let e := splitCo S.ratio (TypeFace 2)
  obtain ⟨hA,hB⟩ := order_exp hp hs.le P c (e z)
  constructor
  · unfold y panePsi; rw [everyColor]; exact hA
  constructor
  · unfold c0 y panePsi
    let U:=installed S.ratio A; let V:=installed S.ratio (P.draw A)
    change (∑ j, |(tensor G U - tensor G V) i j|) ≤ _
    rw [← tensor_sub,everyColor]; exact hB
  intro j hj; unfold y panePsi tensor; rw [Matrix.of_apply]; split
  · apply enough_room P c
    rwa [show (e (i.1,i.2.1)).1=seat S 2 i from rfl]
  rfl
end columns
end YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.Cut
