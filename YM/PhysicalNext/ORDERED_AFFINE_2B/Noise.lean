import YM.Next.WARD_BIN.Coin
import YM.PhysicalNext.ORDERED_AFFINE_2B.Tests
import YM.Push.ABSOLUTE_SUMS.Mixed
/-!
# Recover the ACTUAL channel orientation for the noise slope in Frco

Use derivatives of true branch predictor on its active argument, with
channel law. For rows that would not be selected, prove both slopes
zero (doesn't require chart derivatives for untested branches).

Critical distinction: this is an isometry on the *a coefficient*. It
is not a rule to replace constants/w data by rotating them via the same
law. Keep constants at their original rows (and their own orientations).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Mapper
open Function Filter Set Lattice Wilson RG Pressure Precision Exterior Tree
open AnalyticBridge AnalyticBridge.ResetIncome SectorTools.ActualScalar
open Further Further.CurvedGaussianJets
open Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows
open Push.SectorMeasure Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {c f : Side} {G : Gauge} {S : StepData c f} (e : Plate G S) (A : Stores S)

/-- CLM used in taking these two ACTUAL derivatives. -/
def logVel : Action e A →L[ℝ] Directions G f :=
  ContinuousLinearMap.pi (fun (i : Bond f) => (ContinuousLinearMap.proj (SectorNext.Vacuum.FlatTree.wheel f i)) ∘L
    (Shape.translate (held e A) G).toContinuousLinearMap)
lemma velocity (x : Action e A) : logVel e A x=logTest e A x := comparing e A x

variable (k : S.Choices) (V : Config G c) (s : Signed) (i : Bond c) (x : Action e A) (hs : S.patch.Branches S.kernel G)

-- Canonical read at canonical endpoint. New-chart functional; motion e.g.
-- in nonuniform gauge does not change this equation.
def readQ (x : Action e A) := Shape.readBond (held e A) (replica S.ratio V) k i x

/-- The linear action required in every channel row IMBEDDING. -/
def coloring : G.Color →L[ℝ] G.Color :=
  if s.flip i.2 then -(G.adjoint ((Q k V (sendEdge s 0 i))⁻¹)).toContinuousLinearMap else ContinuousLinearMap.id ℝ _
lemma comp_color (a : Directions G c) : Motion.inChannel s (Q k V) a i = coloring k V s i (a (sendEdge s 0 i)) := by
  rw [Motion.in_eval]; unfold coloring; split <;> rfl

include hs
lemma turns : predictGroup V k s i (logVel e A x) =
    if s.flip i.2 then (readQ e A k V (sendEdge s 0 i) x)⁻¹ else readQ e A k V (sendEdge s 0 i) x := by
  unfold predictGroup facade
  rw [(Oriented.carry s hs k _).2,Motion.turn_read, velocity,←comparing]; rfl

lemma curvature_turn : G.curvature (predictorTurn V k s i (logVel e A x)) =
    coloring k V s i (G.curvature (readQ e A k V (sendEdge s 0 i) x * ((Q k V (sendEdge s 0 i))⁻¹))) := by
  unfold predictorTurn; rw [turns e A k V s i x hs]
  have hh := turns e A k V s i 0 hs; rw [map_zero] at hh; rw [hh]
  unfold readQ Shape.readBond; rw [Shape.restore_zero]
  unfold Q coloring; split; swap; · rfl
  let q := S.prediction (replica S.ratio V) k (sendEdge s 0 i)
  let p := Shape.readBond (held e A) (replica S.ratio V) k (sendEdge s 0 i) x
  change G.curvature (p⁻¹*q⁻¹⁻¹) = - (G.adjoint q⁻¹ (G.curvature (p*q⁻¹)))
  rw [show p⁻¹*q⁻¹⁻¹=q⁻¹*(p*q⁻¹)⁻¹*q⁻¹⁻¹ by group,G.curvature_conjugate,G.curvature_inv,map_neg]

omit hs in
lemma gauge_test (h : DifferentiableAt ℝ (fun y => G.mat (readQ e A k V i y)) 0) :
    HasDerivAt (fun r : ℝ => G.curvature (readQ e A k V i (r • x) * ((Q k V i)⁻¹)))
      (Shape.nozzle (held e A) (replica S.ratio V) k i x) 0 := by
  let u y := readQ e A k V i y; let q := Q k V i
  let f y := G.mat (u y); let v (r : ℝ) := u (r • x) * q⁻¹
  let X := fderiv ℝ f 0 x * G.mat q⁻¹
  have ht : HasDerivAt (fun r => G.mat (v r)) X 0 := by
    unfold v X; simp_rw [G.mat_mul]; exact (Shape.read_deriv _ f h x).mul_const _
  have hv : v 0=1 := by unfold v u q readQ Q Shape.readBond; rw [zero_smul,Shape.restore_zero,mul_inv_cancel]
  have hx := G.colorMat_project_self (G.tangent_generates ht (by rw [hv,G.mat_one]) (fun r=>⟨_,rfl⟩))
  exact Work.F03.curvature_of_hasDerivAt (V:=v) (c:=G.projectColor X) (by rwa [hx])

lemma read_auth (h : DifferentiableAt ℝ (fun a=> G.mat (predictGroup V k s i a)) 0) :
    DifferentiableAt ℝ (fun y => G.mat (readQ e A k V (sendEdge s 0 i) y)) 0 := by
  let L := logVel e A
  have hh : DifferentiableAt ℝ (fun y=> G.mat (predictGroup V k s i (L y))) 0 :=
    (show DifferentiableAt ℝ (fun y => G.mat (predictGroup V k s i y)) (L 0) from (map_zero L).symm ▸ h).comp _ L.differentiableAt
  unfold L at hh
  simp_rw [turns e A k V s i _ hs] at hh
  split at hh; swap; · exact hh
  simp_rw [G.mat_inv] at hh
  have ht := hh.star; simp only [star_star] at ht; exact ht

lemma bought_noise (h : DifferentiableAt ℝ (fun a=> G.mat (predictGroup V k s i a)) 0) :
    blockJet V k s i (logTest e A x) = coloring k V s i (Shape.nozzle (held e A) (replica S.ratio V) k (sendEdge s 0 i) x) := by
  let f a := predictorTurn V k s i a
  have hf : DifferentiableAt ℝ (fun a => G.mat (f a)) 0 := by
    unfold f predictorTurn; simp_rw [G.mat_mul]; exact h.mul_const _
  have hg : DifferentiableAt ℝ (fun a => G.curvature (f a)) 0 := by
    -- `Ball.paint` from CGJ as CLM
    simp_rw [← Ball.curvature_eq]; exact (Ball.paint G).differentiableAt.comp _ hf
  have he := Push.side (fun a => G.curvature (f a)) hg (logVel e A x)
  let L := coloring k V s i
  simp_rw [← map_smul (logVel e A),f,curvature_turn e A k V s i _ hs] at he
  have hL := L.hasFDerivAt.comp_hasDerivAt 0 (gauge_test e A k V (sendEdge s 0 i) x (read_auth e A k V s i hs h))
  unfold blockJet; rw [← velocity]; exact he.unique hL

private lemma flat_read (h : ¬curb (shots S e.x) A e.forest e.x s (.inr i)) :
    readQ e A k V (sendEdge s 0 i) x=readQ e A k V (sendEdge s 0 i) 0 := by
  have ht : predictGroup V k s i (logVel e A x)=predictGroup V k s i (logVel e A 0) := by
    apply noise_dep _ _ _ _ _ _ hs; intro j hj
    have hk : j∈shots S e.x s (.inr i) := (contains ..).mpr (by unfold roots; simp only [Sum.elim_inr]; unfold span; omega)
    rw [map_zero, velocity]; unfold logTest Rows.fresh; split
    · split
      · exact False.elim (h ⟨⟨⟨j,‹_›⟩,‹_›⟩,hk⟩)
      rfl
    rfl
  simp_rw [turns e A k V s i _ hs] at ht; split at ht; exact inv_injective ht; exact ht

-- Equate with the LIFT of fluid in the *actual physical* row.
lemma noise (hp : curb (shots S e.x) A e.forest e.x s (.inr i) →
      DifferentiableAt ℝ (fun a=> G.mat (predictGroup V k s i a)) 0) :
    Motion.inChannel s (Q k V) (solo (values e A k V x)) i = noiseKick V k (logTest e A x) s i := by
  rw [comp_color,price_noise]; simp_rw [map_neg,map_smul]; unfold noiseKick
  by_cases h : curb (shots S e.x) A e.forest e.x s (.inr i)
  · rw [bought_noise e A k V s i x hs (hp h)]
  have hz := skip_bump e.tube e.x V k A e.forest s (.inr i) (Next.SectorChange.tape (chartMap e A x)) hs h
  let p := sendEdge s 0 i
  have he : Shape.nozzle (held e A) (replica S.ratio V) k p x=0 := by
    have hd : fderiv ℝ (fun y=> G.mat (readQ e A k V p y)) 0 = 0 := by
      rw [show (fun y => G.mat (readQ e A k V p y)) = (fun _ => G.mat (readQ e A k V p 0)) from funext fun _=> congr_arg _ (flat_read e A k V s i _ hs h)]; exact fderiv_const_apply ..
    unfold Shape.nozzle; change G.projectColor (fderiv ℝ _ 0 x * _) = _
    change G.projectColor (fderiv ℝ (fun y => G.mat (readQ e A k V p y)) 0 x * G.mat ((Q k V p)⁻¹)) = 0
    rw [hd]; simp
  rw [he,map_zero,smul_zero,neg_zero]; exact hz.symm
end YM.PhysicalNext.OrderedAffine2B.Mapper
