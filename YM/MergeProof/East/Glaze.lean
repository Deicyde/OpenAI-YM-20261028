import YM.Extra.MULTISOURCE_TRAJECTORIES.Service
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Symbol
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Transplant
import YM.Next.RANK.GlowLine
import YM.Next.RANK.Pin


/-!
# Same winding with base relabel

Keep finite stencil and radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.East
open Function Lattice Wilson RG Labels Source Source.Drops Spindle  Further.CorrectedLift.Compass
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {n k p d b:ℕ}

def swing (s:Signed)(x:Spindle.Turn b):Turn b:=
    ⟨Face.send s 0 x.val, by
      obtain ⟨x,hx⟩:=x; change Face.send s 0 x ∈ Device b
      rw [show Device b = Axial.faceSet (box b) from rfl,← Axial.face_set_image (box b) s (box_covariant b s)]
      exact Finset.mem_image_of_mem _ hx⟩
lemma swing_flies (s:Signed) : Injective (swing (b:=b) s) := fun _ _ h=> Subtype.ext (Face.injective_send s 0 (Subtype.ext_iff.mp h))

def crown (p:Turn b):RG.Slot:=⟨Spindle.paths p.val.1,p.val.2⟩
lemma inner (U : CoverConfig G) (p:Turn b): G.curvature (Spindle.used U p)=(crown p).eval U:=by unfold Spindle.used central; rw [Lattice.face_gauge,G.curvature_conjugate,Slot.eval]; simp only [crown,Slot.offset,Spindle.stops];rfl
lemma prize (N:Side)(s:Signed)(p:Turn b):Face.send s 0 (wrap N p.val.1,p.val.2)=(wrap N (swing s p).val.1,(swing s p).val.2):=by
    refine Prod.ext ?_ rfl
    have he (x:Cover)(a b : Step): wrap N (atFace x a b)=atFace (wrap N x) a b:=by unfold atFace;cases h : a.neg <;>cases h' : b.neg <;>simp [wrap_vec]
    change atFace (affine _ _ (wrap _ p.val.1)) _ _=wrap N (atFace _ _ _); rw [he]; simp only [affine,add_zero,wrap_signed]
lemma bent (G : Gauge) (s:Signed) (p:Turn b): let z:=bend G s (crown p)
    (z.offset,z.plaq)=(swing s p).val := by
    intro z
    let x:=z.offset;let y:=(swing s p).val.1
    let m:= Finset.univ.sup (fun i=> (x i).natAbs+(y i).natAbs)
    let N:Side:= ⟨2*(m+2),by positivity⟩
    have ht:= (Further.CorrectedLift.Compass.stamp (G:=G) (crown p) s).choose_spec.2.2 N
    change (wrap N z.offset,z.plaq)=Face.send s 0 (wrap N (crown p).offset,(crown p).plaq) at ht
    rw [show (crown p).offset=p.val.1 from Spindle.stops _,show (crown p).plaq=p.val.2 from rfl, prize] at ht
    have hh(i): (x i).natAbs + (y i).natAbs≤m := Finset.le_sup (f:=fun i=>(x i).natAbs + (y i).natAbs) (Finset.mem_univ i)
    have hB:= congr_arg Prod.snd ht; refine Prod.ext ?_ hB
    change x=y
    refine wrap_injOn N ?_ ?_ (congr_arg Prod.fst ht)
    · intro i; have h':= hh i; change -(↑(2*(m+2)):ℤ)<2*x i ∧ 2*x i ≤ ↑(2*(m+2)); omega
    intro i; have h':= hh i; change -(↑(2*(m+2)):ℤ)<2*y i ∧ 2*y i ≤ ↑(2*(m+2)); omega

private lemma takes_woven (H : Hol G) (v : Slot) (Z : Snap G d) (s:Signed):
    takes H d v (turning s d G Z) = wind s v.plaq • takes H d (bend G s v) Z := by
  unfold takes; rw [← Further.CorrectedLift.Compass.rotated]
  have he : expand d (turning s d G Z) = changedJet (fun i : ℕ => Taylor.turn (G:=G) (j:=i) s.ortho⁻¹) (expand d Z) := by
    funext j; by_cases hj : j<d-1 <;> simp only [expand,hj,changedJet, ↓reduceDIte] <;> first | rfl | simp
  rw [he,← Work.G01.swirls_of_flow H s]

set_option maxHeartbeats 600000 in
lemma takes_deriv (H:Hol G)(v:Slot) (d:ℕ)(s:Signed)(A:Snap G d):
   Blurb H d v (turning s d G A) =wind s v.plaq • Blurb H d (bend G s v) A:= by
    let f := takes H d v;let h:=takes H d (bend G s v);let T:=turning s d G
    let r:= wind s v.plaq • ContinuousLinearMap.id ℝ G.Color
    have hs : f ∘ T=r ∘ h:= funext fun x=>takes_woven H v x s
    have hL : DifferentiableAt ℝ f (T 0):=by rw [map_zero]; exact (Work.G02.slotGerm H d v).1.differentiableAt
    have hB : DifferentiableAt ℝ h 0:= (Work.G02.slotGerm H d _).1.differentiableAt
    have he:= fderiv_comp (𝕜:=ℝ) (0:Snap G d) hL T.differentiableAt
    rw [hs,fderiv_comp 0 r.differentiableAt hB, ContinuousLinearMap.fderiv,ContinuousLinearMap.fderiv, T.map_zero] at he
    exact DFunLike.congr_fun he.symm A
lemma lustre (H:Hol G)(s:Signed)(x:Turn b)(A:Snap G d): lamp d (turning s d G A) x= wind s x.val.2 • lamp d A (swing s x) := by
    have hx:= takes_deriv H (crown x) d s A
    rw [(Work.G02.slotGerm ..).2,(Work.G02.slotGerm ..).2] at hx
    let z:=bend G s (crown x)
    have hh : glow A z=lamp d A (swing s x) := by unfold glow lamp oneGlow; rw [← (show (z.offset,z.plaq)= _ from bent G s x)]
    apply Eq.trans _ (hx.trans ?_)
    · unfold lamp oneGlow glow; rw [show (crown x).offset=x.val.1 from Spindle.stops ..];rfl
    exact congr_arg (wind s _ • ·) hh
end YM.Next.Rank.East
