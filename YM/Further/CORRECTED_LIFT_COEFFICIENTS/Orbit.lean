import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Deliver
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.TurnCorner
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails

/-!
# Rotated k-chart; no off-stencil identification without links

Must still buy costs on these actual rotated layouts (also Probed angles
and the D_t Taylor costs). -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.Compass
open Filter Function Set Lattice Wilson RG Source Source.Drops Labels Cells Extraction
open Push.Corrected Push.Corrected.Issue Push.CutoffProjectors Next.Foundations
open ProjectorNext.Equivariance
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} {P : BudgetPoint} {d t : ℕ}

-- fixed before L
variable (G) in
def bend (s : Signed) (v : Slot) := (stamp (G:=G) v s).choose
lemma lesser (G : Gauge) (s : Signed) (v : Slot) : (bend G s v).walk.length ≤ v.walk.length + 2 :=
    (stamp (G:=G) v s).choose_spec.1
lemma rotated (s : Signed) (v : Slot) (U : CoverConfig G) :
    v.eval (pull s 0 U)=wind s v.plaq • (bend G s v).eval U := (stamp (G:=G) v s).choose_spec.2.1 U
lemma pocket (s : Signed) (v : Slot) (U : Config G n) : v.atSite (pull s 0 U) 0=wind s v.plaq • (bend G s v).atSite U 0 := by
  unfold Slot.atSite; rw [expandAt_pull,rotated]; simp [affine]

variable (B : Board G n P t) (s : Signed)

def retract : B.Eye →L[ℝ] B.Eye := LinearMap.toContinuousLinearMap (LinearMap.pi fun i => wind s (B.leg i).plaq • LinearMap.proj i)
def invert : Directions G n →L[ℝ] Directions G n := LinearMap.toContinuousLinearMap (pulledDirection s⁻¹ 0 (1:Config G n))

def vacancy : Prop := ∀ i, ∀ x∈(bend G s (B.leg i)).stencil, ∀ j : Axis,20*((x j).natAbs+1)≤n.val

private lemma pulled_back (U : Config G n) : pull s⁻¹ 0 (pull s 0 U)=U := by rw [pull_pull]; simp [affine]
private lemma room_back : (B.cube.image (affine s 0)).image (affine s⁻¹ 0)=B.cube := by
  rw [Finset.image_image]; simp [comp_def,affine]

private lemma inkPull (Y : B.Eye) : pull s⁻¹ 0 (B.showAt Y) = increment (1:Config G n)
    (P.threshold • (invert s) (B.replay Y)) := by
  rw [Board.showAt, pull_increment,pull_constant, map_smul]; rfl

def arrow (hp : vacancy B s) : Board G n P t where
  size := B.size
  leg i := bend G s (B.leg i)
  cube := B.cube.image (affine s 0)
  replay := invert s ∘ (B.replay ∘ retract B s)
  empty := by simp [B.empty]
  nice := by
    have h := (B.empty); let A := retract B s
    have he : ContDiffAt ℝ t B.replay (A 0) := by rw [map_zero]; exact B.nice
    exact (invert s).contDiff.contDiffAt.comp 0 (he.comp 0 A.contDiff.contDiffAt)
  fits := hp
  authentic := by
    let L := pull (K:=G.El) s (0:Site n)
    have he : Tendsto L (𝓝 1) (𝓝 1) := by simpa only [L,pull_constant] using (continuous_pull s 0).tendsto (1:Config G n)
    refine (he.eventually B.authentic).mono ?_
    rintro U ⟨v,hv⟩
    have hw : Agrees _ (pull s⁻¹ 0 (gauge v (pull s 0 U))) (pull s⁻¹ 0 (B.showAt (B.input (pull s 0 U)))) :=
      agrees_pull s⁻¹ (n:=n) 0 (B.cube.image (affine s 0)) (by rw [room_back]; exact hv)
    rw [ProjectorNext.Equivariance.pull_gauge, pulled_back, inkPull] at hw
    let X : B.Eye := P.threshold⁻¹ • fun i => (bend G s (B.leg i)).atSite U 0
    have hx : B.input (pull s 0 U) = retract B s X := by
      funext i
      change P.threshold⁻¹ • (B.leg i).atSite (pull s 0 U) 0=wind s (B.leg i).plaq • (P.threshold⁻¹ • _)
      rw [pocket]; exact smul_comm ..
    rw [hx] at hw
    exact ⟨_,hw⟩



section shadow
variable {C : Family G} {m p N : ℕ} (B : Screen C m p t)


end shadow
end YM.Further.CorrectedLift.Compass
