import YM.RG08.Vale.Posh
/-!
# Simultaneous radial potential and polynomial site gauges

No tolerance. Finite-period approximations preserve the exact analytic
arc identities used, at every seam. Pass in display coefficients only.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {p m c: Side} {D d e j r n i k:ℕ}
abbrev Stage (r:ℕ) := Fin r → ℝ
def rung {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](x:Fin r→ E) : Stage r→L[ℝ] E := ∑ i, (ContinuousLinearMap.proj i).smulRight (x i)
lemma rung_at {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](x:Fin r→ E)(u:Stage r) : rung x u=∑ i,u i • x i := by rw [rung,_root_.sum_apply]; rfl
def bony (i:Fin r) : Stage r := Pi.single i 1
lemma rung_one {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](x:Fin r→ E)(i) : rung x (bony i)=x i := by
  rw [rung_at,sum_eq_single i]; · simp only [bony,Pi.single_eq_same,one_smul]
  · intro j _ hj; simp [bony,hj]
  simp

variable (X:Fin r→ Snap G d)(w:Fin r→ E4→G.Color) (m : Side)
def pedestal (x:Cover): Stage r→L[ℝ] G.Color := rung (fun i=> w i (Place.seat x))
def supportAt (x y:Cover)(a:Axis) : Stage r→L[ℝ] Place.EdgeRead G d :=
    (pedestal w x).prod ((pedestal w x-pedestal w y).prod ((road (Place.seat x) a).comp (rung X)))
abbrev seam (x:Site m)(a:Axis) := supportAt X w (lift x) (lift (x+step a)) a
def curtain (U:Stage r) : Link G m := fun p=> scent p.2.2 (Place.logo (seam X w m p.1 (axisEquiv.symm p.2.1) U))
def floorP : LeafPath (Stage r) (Loc G 1) := fun p U=> scent p.2.2 (Place.logo (supportAt X w p.1 (p.1+step (heap p).2) (heap p).2 U))
lemma curtain_fs (x : Site m) (i : Axis)(v : Stage r) : arm G m 1 (curtain X w m v) (x,coord i)=Place.logo (seam X w m x i v) := by
  ext1 j; rw [arm_apply]; unfold curtain; simp only [show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply _]; rfl
lemma curtain_sm : ContDiffAt ℝ ω (curtain X w m) 0 := by
  apply contDiffAt_pi.mpr; intro v
  let L:=seam X w m v.1 (axisEquiv.symm v.2.1)
  exact (scent v.2.2).contDiff.contDiffAt.comp _ ((show ContDiffAt ℝ ω (Place.logo (G:=G) (d:=d)) (L 0) from (map_zero L).symm ▸ Place.logo_smooth ..).comp (f:=L) 0 L.contDiff.contDiffAt)
lemma curtain_root : curtain X w m 0=0 := funext fun x=> by simp [curtain]
variable {m} in
lemma overarch (H:Hol G) : ∀ᶠ u:Stage r in 𝓝 0,input G m (curtain X w m u)= Lattice.gauge (fun x=>G.lieExp (pedestal w (lift x) u)) (input G m (studio G d m (rung X u))) := by
  have h (x: Site m)(a:Axis) : ∀ᶠ u:Stage r in 𝓝 0,input G m (curtain X w m u) (x,a)= Lattice.gauge (fun y=>G.lieExp (pedestal w (lift y) u)) (input G m (studio G d m (rung X u))) (x,a) := by
    let L:=seam X w m x a
    have he : Tendsto L (𝓝 0) (𝓝 0) := by simpa only [map_zero] using L.continuous.tendsto 0
    have hL : Tendsto (Place.peak ∘ L) (𝓝 0) (𝓝 1) := Tendsto.comp (by rw [← Place.peak_root G d]; exact (((G.continuous_mat.isClosedEmbedding G.mat_injective).isInducing.continuousAt_iff).2 (Place.peak_smooth G d).continuousAt).tendsto) he
    have hp : Tendsto (rung X) (𝓝 0) (𝓝 0):= by rw [← map_zero (rung X)]; exact (rung X).continuous.tendsto _
    filter_upwards [hL.eventually G.plog_right, hp.eventually (Film.leak H (d:=d) (lift x,a))] with u hU hA
    rw [encode_link,curtain_fs]
    change G.lieExp (G.plog (G.mat (Place.peak (L u))))= _; change G.lieExp (G.plog (G.mat (Place.peak (L u))))= _ at hU; rw [hU]; unfold Lattice.gauge; rw [encode_link]
    rw [show arm G m 1 (studio G d m (rung X u)) (x,coord a)=Film.lane (Place.seat (lift x)) a (rung X u) from by
      ext1 j; rw [arm_apply]; unfold studio screenR heap; dsimp only; rw [← coord_map,axisEquiv.symm_apply_apply]; rfl,hA]
    unfold Function.comp L seam supportAt Place.peak; simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,_root_.sub_apply,sub_sub_cancel]
    exact congr_arg (fun z=> G.lieExp (pedestal w (lift x) u)*z*(G.lieExp (pedestal w (lift (x+step a)) u))⁻¹) (congr_fun (Place.flight_test H (lift x,a) (rung X u)) 1)
  filter_upwards [eventually_all.mpr (fun i=>eventually_all.mpr (fun j=>h i j))] with x hx
  exact funext fun ⟨i,j⟩ => hx i j
lemma motionD {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (Q:E→L[ℝ] Place.EdgeRead G d)(p:G.ColorIndex) (i:ℕ)(x:Fin i→E) :
    iteratedFDeriv ℝ i (fun U=> scent p (Place.logo (Q U))) 0 x=scent p (iteratedFDeriv ℝ i (Place.logo (G:=G) (d:=d)) 0 (Q ∘ x)) := by
  have he : ContDiffAt ℝ i Place.logo (Q 0) := by rw [map_zero Q]; exact (Place.logo_smooth G d).of_le le_top
  have h := DFunLike.congr_fun ((scent p).iteratedFDeriv_comp_left (he.comp 0 Q.contDiff.contDiffAt) le_rfl) x
  rw [map_zero Q] at he
  exact h.trans (congr_arg (scent p) (DFunLike.congr_fun (Next.Foundations.jets_linear Q he) x))
lemma curtain_card (i : ℕ)(x: Fin i→ Stage r)(z:Site m)(p: TypeFace 1)(q:G.ColorIndex):
    iteratedFDeriv ℝ i (curtain X w m) 0 x (z,p,q) = scent q (iteratedFDeriv ℝ i (Place.logo (G:=G) (d:=d)) 0 ((seam X w m z (axisEquiv.symm p)) ∘ x)) := by
  let f: Link G m →L[ℝ] ℝ := ContinuousLinearMap.proj (z,p,q)
  exact (DFunLike.congr_fun (f.iteratedFDeriv_comp_left (curtain_sm ..) le_top).symm x).trans (motionD ..)
-- linear part
lemma align (x:Cover)(a:Axis) (i:Fin r) : supportAt X w x (x+step a) a (bony i)=
    (w i (Place.seat x),Place.jump (w i) (Place.seat x) a, Place.road (Place.seat x) a (X i)) := by simp [supportAt,rung_one,pedestal,Place.jump]
lemma summonsP (p:Fare G)(i:Fin r): fderiv ℝ (floorP X w p) 0 (bony i)=scent p.2.2 ((Place.jump (w i) + Place.sampled (X i)) (Place.seat p.1) (heap p).2) := by
  let a:=heap p
  have he:= motionD (supportAt X w a.1 (a.1+step a.2) a.2) p.2.2 1 (fun _=> bony i)
  unfold floorP; rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,Place.echoing] at he; dsimp only [Function.comp_apply] at he; rw [show a.1=p.1 from rfl,align] at he
  refine he.trans ?_; unfold Place.sampled; simp [add_comm,a]
end YM.RG08.Vale
