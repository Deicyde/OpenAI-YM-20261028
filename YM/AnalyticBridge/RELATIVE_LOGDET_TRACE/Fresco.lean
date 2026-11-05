import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Corners
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Paint

/-!
# The actual Gram passes the block-color rotation test

Location: projected INITIAL site in original common coordinates. If a row uses
reversed oriented data, it is still the real pull of all functions -- in
particular no rule that V tangent rotates like Q tangent. This is an identity
at fixed W/Σ/tags and V; rewrite whole color blocks before using.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet.Physical
open Filter Function Set Matrix MeasureTheory FreeResolvent Next.SectorChange Next.SectorChange.Motion
open Lattice RG Wilson Pressure Tree Precision Push.SectorMeasure Paint
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {M C Λ : ℝ} {o : Clip}
variable (z : Site c→G.El) (V : Config G c) (k : S.Choices) (s : Signed) (a : Directions G f)
    (T : Tube G S) (hS : S.patch.Branches S.kernel G)

section primitive
private lemma back_swing (z : Site f→G.El) : ∀ a : Directions G f, swing z⁻¹ (swing z a)=a := fun a=>funext fun i=> by
  simp_rw [swing_eval,← G.adjoint_mul,Pi.inv_apply, inv_mul_cancel, G.adjoint_one]

/-- Equivariance also for unused rows with default fderiv.
No smoothness assertion (appointed Taylor jets must pay separately). -/
private lemma altered {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A B : E→F} (T R : E →L[ℝ] E) (L Q : F→L[ℝ] F) (hl : RightInverse R T) (hq : LeftInverse Q L)
    (he : B ∘ T=L ∘ A) (x : E) : fderiv ℝ B 0 (T x) = L (fderiv ℝ A 0 x) := by
  by_cases h : DifferentiableAt ℝ A 0
  · have hw : B=L ∘ A ∘ R := by
      rw [← Function.comp_assoc,← he, Function.comp_assoc,show ⇑T ∘ ⇑R = id from hl.id]; rfl
    have ht : DifferentiableAt ℝ B 0 := by
      rw [hw]; exact L.differentiableAt.comp _ ((show DifferentiableAt ℝ A (R 0) from by rw [map_zero]; exact h).comp _ R.differentiableAt)
    have hg : fderiv ℝ (B ∘ T) 0=(fderiv ℝ B 0).comp T := by
      rw [fderiv_comp _ (show DifferentiableAt ℝ B (T 0) by rw [map_zero]; exact ht) T.differentiableAt,map_zero,T.fderiv]
    rw [he, fderiv_comp _ L.differentiableAt h,L.fderiv] at hg
    exact (congr_arg (fun u : E →L[ℝ] F => u x) hg).symm
  rw [fderiv_zero_of_not_differentiableAt h,fderiv_zero_of_not_differentiableAt]
  · simp
  intro hh; apply h
  have hf : A=Q ∘ B ∘ T := by rw [he,← Function.comp_assoc,show ⇑Q ∘ ⇑L=id from hq.id]; rfl
  rw [hf]; exact Q.differentiableAt.comp _ ((show DifferentiableAt ℝ B (T 0) by rw [map_zero]; exact hh).comp _ T.differentiableAt)
private lemma jet_swing (w : Site f→G.El) (u : G.El) {F H : Directions G f→G.Color} (h : ∀ a, H (swing w a)=G.adjoint u (F a))
    (a : Directions G f) : fderiv ℝ H 0 (swing w a)=G.adjoint u (fderiv ℝ F 0 a) := by
  have hh : ∀ a, swing w (swing w⁻¹ a)=a := fun a=>by simpa only [inv_inv] using back_swing w⁻¹ a
  exact altered (swing w) (swing w⁻¹) (G.adjoint u).toContinuousLinearMap (G.adjoint u⁻¹).toContinuousLinearMap hh
    (fun a=> (show G.adjoint u⁻¹ (G.adjoint u a)=a by rw [← G.adjoint_mul, inv_mul_cancel,G.adjoint_one])) (funext h) a

def wind (S : StepData c f) (z : Site c→G.El) (s : Signed) : Site f→G.El := fun i=> constantGauge z S.ratio (s.act i)
lemma rim : facade S s (gauge z V) (swing (constantGauge z S.ratio) a)=gauge (wind S z s) (facade S s V a) := by
  unfold facade; rw [← copied _ S.patch.odd_side, swing_increment,Work.F05.pull_gauge_zero]; simp [affine]; rfl
lemma rim0 : facade S s (gauge z V) 0=gauge (wind S z s) (facade S s V 0) := by simpa only [map_zero] using rim z V s (S:=S) 0

lemma plaque_tide (i : Cell f) : plaquetteJet S (gauge z V) s i (swing (constantGauge z S.ratio) a)=G.adjoint (wind S z s i.1)
    (plaquetteJet S V s i a) := by
  unfold plaquetteJet; apply jet_swing (H:=fun y=>G.curvature (faceValue (facade S s (gauge z V) y) i)); intro a
  rw [rim,face_gauge,G.curvature_conjugate]
include hS
lemma noise_tide (i : Bond c) : blockJet (gauge z V) k s i (swing (constantGauge z S.ratio) a) = G.adjoint (wind S z s (S.ratio.embed i.1))
    (blockJet V k s i a) := by
  unfold blockJet
  apply jet_swing (H:=fun y=>G.curvature (predictorTurn (gauge z V) k s i y)); intro a
  rw [← G.curvature_conjugate]
  unfold predictorTurn predictGroup
  rw [rim,rim0,(choice_gauge hS _ _ (wind S z s)).2,(choice_gauge hS _ _ (wind S z s)).2]
  unfold Lattice.gauge Function.comp; congr 1; group

-- slot gauge in the pulled formula
omit hS
def zenith (S : StepData c f) (z : Site c→G.El) (i : Slots S) :=
  Sum.elim (fun r : Twin f=>wind S z i.1 r.1.1) (fun r : Bond c=>wind S z i.1 (S.ratio.embed r.1)) i.2

include hS
lemma bump_flip (x : ℝ) (hT : T.up.Bounds o M C Λ) (i : Slots S) : Rows.bump T x (gauge z V) k (swing (constantGauge z S.ratio) a) i =
    G.adjoint (zenith S z i) (Rows.bump T x V k a i) := by
  obtain ⟨s,r|r⟩ := i
  · change Rows.faceKick T x (gauge z V) (swing _ _) s r = G.adjoint (wind S z s r.1.1) (Rows.faceKick ..)
    unfold Rows.faceKick; split
    next he =>
      let Q (l : Cell f) := plaquetteJet S V s l a
      let J:=(G.adjoint (wind S z s r.1.1)).toContinuousLinearMap
      change _=J (barrel T.up _ _ Q _)
      unfold barrel; rw [J.map_tsum (barrel_summed _ _ _ Q _ hT)]; apply tsum_congr; intro n
      dsimp only; split
      next hi =>
        let P:= (T.up.row r.1.2 n).2
        have ht : stop r.1.1 P.walk=(Work.F03.slotFace P r.1.1).1 := by
          unfold Work.F03.slotFace Slot.offset; rw [wrap_stop_cover, map_zero, add_comm]
          nth_rw 1 [show r.1.1=r.1.1+0 by rw [add_zero]]; rw [Work.E03.stop_add_left]
        rw [map_smul,rim0,travel_gauge,ht,plaque_tide,G.adjoint_mul,G.adjoint_mul,← G.adjoint_mul (wind _ _ _ _)⁻¹ (wind _ _ _ _),
          inv_mul_cancel,G.adjoint_one]; rfl
      next h => rw [map_zero]
    next he => rw [map_smul,plaque_tide]
  change Rows.noiseKick (gauge z V) k (swing _ a) s r = G.adjoint _ (Rows.noiseKick ..)
  unfold Rows.noiseKick; rw [map_neg,map_smul, noise_tide _ _ _ _ _ hS]; rfl
end primitive

-- only ever acts on orthonormal physical colors
def banner (u : G.El) : Square G.ColorIndex := Matrix.of fun i j=> G.adjoint u (EuclideanSpace.basisFun G.ColorIndex ℝ j) i
lemma banner_spins (u : G.El) : (banner (G:=G) u).transpose*banner u=1 := by
  let L:= G.adjoint u
  let Q : G.Color →ₗᵢ[ℝ] G.Color := { L with norm_map' := fun _=> G.norm_adjoint .. }
  let b:=EuclideanSpace.basisFun G.ColorIndex ℝ
  ext i j
  calc
    _ = inner ℝ (Q (b j)) (Q (b i)) := rfl
    _ = _ := by rw [LinearIsometry.inner_map_map,orthonormal_iff_ite.mp b.orthonormal]; simp only [Matrix.one_apply]; by_cases h : i=j <;> aesop
lemma flag_wind (u : G.El) (x : G.Color) (i : G.ColorIndex) : G.adjoint u x i=∑ j,banner u i j * x j := by
  let b:=EuclideanSpace.basisFun G.ColorIndex ℝ
  nth_rw 1 [← b.sum_repr x,map_sum]
  rw [WithLp.ofLp_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl; intro j _; rw [map_smul]; exact mul_comm _ _
lemma herald (i : Key G f) : swing (constantGauge z S.ratio) (axisPrice i)=∑ j,banner (G:=G) (z (place S i)) j i.2 • axisPrice (i.1,j) := by
  funext e
  rw [Finset.sum_apply]; simp_rw [on_axis,swing_eval]
  by_cases he : e=i.1
  · subst e
    simp only [Pi.smul_apply,Pi.single_eq_same]
    exact ((EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr (G.adjoint (z (place S i)) ((EuclideanSpace.basisFun G.ColorIndex ℝ) i.2))).symm
  simp [he, Pi.single_eq_of_ne]

def clockface (S : StepData c f) (z : Site c→G.El) (i : Bond f) : Square G.ColorIndex := banner (z (S.ratio.parent i.1))

def tender (x : ℝ) (r : Slots S) (i : Bond f) : Square G.ColorIndex := Matrix.of fun u j=> clue T k V x (i,j) (r,u)

include hS
lemma stacked (x : ℝ) (hT : T.up.Bounds o M C Λ) (r : Slots S) (i : Bond f) : tender (gauge z V) k T x r i= banner (zenith S z r)* tender V k T x r i*(clockface S z i).transpose := by
  let F (V : Config G c) := tender V k T x r i
  let Q:= clockface S z i; let W := gauge z V
  have he : F W*Q=banner (zenith S z r)*F V := by
    let L (W : Config G c) : Directions G f →ₗ[ℝ] G.Color := {
      toFun a:= Rows.slip • Rows.bump T x W k a r
      map_add' a b:= by rw [Rows.bump_add _ _ _ _ hT,Pi.add_apply,smul_add]
      map_smul' t a:= by rw [Rows.bump_smul _ _ _ _ hT,Pi.smul_apply,smul_comm]; rfl }
    have hl (a) : L W (swing (constantGauge z S.ratio) a)=G.adjoint (zenith S z r) (L V a) := by
      change Rows.slip • _=G.adjoint _ (Rows.slip • _); rw [map_smul,bump_flip _ _ _ _ _ hS x hT]
    ext u j
    have ht : L W (swing (constantGauge z S.ratio) (axisPrice (G:=G) (i,j))) = G.adjoint (zenith S z r) (L V (axisPrice (G:=G) (i,j))) := hl _
    rw [herald,map_sum] at ht
    rw [Matrix.mul_apply, Matrix.mul_apply]
    change _ = ∑ m, banner (G:=G) (zenith S z r) u m * L V (axisPrice (G:=G) (i,j)) m
    rw [← flag_wind (G:=G), ← ht,WithLp.ofLp_sum,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro m _; rw [map_smul]; exact mul_comm _ _
  have hr : Q*Q.transpose=1 := mul_eq_one_comm.mp (banner_spins (G:=G) _)
  change F W=banner _*F V*Q.transpose
  rw [← he, Matrix.mul_assoc,hr,Matrix.mul_one]

private lemma issuedRow (x : ℝ) (A : Stores S) (F : Forest S.ratio) (i j : Bond f) (h : openBond A F x i ∧ openBond A F x j) :
     block (AFull T A F x V k) i j=∑ r,(tender V k T x r i).transpose*tender V k T x r j := by
  ext u v
  rw [Matrix.sum_apply,block,of_apply,read_kernel T k _ _ _ _ hS (i,u) (j,v), if_pos h]
  change (∑ r : Slots S × G.ColorIndex,_)= _; rw [Fintype.sum_prod_type]; rfl
private lemma tacitRow (x : ℝ) (A : Stores S) (F : Forest S.ratio) (i j : Bond f) (h : ¬ (openBond A F x i ∧ openBond A F x j)) :
    block (AFull T A F x V k) i j=block (1:Square (Key G f)) i j := by
  ext u v; simp only [block,of_apply]; rw [read_kernel T k _ _ _ _ hS (i,u) (j,v),if_neg h]

/-- Even when using cut horizons. -/
theorem gauge_elation (x : ℝ) (A : Stores S) (F : Forest S.ratio) (hT : T.up.Bounds o M C Λ) :
    Elation (clockface S z) (AFull T A F x V k) (AFull T A F x (gauge z V) k) := by
  intro i j
  by_cases h : openBond A F x i ∧ openBond A F x j
  · rw [issuedRow _ _ _ hS _ _ _ i j h,issuedRow _ _ _ hS _ _ _ i j h,Finset.mul_sum,Finset.sum_mul]; refine Finset.sum_congr rfl fun r _=> ?_
    simp_rw [stacked z V k T hS x hT,transpose_mul,transpose_transpose,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (banner (zenith S z r)).transpose,banner_spins,Matrix.one_mul]
  have he : Moves (clockface S z) := fun i=>banner_spins (G:=G) (z (S.ratio.parent i.1))
  rw [tacitRow (gauge z V) k T hS x A F i j h,tacitRow V k T hS x A F i j h]
  exact Elation.colorless he i j
end YM.AnalyticBridge.RelativeLogdet.Physical
