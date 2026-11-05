import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Schur




set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Flat *cut* precision determinant, all actual tree tags

Check the price is the same even without comparing to the uncut determinant
and even for a slice with different Free indices. Use F05's actual group
transition at flat (toll receipt on arbitrary LocalRatio witnesses in
particular), before comparing the linearized reads. Together with the Gap
results licenses the common-tag A-flat det price factoring out of a tree
mixture. (All mixtures in Push are just on fixed given trees.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Native
open Function Filter Lattice RG Wilson Precision Exterior Tree MeasureTheory Matrix NormedSpace
  YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
  YM.Next.Fluctuations YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented Rows Gaussian YM.Work.F03
open YM.Work.F05
open scoped Topology BigOperators Classical InnerProductSpace ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) {E σ Λ : ℝ} {p : Clip}
variable (F H : Forest S.ratio) (k : S.Choices)

def lay : AxisChart G F →L[ℝ] Directions G f :=
  ((LinearMap.pi fun i : Bond f => if hi : i∈F.trunks then (0 : AxisChart G F →ₗ[ℝ] G.Color) else LinearMap.proj (⟨i,hi⟩ : F.Free))).toContinuousLinearMap

private def blank : Stores S := ⟨∅,∅,∅⟩

private lemma cleared (x : ℝ) (i : F.Free) : ¬chill (blank (S:=S)) x F i := by
  simp [chill,Stores.dome,Stores.place,halo_spec,blank]

def every (x : ℝ) : F.Free ≃ Active (blank (S:=S)) x F where
  toFun i := ⟨i,cleared F x i⟩
  invFun i := i.val
  left_inv _ := rfl
  right_inv _ := rfl

def lineEquiv (x : ℝ) : Key F G ≃ In x blank F (G:=G) := Equiv.prodCongr (every F x) (Equiv.refl _)

def seed (x : ℝ) : Matrix (Receipt G S) (Key F G) ℝ := Matrix.of fun i j => tape.symm (slip • bump T x 1 k (lay F (axisPrice j))) i

def kinetic (x : ℝ) := let D:=seed T F k x; D.transpose * D

/-- Show this counting matrix is exactly affvd with no holes and V=one
on regular positions, not getting a receipt for it from an uncut one. -/
lemma origin (x : ℝ) (h : S.patch.Branches S.kernel G) :
    (Rows.move T x 1 k (shots S x) (blank (S:=S)) F).submatrix id (lineEquiv F x)=seed T F k x := by
  let W:=shots S x; let v := lineEquiv (G:=G) F x
  have he (i : Key F G) : fresh x W (blank (S:=S)) F (axisPrice (v i)) = lay F (axisPrice i) := by
    funext b
    unfold fresh; split
    next h =>
      let j : F.Free := ⟨b,h⟩ -- neg swapped
      rw [dif_pos (cleared F x j),on_axis,on_axis]
      unfold lay; simp [h]
      by_cases hj : j=i.1
      · have hl' : (v i).1=(every F x) j := by rw [hj]; rfl
        change Pi.single _ _ ((every F x) j)=_
        have ht : (v i).2=i.2 := rfl
        rw [ht,hl',Pi.single_eq_same]
        change _ = Pi.single (M:=fun _ => G.Color) i.1 _ j
        rw [hj,Pi.single_eq_same]
      have hl' : (every F x) j ≠ (v i).1 := fun H => hj ((every F x).injective H)
      change Pi.single (M:=fun _ => G.Color) _ _ ((every F x) j)=Pi.single (M:=fun _ => G.Color) _ _ j
      rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hl']
    next h => unfold lay; simp [not_not.mp h]
  ext i j
  unfold Matrix.submatrix Rows.move seed
  simp_rw [Matrix.of_apply,selected_all _ _ _ _ _ _ _ h]; rw [he]; rfl

lemma ground_gram (x : ℝ) (h : S.patch.Branches S.kernel G) :
    (Rows.gram T x 1 k (shots S x) (blank (S:=S)) F).submatrix (lineEquiv F x) (lineEquiv F x)=kinetic T F k x := by
  unfold kinetic Rows.gram
  rw [← Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _) _,show ((Equiv.refl _):Receipt G S→_) = id from rfl,← transpose_submatrix,origin T F k x h]



section turn

private lemma adjoint_continuous : Continuous (fun z : G.El × G.Color => G.adjoint z.1 z.2) := by
  let F := G.colorMat.toContinuousLinearMap
  change Continuous (fun z : G.El × G.Color => G.projectColor (G.conjugate z.1 (G.colorMat z.2)))
  apply G.projectColor.toContinuousLinearMap.continuous.comp (f:=fun z : G.El × G.Color => G.conjugate z.1 (G.colorMat z.2))
  unfold Gauge.conjugate
  exact ((G.continuous_mat.comp continuous_fst).mul (F.continuous.comp continuous_snd)).mul ((continuous_star.comp G.continuous_mat).comp continuous_fst)

private def test (a : AxisChart G F) := F.drape (exposure F 0 a)

private lemma test_eq (a : AxisChart G F) : test F a = increment 1 (lay F a) := by
  funext i
  by_cases he : i∈F.trunks
  · rw [test,F.on_tree (exposure F 0 a) (⟨i,he⟩ : ↥F.trunks)] -- rewrite coe issue
    unfold increment lay
    simp [he]
  let k : F.Free := ⟨i,he⟩
  have hp : test F a i=exposure F 0 a k := F.off_tree (exposure F 0 a) k
  rw [hp]
  unfold increment lay exposure; simp [he]
  rfl

private lemma test_zero : test F (0:AxisChart G F)=1 := by rw [test_eq,map_zero,Motion.increment_zero]

private def stepX (a : AxisChart G F) := switch F H 0 a

private lemma step_zero : stepX F H (0:AxisChart G F) = 0 := switch_zero ..

private lemma step_jet : ContDiffAt ℝ ω (stepX F H (G:=G)) 0 := hold_jet (switch_jet F H)

private lemma test_turns : (test H ∘ stepX F H (G:=G)) =ᶠ[𝓝 0]
    (fun a => Lattice.gauge (H.foldAt (test F a)) (test F a)) := by
  filter_upwards [hold_near (exposure_switch F H (G:=G))] with a ha
  change exposure H _ (stepX F H a)=_ at ha
  unfold Function.comp test; rw [ha]
  exact Profiles.wears H _

private def run := fderiv ℝ (stepX F H (G:=G)) 0

private lemma run_p (s : Signed) (i : Cell f) (a : AxisChart G F) :
    plaquetteJet S 1 s i (lay H (run F H a))=plaquetteJet S 1 s i (lay F a) := by
  let P (U : Config G f) := G.curvature (faceValue (pull s 0 U) i)
  let Q (K : Forest S.ratio) := P ∘ test K
  have he (K : Forest S.ratio) : Q K=(fun y => G.curvature (faceValue (facade S s 1 y) i)) ∘ lay K := by
    funext a; unfold Q P Function.comp; rw [test_eq]; dsimp only [facade]; rw [replica_one]
  have hi (K : Forest S.ratio) : ContDiffAt ℝ ω (Q K) 0 := by
    rw [he]
    have h0 := (Motion.plaquette_turn s (1:Config G c) i (S:=S) (LocalJet.face_smooth _ _ (G:=G)).contDiffAt).1
    apply ContDiffAt.comp (f:=(lay K)) 0 _ (lay K).contDiff.contDiffAt
    rw [map_zero]; exact h0
  have hv (K : Forest S.ratio) (a : AxisChart G K) : fderiv ℝ (Q K) 0 a=plaquetteJet S 1 s i (lay K a) := by
    rw [he,fderiv_comp _ _ (lay K).differentiableAt,map_zero,(lay K).fderiv]; rfl
    rw [map_zero]; exact ((Motion.plaquette_turn s _ i (LocalJet.face_smooth _ _).contDiffAt).1).differentiableAt (by simp)
  have ht (K : Forest S.ratio) : Q K 0=0 := by
    unfold Q P Function.comp; rw [test_zero]
    have hp : pull s 0 (1:Config G f)=1 := by funext; unfold pull Step.read; split <;> simp
    change G.curvature (faceValue (pull s 0 1) i) = 0; rw [hp,show faceValue (1:Config G f) i=1 by rw [← link_one (G:=G)]; exact YM.Push.stroll_zero ..,G.curvature_unit]
  have hz : fderiv ℝ (Q H ∘ stepX F H (G:=G)) 0 a = plaquetteJet S 1 s i (lay H (run F H a)) := by
    rw [fderiv_comp _ _ ((step_jet F H).differentiableAt (by simp)),step_zero,ContinuousLinearMap.comp_apply,hv]; rfl
    rw [step_zero]; exact (hi H).differentiableAt (by simp)
  rw [← hz, ← hv F]
  have hlim (q : AxisChart G F → G.Color) (hq : DifferentiableAt ℝ q 0) (h0 : q 0=0) :
      Tendsto (fun t : ℝ => t⁻¹ • q (t • a)) (𝓝[≠] 0) (𝓝 (fderiv ℝ q 0 a)) := by
    simpa [h0] using! (hasDerivAt_iff_tendsto_slope_zero.mp (YM.Push.side q hq a))
  apply tendsto_nhds_unique (hlim (Q H ∘ stepX F H)
    ((show ContDiffAt ℝ ω _ _ from ContDiffAt.comp _ (by rw [step_zero]; exact hi H) (step_jet F H)).differentiableAt (by simp))
      (by simp only [Function.comp_apply,step_zero,ht]))
  have hm : Tendsto (fun v : ℝ => v • a) (𝓝[≠] 0) (𝓝 0) := by
    simpa using! (show Continuous fun v : ℝ => v • a from by fun_prop).tendsto 0 |>.mono_left (nhdsWithin_le_nhds (s:=({0}ᶜ:Set ℝ)))
  let Y := fun u : AxisChart G F => H.foldAt (test F u) (affine s 0 i.1)
  have hy : Continuous (test F (G:=G)) := F.continuous_drape.comp ((exposure_continuous F (G:=G)).comp (f:=fun y=>(0,y)) (continuous_const.prodMk continuous_id))
  have hw : Tendsto (fun v : ℝ => Y (v • a)) (𝓝[≠] 0) (𝓝 1) := by
    have hx : Continuous Y := (H.folds _).comp hy
    have hl : Y 0=1 := by
      unfold Y Tree.Forest.foldAt; rw [test_zero,← link_one (G:=G),YM.Push.stroll_zero,inv_one]
    simpa only [hl] using! (hx.tendsto _).comp hm
  have hh := adjoint_continuous.continuousAt.tendsto.comp (hw.prodMk_nhds (hlim (Q F) ((hi F).differentiableAt (by simp)) (ht F)))
  dsimp only at hh
  rw [G.adjoint_one] at hh
  refine hh.congr' ?_
  filter_upwards [hm.eventually (test_turns F H)] with t hi
  change test H (stepX F H (t • a)) = _ at hi
  dsimp only [Function.comp,Q,P,Y,Prod.fst,Prod.snd]
  rw [hi,pull_gauge_zero,face_gauge,G.curvature_conjugate]; exact map_smul ..
private lemma run_b (s : Signed) (i : Bond c) (a : AxisChart G F) (h : S.patch.Branches S.kernel G) :
    blockJet 1 k s i (lay H (run F H a)) = blockJet 1 k s i (lay F a) := by
  let P (U : Config G f) := G.curvature (S.prediction (pull s 0 U) (choice s k) i)
  let Q (K : Forest S.ratio) := P ∘ test K
  let g := fun y => G.curvature (predictorTurn (1:Config G c) k s i y)
  have h1 : predictGroup (1:Config G c) k s i 0 = 1 := by
    rw [predictGroup,Flat.facade_all]
    have hz : pulled (Flat.labels (0:Directions G f)) s=0 := by funext v; unfold pulled Flat.labels; dsimp only [Pi.zero_apply]; split <;> simp
    rw [hz,link_one]; exact YM.Push.settled S h i _
  have hm (U : Config G c) (i : Bond c) : pull s 0 U i = if s.flip i.2 then (U (sendEdge s 0 i))⁻¹ else U (sendEdge s 0 i) := Motion.turn_read s U i
  have he (K : Forest S.ratio) : Q K=g ∘ lay K := by
    funext a; unfold Function.comp Q; unfold Function.comp P g predictorTurn
    rw [test_eq, h1, inv_one,mul_one]; unfold predictGroup facade; rw [replica_one]
  have H1 : ContDiffAt ℝ ω g 0 := by
    apply Next.Fluctuations.curvature_diff_mat
    unfold predictorTurn; rw [h1]
    simp only [inv_one,mul_one,predictGroup, Flat.facade_all]
    have hz : pulled (Flat.labels (0:Directions G f)) s=0 := by funext v; unfold pulled Flat.labels; dsimp only [Pi.zero_apply]; split <;> simp
    have he := YM.Push.prediction_cont S h i (choice s k)
    rw [← hz] at he
    exact he.comp (f:=fun a => pulled (Flat.labels a) s) 0 (Flat.labels_pull_smooth s).contDiffAt
  have hi (K : Forest S.ratio) : DifferentiableAt ℝ (Q K) 0 := by
    rw [he]
    apply DifferentiableAt.comp _ _ (lay K).differentiableAt
    rw [map_zero]; exact H1.differentiableAt (by simp)
  have hv (K : Forest S.ratio) (a : AxisChart G K) : fderiv ℝ (Q K) 0 a=blockJet 1 k s i (lay K a) := by
    rw [he, fderiv_comp _ _ (lay K).differentiableAt,map_zero,(lay K).fderiv]; rfl
    rw [map_zero]; exact H1.differentiableAt (by simp)
  have H2 : Q H ∘ stepX F H =ᶠ[𝓝 0] Q F := by
    filter_upwards [test_turns F H (G:=G)] with a ha
    dsimp only [Function.comp,Q,P]
    rw [show test H (stepX F H a)=_ from ha]
    simp_rw [(carry s h k _).2,(choice_gauge h _ k _).2]
    rw [show Lattice.gauge (H.foldAt (test F a) ∘ S.ratio.embed) (S.prediction _ k)=S.prediction (test F a) k from ?_]
    funext i; simp only [Lattice.gauge,Function.comp_apply,Tree.Forest.fold_root,one_mul,inv_one,mul_one]
  rw [← hv, ← hv]
  have ht : DifferentiableAt ℝ (Q H) (stepX F H 0) := (step_zero F H).symm ▸ hi H
  rw [show fderiv ℝ (Q H) 0 (run F H a)=fderiv ℝ (Q H ∘ stepX F H) 0 a from ?_, H2.fderiv_eq]
  rw [fderiv_comp _ ht ((step_jet F H).differentiableAt (by simp)),step_zero]; rfl

private lemma run_bump (r : ℝ) (a : AxisChart G F) (h : S.patch.Branches S.kernel G) :
    bump T r 1 k (lay H (run F H a))=bump T r 1 k (lay F a) := by
  funext i; obtain ⟨s,j|j⟩ := i
  · simp only [bump,Sum.elim_inl,faceKick]; split
    next hh => simp_rw [run_p]
    rw [run_p]
  simp only [bump,Sum.elim_inr,noiseKick,run_b F H k s j a h]

lemma seed_mass (x : ℝ) (hT : T.up.Bounds p σ E Λ) (a : Prices G F.Free) :
    seed T F k x *ᵥ a=tape.symm (slip • bump T x 1 k (lay F (tape a))) := by
  let A : AxisChart G F →ₗ[ℝ] LogArray G (Slots S) :=
    { toFun := fun a => bump T x 1 k (lay F a)
      map_add' := fun a b => by rw [(lay F).map_add,bump_add _ _ _ _ hT]
      map_smul' := fun i a => by rw [(lay F).map_smul,bump_smul _ _ _ _ hT]; rfl }
  let F₀ := ((colors (ι:=Slots S) (G:=G)).symm.toLinearMap ∘ₗ (slip • A)) ∘ₗ colors.toLinearMap
  have he : LinearMap.toMatrix' F₀=seed T F k x := by
    ext i j; rw [LinearMap.toMatrix'_apply]; rfl
  rw [← he,LinearMap.toMatrix'_mulVec]; rfl

/-- Simultaneously reindex the destination by the F05 isomorphism
*before* taking chart derivative. -/
private def price (e : F.Free ≃ H.Free) := LinearMap.toMatrix'
  ((colors (G:=G) (ι:=F.Free)).symm.toLinearMap ∘ₗ
       ((fderiv ℝ (YM.Work.F05.move (G:=G) e 0) 0).toLinearMap ∘ₗ colors.toLinearMap))

private lemma pulls (x : ℝ) (h : S.patch.Branches S.kernel G) (e : F.Free ≃ H.Free) (hT : T.up.Bounds p σ E Λ) :
    (seed T H k x).submatrix id (onKey e) * price F H e = seed T F k x := by
  let t := price F H e (G:=G)
  let L := fderiv ℝ (YM.Work.F05.move (G:=G) e (0:Dir G c)) 0
  have he (a : AxisChart G F) (i : F.Free) : (index e a) (e i)=a i := index_apply e ..
  have hs (a : Prices G F.Free) : tape (t *ᵥ a)=L (tape a) := by unfold t price; rw [LinearMap.toMatrix'_mulVec]; exact colors.apply_symm_apply _
  have ht (v : AxisChart G F) : index e (L v) = run F H v := by
    unfold L run stepX
    have hf := hold_jet (move_jet e (G:=G)) (x:=(0 : Dir G c)) (y:= (0:AxisChart G F))
    have hx := move_eq (G:=G) e 0
    simp_rw [hx,fderiv_comp _ (index e).differentiableAt (hf.differentiableAt (by simp)), ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
  have hh (a : Prices G F.Free) :
      ((seed T H k x).submatrix id (onKey e)*t) *ᵥ a = tape.symm (slip • bump T x 1 k (lay F (tape a))) := by
    let Y : AxisChart G H := index e (tape (t *ᵥ a))
    have hi (i : Key F G) : tape.symm Y (onKey e i)=(t *ᵥ a) i := by
      change (index e _ (e i.1)) i.2 = _; rw [he,tape_ap]
    rw [← mulVec_mulVec]
    have hr : (seed T H k x).submatrix id (onKey e) *ᵥ (t *ᵥ a)=seed T H k x *ᵥ (tape.symm Y) := by
      funext i
      unfold mulVec dotProduct
      rw [← (onKey (G:=G) e).sum_comp (fun j => (seed T H k x i j)*(tape.symm Y j))]
      simp only [Matrix.submatrix,Matrix.of_apply,id_eq,hi]; rfl
    rw [hr,seed_mass T H k x hT, tape.apply_symm_apply,show Y=_ from ?_,run_bump T F H k _ _ h]
    unfold Y; rw [hs,ht]
  apply Matrix.toLin'.injective
  apply LinearMap.ext; intro a
  change (_ * _) *ᵥ a = seed T F k x *ᵥ a
  rw [seed_mass T F k x hT]; exact hh a

private lemma unscaled (e : F.Free ≃ H.Free) (J : ChartRatio G) (hJ : LocalRatio J) :
    |(price F H (G:=G) e).det|=1 := by
  have he := (toll_switch (P:=J) e hJ).self_of_nhds
  dsimp only [Prod.fst_zero,Prod.snd_zero] at he
  rw [switch_zero] at he
  simp only [YM.Work.F05.toll,Pi.zero_apply,hJ.anchored,Finset.prod_const_one,mul_one] at he
  apply Eq.trans ?_ he.symm
  unfold price; rw [LinearMap.det_toMatrix']; congr 1
  exact LinearMap.det_conj _ colors.symm

/-- Same path data and physical R even if forest changes. -/
lemma common (J : ChartRatio G) (hJ : LocalRatio J) (x : ℝ) (hT : T.up.Bounds p σ E Λ)
    (h : S.patch.Branches S.kernel G) (u : S.Choices) :
    Matrix.det (kinetic T F k x) = Matrix.det (kinetic T H u x) := by
  have hz (a : Directions G f) : bump T x 1 u a = bump T x 1 k a := by
    funext i
    obtain ⟨i,j|j⟩ := i
    · simp [bump]
    unfold bump noiseKick; simp only [Sum.elim_inr, Flat.flat_probe _ _ _ _ h]
  have hy : seed T H u x=seed T H k x := by ext i j; unfold seed; simp_rw [hz]
  let v := freeEquiv F H; let A := seed T H k x; let e := onKey v (G:=G); let B := A.submatrix id e; let L := price F H (G:=G) v
  have hh : seed T F k x=B*L := (pulls T F H k x h v hT).symm
  have he : B.transpose * B=(kinetic T H k x).submatrix e e := by
    unfold B kinetic; rw [transpose_submatrix]; exact Matrix.submatrix_mul_equiv _ _ e (Equiv.refl _) e
  have hc := unscaled F H v J hJ
  unfold kinetic
  rw [hh,hy]; dsimp only; rw [Matrix.transpose_mul,Matrix.mul_assoc L.transpose,← Matrix.mul_assoc B.transpose,he,Matrix.det_mul,Matrix.det_mul,
    Matrix.det_transpose,Matrix.det_submatrix_equiv_self]
  change L.det*(det (kinetic T H k x)*L.det)=_
  have hi : L.det^2=1 := by rw [← sq_abs,show |L.det|=1 from hc]; norm_num
  calc
    _ = L.det^2*det (kinetic T H k x) := by ring
    _ = _ := by rw [hi,one_mul]; rfl

/-- Even if not yet supplied the particular chartRatio eventually used,
this result holds from actual production of *a* chart (normalized
Jacobians drop out at this comparison). -/
lemma shared (x : ℝ) (hT : T.up.Bounds p σ E Λ) (h : S.patch.Branches S.kernel G) (u : S.Choices) :
    Matrix.det (kinetic T F k x) = Matrix.det (kinetic T H u x) := by
  exact common T F H k (Foundations.chart G) (Foundations.chart_ok G) _ hT h u
end turn
end YM.Next.SectorChange.Native
