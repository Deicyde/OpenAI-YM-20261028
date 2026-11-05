import YM.RG08.Canon.Rotation
/-!
# Pull centered Hessian transport back to true Counting basis
for path Lie slice. Post costs arbitrary at this step. Exact determinant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {F : Forest S.ratio} {p : Clip} {R : PathData G} {η : ℝ} {ρ : fieldDir G c 1 → AxisChart G F}
local notation "Γ" => fieldDir G c 1
local notation "U" => AxisChart G F
local notation "K" => Precision.Key F G
local notation "T" => Matrix (K) (K) ℝ

-- direction map, actual Hessian basis.
def axisKeys (G : Gauge) {c f : Side} {k : Ratio c f} (F : Forest k) : AxisChart G F≃L[ℝ](Precision.Key F G →ℝ) := LinearEquiv.toContinuousLinearEquiv {
  toFun x i:= x i.1 i.2
  invFun a i:= WithLp.toLp 2 (fun z=> a (i,z))
  left_inv _:= rfl, right_inv _:= rfl, map_add' _ _:= rfl, map_smul' _ _:=rfl }
lemma axis_single (i : Precision.Key F G) : (axisKeys G F) (Precision.frame F i)= Pi.single i 1 := by
  funext j
  change (Precision.frame F i j.1) j.2=_
  by_cases h:i.1=j.1
  · rw [← h,frame,Pi.single_eq_same,Pi.single_apply]; split
    next he=> subst j; simp
    next he=> simp [EuclideanSpace.basisFun_apply,(show j.2≠i.2 from fun v=> he (Prod.ext h.symm v))]
  rw [frame,Pi.single_eq_of_ne (Ne.symm h),Pi.single_eq_of_ne (show j≠i from fun v=>h (congr_arg Prod.fst v.symm))]; rfl
variable (t : S.Choices)
lemma reflect_grit (h : Critical F p R ρ) :
    ContDiffAt ℝ ω (fun u:Γ=> Precision.hessian F t p R u (ρ u)) 0 ∧ ∀ᶠ u in 𝓝 0, (Precision.hessian F t p R u (ρ u)).IsSymm := by
  let H:= tested F t p R; let P u : (T):= Precision.hessian F t p R u (ρ u)
  have ht : ContDiffAt ℝ ω (uncurry H) (0,ρ 0) := by rw [h.1]; exact (h.2.2 t).1
  have hv : ContDiffAt ℝ ω (fun u:Γ=> (u,ρ u)) 0:= contDiffAt_id.prodMk h.2.1
  have hu : ContDiffAt ℝ ω (fun u:Γ => fderiv ℝ (fderiv ℝ (H u)) (ρ u)) 0 :=
    (show ContDiffAt ℝ ω (fun z:(Γ)×(U)=>fderiv ℝ (fderiv ℝ (H z.1)) z.2) (0,ρ 0) from by rw [h.1]; exact Work.F05.curve_partial (F:=fun x=> fderiv ℝ (H x)) (Work.F05.curve_partial ((h.2.2 t).1))).comp (f:=fun u=> (u,ρ u)) 0 hv
  refine ⟨?_,?_⟩
  · let N (B : (U)→L[ℝ](U)→L[ℝ]ℝ):T:= Matrix.of fun i j=> B (frame F i) (frame F j)
    let A : (((U)→L[ℝ] (U)→L[ℝ]ℝ)) →ₗ[ℝ] (T) := {
    toFun:=N, map_add' _ _:=rfl, map_smul' _ _:=rfl }
    rw [show (fun u:Γ=>Precision.hessian F t p R u (ρ u))= (fun u:Γ=>N (fderiv ℝ (fderiv ℝ (H u)) (ρ u))) by ext; simp [Precision.hessian,N,H,iteratedFDeriv_two_apply]]
    exact (A.toContinuousLinearMap.contDiff.contDiffAt.comp (f:=fun u=> fderiv ℝ (fderiv ℝ (H u)) (ρ u)) 0 hu)
  filter_upwards [hv.continuousAt.eventually (ht.eventually (by simp))] with x hx
  ext i j
  have hH : ContDiffAt ℝ ω (H x) (ρ x) := hx.comp (f:=fun y=> (x,y)) _ (contDiffAt_const.prodMk contDiffAt_id)
  simp only [Precision.hessian,of_apply,transpose_apply,iteratedFDeriv_two_apply]
  exact ((hH.isSymmSndFDerivAt (by simp)) _ _)

def fromKeys (G : Gauge) {c f : Side} {k : Ratio c f} (F : Forest k) (A : Matrix (Precision.Key F G) (Precision.Key F G) ℝ) : AxisChart G F →L[ℝ] AxisChart G F:=
   (axisKeys G F).symm.toContinuousLinearMap ∘L A.mulVecLin.toContinuousLinearMap ∘L (axisKeys G F).toContinuousLinearMap
omit t in
lemma keys_det (A : T) : LinearMap.det (fromKeys G F A).toLinearMap=Matrix.det A := by
  rw [show (fromKeys G F A).toLinearMap=(axisKeys G F).symm.toLinearEquiv.conj A.mulVecLin from rfl]; exact (LinearMap.det_conj A.mulVecLin (axisKeys G F).symm.toLinearEquiv).trans (LinearMap.det_toLin' A)
omit t in
lemma keys_fit (P : (Γ)→(T)) (h : ContDiffAt ℝ ω P 0) : ContDiffAt ℝ ω (fun u=>fromKeys G F (P u)) 0 := by
  let A : (T) →ₗ[ℝ] ((U) →L[ℝ] (U)) := {
    toFun:=fromKeys G F
    map_add' x y := by
       ext v
       simp [fromKeys]
    map_smul' a x:= by
       ext v
       simp [fromKeys] }
  exact A.toContinuousLinearMap.contDiff.contDiffAt.comp _ h

omit t in
lemma hessian_keys {B : (U) → ℝ} (u x y : U) : iteratedFDeriv ℝ 2 B u ![x,y] =
      axisKeys G F x ⬝ᵥ (Matrix.of (fun i j=> iteratedFDeriv ℝ 2 B u ![frame F i,frame F j])*ᵥ (axisKeys G F y)) := by
  let H:= fderiv ℝ (fderiv ℝ B) u
  let C:= axisKeys G F
  have hm (x:U) : (∑ j,C x j • frame F j)=x := by
    apply (axisKeys G F).injective
    rw [map_sum]; simp_rw [map_smul,axis_single]; funext i; rw [Finset.sum_apply]; simp [Pi.single_apply,mul_ite,C]
  simp_rw [iteratedFDeriv_two_apply]
  simp only [Fin.isValue,Matrix.cons_val_zero, Matrix.cons_val_one]
  conv_lhs=> rw [← hm x,map_sum, _root_.sum_apply,← hm y]
    -- explicitly normalize sum before tensor becomes equation
  change (∑ i:K,(H (C x i • frame F i)) (∑ j,C y j • frame F j))=_
  simp only [C,dotProduct,Matrix.mulVec,map_smul,map_sum,_root_.smul_apply,
    smul_eq_mul,Finset.mul_sum,Matrix.of_apply]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; dsimp only [H]
  rw [_root_.mul_comm ((axisKeys G F) y j), _root_.mul_assoc]

section simple
omit t in
lemma quick_comp {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E] (b y : E) (φ : E→ℝ) (A : E≃L[ℝ]E) :
    jet (fun x:E=> φ (b+A x)) 2 y = jet (fun x:E=> φ (b+x)) 2 (A y) := by
  let f (x:E):= φ (b+x)
  have g := A.iteratedFDerivWithin_comp_right f (s:=Set.univ) uniqueDiffOn_univ (x:=0) (Set.mem_univ (A 0)) 2
  simp only [Set.preimage_univ,map_zero,iteratedFDerivWithin_univ] at g
  change (jet (f ∘ A) 2 y) = jet f 2 (A y)
  unfold jet; rw [g]; rfl
end simple
lemma jet_shiftKeys (h : Critical F p R ρ) (X : T) (L : U ≃L[ℝ] (U)) (i : Γ) (y : U)
    (he : L.toContinuousLinearMap=fromKeys G F X) (hX:Xᵀ*Precision.hessian F t p R i (ρ i)*X = Precision.hessian F t p R 0 (ρ 0)) :
    jet (fun x:U=> tested F t p R i (ρ i+L x)) 2 y=jet (tested F t p R 0) 2 y := by
  rw [quick_comp]
  unfold jet; -- matrix
  have hm (u:U) : (fun _:Fin 2=>u)=![u,u] := funext fun z=> by fin_cases z <;> simp
  have ha : axisKeys G F (L y)=X*ᵥ(axisKeys G F y) := by
    change axisKeys G F (L.toContinuousLinearMap y)=_
    rw [he]; exact (axisKeys G F).apply_symm_apply _
  rw [hm,hm y, iteratedFDeriv_comp_add_left,add_zero,hessian_keys (S:=S)]
  let z:= axisKeys G F y
  have hT : iteratedFDeriv ℝ 2 (tested F t p R 0) 0 ![y,y]=z ⬝ᵥ (Precision.hessian F t p R 0 (ρ 0) *ᵥ z) := by
    rw [h.1]
    exact hessian_keys (S:=S) ..
  rw [ha,hT, ← hX]; apply congr_arg ((↑(Nat.factorial 2):ℝ)⁻¹ * ·)
  let H:= Precision.hessian F t p R i (ρ i)
  change (X*ᵥz) ⬝ᵥ (H*ᵥ (X*ᵥz))=z ⬝ᵥ ((Xᵀ*H*X) *ᵥ z)
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, mulVec_mulVec, vecMul_transpose, mulVec_mulVec]
set_option maxHeartbeats 500000 in
lemma revolves (h : Critical F p R ρ) (hw : PriceGap F p R η) (he : 0<η) :
    ∃ L : (Γ) → (U)≃L[ℝ](U),L 0=ContinuousLinearEquiv.refl ℝ (U) ∧
      ContDiffAt ℝ ω (fun i:Γ=> (L i).toContinuousLinearMap) 0 ∧ ContDiffAt ℝ ω (fun i:Γ=> (L i).symm.toContinuousLinearMap) 0 ∧
      (∀ᶠ i in 𝓝 0, let v := LinearMap.det (L i).toContinuousLinearMap.toLinearMap
                   0<v ∧ v^2 * (Precision.hessian F t p R i (ρ i)).det = (Precision.hessian F t p R 0 (ρ 0)).det ∧
                    ∀ y, jet (fun x:U=> tested F t p R i (ρ i + L i x)) 2 y = jet (tested F t p R 0) 2 y) := by
  let H u : T:= Precision.hessian F t p R u (ρ u)
  have hp : 0<(H 0).det := (Work.F05.hessian_pos he hw h t).self_of_nhds
  obtain ⟨h₁,h₂⟩:= reflect_grit t h
  obtain ⟨X,hX,hC,hL⟩:= planets (H:=H) h₁ hp.ne' h₂
  have hf := hL.mono fun _ ho=> ho.1.ne'
  let L (i:Γ): (U)≃L[ℝ](U):= if h: (X i).det ≠0 then ((fromKeys G F (X i)).toLinearMap.equivOfDetNeZero (by rw [keys_det]; exact h)).toContinuousLinearEquiv else ContinuousLinearEquiv.refl ℝ (U)
  have hK : (fun i=>(L i).toContinuousLinearMap)=ᶠ[𝓝 0](fun i=> fromKeys G F (X i)) := hf.mono (fun i H=> by dsimp only; unfold L; rw [dif_pos H]; rfl)
  have hl : L 0=ContinuousLinearEquiv.refl ℝ (U) := by
    apply DFunLike.ext; intro b; change (L 0).toContinuousLinearMap b=_; rw [show (L 0).toContinuousLinearMap=_ from hK.eq_of_nhds,hX]; 
    change (axisKeys G F).symm ((1:T) *ᵥ (axisKeys G F b))=b
    rw [Matrix.one_mulVec]; exact (axisKeys G F).symm_apply_apply _
  have hc := (keys_fit _ hC).congr_of_eventuallyEq hK
  refine ⟨L,hl,hc,?_,?_⟩
  · -- inverse
    simp_rw [← ContinuousLinearMap.inverse_equiv]; refine ContDiffAt.comp (g:=ContinuousLinearMap.inverse) _ ?_ hc
    -- equivalence at flat
    exact contDiffAt_map_inverse _
  filter_upwards [hK,hL] with i hi ⟨ht,hQ⟩
  change (L i).toContinuousLinearMap=fromKeys G F (X i) at hi
  have hv : LinearMap.det (L i).toContinuousLinearMap.toLinearMap=(X i).det := by rw [hi,keys_det]
  refine ⟨hv.symm ▸ ht,?_,fun y=>?_⟩
  · have hd:=congr_arg Matrix.det hQ; simp only [Matrix.det_mul,Matrix.det_transpose] at hd; rw [hv,← show _=(Precision.hessian F t p R 0 (ρ 0)).det from hd]; unfold H; ring
  exact jet_shiftKeys t h _ _ i y hi hQ
end YM.RG08.Canon
