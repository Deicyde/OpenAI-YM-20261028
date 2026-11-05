import YM.Push.LOOP_COEFFICIENT.Admission
import YM.Work.B04

/-!
# Bond-gradient correction tests

At the *prepared* stationary backgrounds. The linear leading bond
gradient is the negative output kinetic precision on all external slots,
not a multiple with an additional half. The base-inverse map response
already kills gradients in every actual finite period satisfying admission.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Lattice RG Wilson Matrix Function Filter Precision Exterior Tree Set
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {c f n : Side} {S : StepData c f}
variable {F : Forest S.ratio} {p : Clip} {W : PathData G} {ρ : fieldDir G c 1 → AxisChart G F} {P : ChartRatio G}
    {A : Matrix (Body 1 f) (Body 1 c) ℝ}

def Zprep (G : Gauge) (t : S.Choices) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (b : Loops.Links G c) :=
    Zmap t (vary 1 (graft G S A b).2)

def JZ (G : Gauge) (t : S.Choices) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (b : Loops.Links G c) : Loops.Links G c :=
    first (penalty S (vary 1 b)) (Zprep G t A b)

lemma positions_graph (x : Scene G c f) : positions (vary 1 x.2) = vary 1 (projectFine G c f *ᵥ x.2) := by rw [projectFine,LinearMap.toMatrix'_mulVec]; rfl

lemma project_graph (v : Loops.Links G c) (φ : Matrix (Body 0 c) (Body 1 c) ℝ) : projectFine G c f *ᵥ (graph G A φ v).2 = liftMatrix G A *ᵥ v := by
  rw [projectFine,LinearMap.toMatrix'_mulVec]; rfl

lemma layer_coord (x : Loops.Links G n) (j : G.ColorIndex) (i : Site n) (a) : layer G n j x (i,coord a) = x ((i,a),j) := by
  change x ((i,axisEquiv.symm (coord a)),j) = _; rw [← coord_map,axisEquiv.symm_apply_apply]

lemma layer_matrix (x : Loops.Links G c) (j : G.ColorIndex) : layer G f j (liftMatrix G A *ᵥ x) = A *ᵥ layer G c j x := by
  ext i; obtain ⟨z,hz⟩ := axisEquiv.surjective i.2; rcases i with ⟨i,k⟩; dsimp only at hz; subst k
  rw [coord_map,layer_coord,liftMatrix_apply]

lemma Zprep_one (t : S.Choices) (h : S.patch.Branches S.kernel G) : Zprep G t A 0 = 1 := by simp only [Zprep,map_zero,Prod.snd_zero,vary_zero,Zmap_one h]

lemma Zprep_diff (t : S.Choices) (h : S.patch.Branches S.kernel G) : MatDiffAt (Zprep G t A) 0 :=
  Zmap_diff h t (U:=fun b => vary 1 (graft G S A b).2) (by simp) ((matDiffAt_const 1).vary (graft G S A).contDiff.contDiffAt.snd)



lemma Zprep_rate (t : S.Choices) (v : Loops.Links G c) (h : S.patch.Branches S.kernel G)
    (K : Matrix (Body 1 c) (Body 1 c) ℝ) (ha : mean S * A = 1 - S.kernel.penalty⁻¹ • K) (e : Bonds c) :
    HasDerivAt (fun s : ℝ => G.mat (Zprep G t A (s • v) e))
      (G.colorMat (paint G _ (v - S.kernel.penalty⁻¹ • (liftMatrix G K *ᵥ v)) e)) 0 := by
  simp_rw [Zprep,graft, Zmap,Lattice.gauge,G.mat_mul,G.mat_inv,map_smul,Prod.smul_snd]
  let z := graph G A (fixRoot S * A) v
  let b := liftMatrix G A *ᵥ v
  have hU i : HasDerivAt (fun s : ℝ => G.mat (auxiliaries (vary 1 (s • z.2)) i))
      (G.colorMat (paint G _ z.2 (.inr i))) 0 := by simpa only [Pi.one_apply, G.mat_one,mul_one] using! mat_vary_rate 1 z.2 (.inr i)
  have hV (s : ℝ) : positions (vary 1 (s • z.2)) = represent (s • chartEquiv G f b) := by
    rw [show positions (vary 1 (s • z.2)) = _ from positions_graph (s • z), Prod.smul_snd, Matrix.mulVec_smul,show projectFine G c f *ᵥ z.2 = b from project_graph ..,
       ← map_smul,represent_chart]
  have he := ((hU e.1).mul (prices S h e t (chartEquiv G f b))).mul (hU (e.1+step e.2)).star
  simp only [Pi.mul_apply,zero_smul,link_one,vary_zero,auxiliaries,Function.comp_apply,Pi.one_apply,G.mat_one,settled S h e t,star_one,mul_one,one_mul,G.colorMat_skew] at he
  change HasDerivAt (fun s : ℝ => G.mat (auxiliaries (vary 1 (s • z.2)) _) * G.mat (S.prediction (positions (vary 1 (s • z.2))) t e) * star (G.mat _)) _ _
  simp_rw [hV]
  convert! he using 1
  rw [← G.colorMat.map_add,← sub_eq_add_neg,← G.colorMat.map_sub]
  congr 1
  apply PiLp.ext; intro j
  simp only [PiLp.sub_apply, PiLp.add_apply,paint_apply,z,graph_right, Pi.sub_apply,Pi.smul_apply, smul_eq_mul]
  rw [← layer_eq,show layer G f j b = _ from layer_matrix v j,probe,Matrix.add_mulVec,Pi.add_apply, ← Matrix.mulVec_mulVec _ (d 0 c),d_sites,
    Matrix.mulVec_mulVec,ha, Matrix.sub_mulVec, Matrix.one_mulVec,Matrix.smul_mulVec,Pi.sub_apply,Pi.smul_apply, layer_coord,
    liftMatrix_apply, Matrix.mulVec_mulVec _ (fixRoot S) A]; ring

private def collected (G : Gauge) (t : S.Choices) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (x : Loops.Links G c × Loops.Links G c) :=
    penalty S (vary 1 x.1) (vary (Zprep G t A x.1) x.2)

private def direction (G : Gauge) (c : Side) (κ : ℝ) (K : Matrix (Body 1 c) (Body 1 c) ℝ) : Loops.Links G c × Loops.Links G c →ₗ[ℝ] Loops.Links G c :=
    (κ⁻¹ • ((liftMatrix G K).mulVecLin.comp (LinearMap.fst ..))) - LinearMap.snd ..

private lemma collected_smooth (t : S.Choices) (h : S.patch.Branches S.kernel G) : ContDiffAt ℝ ω (collected G t A) 0 := by
  have hz := Zprep_diff (A:=A) t h
  exact penalty_diff S (x:=((0,0) : Loops.Links G c × Loops.Links G c)) ((matDiffAt_const 1).vary contDiffAt_fst) ((hz.comp (v:=Zprep G t A) (f:=Prod.fst) (x:=(0,0)) contDiffAt_fst).vary contDiffAt_snd)

private lemma collected_limit (t : S.Choices) (v : Loops.Links G c × Loops.Links G c) (h : S.patch.Branches S.kernel G)
    (K : Matrix (Body 1 c) (Body 1 c) ℝ) (ha : mean S * A = 1 - S.kernel.penalty⁻¹ • K) :
    let x := direction G c S.kernel.penalty K v
    Tendsto (fun t₁ : ℝ => collected G t A (t₁ • v)/t₁^2) (𝓝[≠] 0) (𝓝 (S.kernel.penalty*(x ⬝ᵥ x)/2)) := by
  intro x
  simp_rw [collected,penalty, Prod.smul_fst,Prod.smul_snd,mul_div_assoc,paint_dot, Finset.sum_div,real_inner_self_eq_norm_sq]
  refine Tendsto.const_mul S.kernel.penalty (tendsto_finsetSum _ (fun i _ => Work.F03.price_limit (V:=fun s : ℝ => vary 1 (s • v.1) i * (vary (Zprep G t A (s • v.1)) (s • v.2) i)⁻¹) ?_ ?_))
  · rw [zero_smul,zero_smul,Zprep_one t h,vary_zero,mul_inv_cancel]
  simp only [G.mat_mul,G.mat_inv]
  have he : HasDerivAt (fun s : ℝ => G.mat (vary (Zprep G t A (s • v.1)) (s • v.2) i))
      (G.colorMat (paint G _ v.2 i + paint G _ (v.1 - S.kernel.penalty⁻¹ • (liftMatrix G K *ᵥ v.1)) i)) 0 := by
    simp only [vary,bump, G.mat_mul,map_add]
    conv => arg 1; ext s; rw [← vary_one]
    simpa only [zero_smul, vary_zero, Zprep_one t h,Pi.one_apply,G.mat_one,one_mul,mul_one] using!
      (mat_vary_rate 1 v.2 i).mul (Zprep_rate t v.1 h K ha i)
  convert! (mat_vary_rate 1 v.1 i).mul he.star using 1
  rw [zero_smul, zero_smul, Zprep_one t h, vary_zero,G.colorMat_skew,Pi.one_apply,G.mat_one,star_one,mul_one, one_mul]
  have hx : paint G _ x i = paint G _ v.1 i - (paint G _ v.2 i + paint G _ (v.1 - S.kernel.penalty⁻¹ • (liftMatrix G K *ᵥ v.1)) i) := by
    simp only [x,direction,LinearMap.sub_apply,LinearMap.smul_apply, LinearMap.comp_apply,LinearMap.fst_apply,LinearMap.snd_apply, Matrix.mulVecLin_apply,map_sub,Pi.sub_apply]
    abel
  rw [hx,map_sub,mul_one]; rfl

private lemma collected_jets (t : S.Choices) (h : S.patch.Branches S.kernel G)
    (K : Matrix (Body 1 c) (Body 1 c) ℝ) (ha : mean S * A = 1 - S.kernel.penalty⁻¹ • K) :
    let κ := S.kernel.penalty; let D := direction G c κ K
    fderiv ℝ (collected G t A) 0 = 0 ∧ ∀ x y, iteratedFDeriv ℝ 2 (collected G t A) 0 ![x,y] = κ*(D x ⬝ᵥ D y) := by
  intro κ D
  exact (Work.F03.hessian_of_limit (Q:=fun x y => κ*(D x ⬝ᵥ D y)) ((collected_smooth t h).of_le le_top) (fun _ => collected_limit t _ h K ha)
    (fun _ _ _ => by rw [map_add, add_dotProduct,mul_add]) (fun _ _ => by rw [dotProduct_comm])).2

lemma JZ_diff (t : S.Choices) (h : S.patch.Branches S.kernel G) : ContDiffAt ℝ ω (JZ G t A) 0 :=
  (grad_diff (f:=fun x a => penalty S (vary 1 x) (vary (Zprep G t A x) a)) (x:=0) (y:=0) (collected_smooth t h)).comp
    (f:=fun x => (x,0)) 0 (contDiffAt_id.prodMk contDiffAt_const)

lemma JZ_leading (t : S.Choices) (h : S.patch.Branches S.kernel G)
    (K : Matrix (Body 1 c) (Body 1 c) ℝ) (ha : mean S * A = 1 - S.kernel.penalty⁻¹ • K) :
    JZ G t A 0 = 0 ∧ linearAt (JZ G t A) 0 = -liftMatrix G K := by
  let F := collected G t A
  let X := Loops.Links G c
  let L := ContinuousLinearMap.inl ℝ X X
  have hs := collected_smooth (A:=A) t h
  obtain ⟨he,hQ⟩ := collected_jets t h K ha
  have hv i : (fun x => JZ G t A x i) =ᶠ[𝓝 0] fun x => Work.F04.vert F (L x) (Pi.single i 1) := by
    have ht := L.continuous.tendsto 0; rw [map_zero] at ht
    filter_upwards [ht.eventually (hs.eventually (by simp))] with y hy
    change ContDiffAt ℝ ω F (y,0) at hy
    exact DFunLike.congr_fun (Work.F04.hasFDerivAt_slice F y 0 (hy.differentiableAt (by simp))).fderiv _
  refine ⟨funext (fun i => ((hv i).self_of_nhds).trans ?_),Matrix.ext_iff_mulVec.mpr fun a => ?_⟩
  · simp only [map_zero,Work.F04.vert,F,he,ContinuousLinearMap.zero_comp,_root_.zero_apply,Pi.zero_apply]
  rw [linearAt_mulVec,Matrix.neg_mulVec]; funext i
  rw [show fderiv ℝ (JZ G t A) 0 a i = fderiv ℝ (fun x => JZ G t A x i) 0 a by rw [fderiv_apply ((JZ_diff t h).differentiableAt (by simp))]; rfl, (hv i).fderiv_eq]
  have hd := (Work.F04.vert_smooth F _ hs).differentiableAt (by simp)
  have hh := ((hd.hasFDerivAt (x:=0)).clm_apply (hasFDerivAt_const (𝕜:=ℝ) (Pi.single i 1) (0:X × X)))
  have hh' := (show HasFDerivAt (fun x => Work.F04.vert F x (Pi.single i 1)) _ (L 0) by simpa only [map_zero] using hh).comp 0 L.hasFDerivAt
  have hw := Work.F04.vert_rate F 0 hs (a,0) (Pi.single i 1)
  rw [show fderiv ℝ (fun x => Work.F04.vert F (L x) (Pi.single i 1)) 0 = _ from hh'.fderiv]
  simp only [ContinuousLinearMap.comp_zero,zero_add, ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply]
  change fderiv ℝ (Work.F04.vert F) 0 (a,(0:Loops.Links G c)) _ = _
  rw [hw, show F=collected G t A from rfl,hQ]
  simp only [direction,
    LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.fst_apply,LinearMap.snd_apply,map_zero,smul_zero,zero_sub,sub_zero,Matrix.mulVecLin_apply,dotProduct_neg,dotProduct_single,mul_one,Pi.smul_apply,smul_eq_mul,Pi.neg_apply]
  rw [mul_neg,← mul_assoc, mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_mul]

lemma response_prepared (h : Admission F ρ p W A P) (t : S.Choices) (v w) :
    fderiv ℝ (response p W t w ∘ graft G S A) 0 (R_g 1 *ᵥ v) = 0 := by
  obtain ⟨σ,C,Λ,hw⟩ := h.paths
  obtain ⟨q,hq⟩ := h.modulo_gauge t (h.graft_station t (R_g 1 *ᵥ v)) (generator_station h.branches hw h.simple (v,0)) (generator_fst (S:=S) (v,0)).symm
  have he := (response_diff h.branches hw (h.invert_vector t) w).differentiableAt (by simp)
  rw [fderiv_comp 0 (show DifferentiableAt ℝ _ ((graft G S A) 0) by rw [map_zero]; exact he) (graft G S A).differentiableAt,
      map_zero,(graft G S A).fderiv,ContinuousLinearMap.comp_apply,hq,map_add]
  simp only [response_ward h.branches hw h.simple (h.invert_vector t),add_zero]
end YM.Push.Loops
