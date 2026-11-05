import YM.Push.LOOP_COEFFICIENT.GermWard

/-!
# Finite response test on the map drift 

The test field transforms *too*. Before contraction with the bond-gradient,
this linear response annihilates longitudinal inputs and has no constant
field term. Not a bound at singular gauges, and not by itself a proof of
zero quadratic momentum jet in the period limit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Lattice Wilson RG Precision Function Filter Set Exterior
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators
variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma gauge_rate (v : Nodes G n) : HasDerivAt (fun s : ℝ => displacement (1:Config G n) (Lattice.gauge (vary 1 (s • v)) 1))
    (R_g 1 *ᵥ v) 0 := by
  let U (s : ℝ) : Config G n := Lattice.gauge (vary 1 (s • v)) 1
  have he : U 0 = 1 := by simp [U]
  have hv (x : Site n) : HasDerivAt (fun s : ℝ => G.mat (vary 1 (s • v) x)) (G.colorMat (paint G _ v x)) 0 := by
    simpa only [Pi.one_apply,G.mat_one,mul_one] using! mat_vary_rate (1:NodeField G n) v x
  have hg (i : Bonds n) : HasDerivAt (fun s => delta (1:G.El) (U s i)) (paint G _ (R_g 1 *ᵥ v) i) 0 := by
    change HasDerivAt (fun s => delta ((1:Config G n) i) _) _ _
    conv => arg 1; ext s; rw [← he]
    refine delta_rate ?_
    rw [he,R_g,LinearMap.toMatrix'_mulVec,paint_brace,Pi.one_apply,G.mat_one,mul_one,G.adjoint_one,map_sub]
    simpa only [U,Lattice.gauge,Pi.one_apply,mul_one,G.mat_mul,G.mat_inv,G.colorMat_skew,zero_smul, vary_zero,G.mat_one,star_one,one_mul,Pi.mul_apply,sub_eq_add_neg] using!
      (hv i.1).mul (hv (i.1 + step i.2)).star
  simpa only [show (fromColor G (Bonds n)) (paint G _ (R_g (1:Config G n) *ᵥ v)) = _ from
    (paint G _).symm_apply_apply _] using! (fromColor G (Bonds n)).hasFDerivAt.comp_hasDerivAt
    (l:=fromColor G (Bonds n)) (0:ℝ) (hasDerivAt_pi.mpr hg)

lemma generator_fst (v : Actors G c f) : (generator S v).1 = R_g 1 *ᵥ v.1 := by
  have he := hasFDerivAt_fst.comp_hasDerivAt (l:=Prod.fst) (0:ℝ) (side _ (switchGauge_diff (S:=S) (G:=G) |>.differentiableAt (by simp)) (v,(0:Scene G c f)))
  simp only [Function.comp_def,switchGauge, Prod.smul_fst,Prod.smul_snd,Prod.fst_zero,smul_zero,vary_zero] at he
  exact he.unique (gauge_rate _)

lemma generator_fine (v : Nodes G f) : generator S (0,v) = (0,R_tot S 1 *ᵥ v) := by
  apply Prod.ext
  · rw [generator_fst,Matrix.mulVec_zero]
  have he := hasFDerivAt_snd.comp_hasDerivAt (l:=Prod.snd) (0:ℝ) (side _ (switchGauge_diff (S:=S) (G:=G) |>.differentiableAt (by simp)) ((0,v),0))
  simp only [Function.comp_def,switchGauge, Prod.smul_fst,Prod.smul_snd,Prod.snd_zero,smul_zero,vary_zero] at he
  rw [R_tot,LinearMap.toMatrix'_mulVec]; exact he.unique (gaugeJoint_rate ..)

def response (p : Clip) (W : PathData G) (t : S.Choices) (v : Loops.Links G c) (x : Scene G c f) := Yresp p W t (vary 1 x.1) (vary 1 x.2) v

variable {W : PathData G} {σ C Λ : ℝ} {p : Clip} {t : S.Choices}

lemma Yresp_linear (p : Clip) (W : PathData G) (t : S.Choices) (V : Config G c) (U : Loops.Inputs G c f) (v : Loops.Links G c) :
    Yresp p W t V U v = ∑ i, v i • ((baseVector p W t V U)⁻¹ * bilinearAt (fun a => localize (Zmap t) U a i) 0).trace := by
  rw [Yresp, acceleration,twist,Matrix.mul_sum, trace_sum]; simp only [Matrix.mul_smul,trace_smul]

lemma response_zero (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (hG : G.Simple) (v : Loops.Links G c) :
    response p W t v 0 = 0 := by
  let L : Loops.Links G c →ₗ[ℝ] ℝ := {
    toFun := Yresp p W t 1 1
    map_add' a b := by simp_rw [Yresp_linear, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    map_smul' a b := by simp_rw [Yresp_linear]; simp [mul_assoc,Finset.mul_sum] }
  have hb := (beam_near (t:=t) h).self_of_nhds
  have hL := cohort_null hG L (fun u a => by
    have he : gaugeJoint S (constantGauge u) (constantGauge u) 1 = 1 := by simpa using! (vary_joint_color (S:=S) u (0:Loops.Dual G c f)).symm
    have hv : Lattice.gauge (constantGauge u) (1:Config G c) = 1 := by simpa using! (vary_link_color u (0:Loops.Links G c)).symm
    have ht : Cohort u a = linkAdj (constantGauge u) *ᵥ a := by apply (paint G (Bonds c)).injective; ext1 i; rw [paint_cohort,linkAdj,paint_adjoints]; rfl
    have hl := Yresp_gauge h hw t _ _ 1 hb (show Beam t (gaugeJoint S (constantGauge u) (constantGauge u) 1) by rw [he]; exact hb) a
    rw [hv, he, ← ht] at hl; exact hl)
  rw [response]; simp only [Prod.fst_zero,Prod.snd_zero,vary_zero]; exact DFunLike.congr_fun hL v

lemma response_diff (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (hN : IsUnit (vector p W t 1 1)) (v : Loops.Links G c) :
    ContDiffAt ℝ ω (response p W t v) 0 := by
  have hu := (matDiffAt_const (1:Loops.Inputs G c f) (x:= (0:Scene G c f))).vary contDiffAt_snd
  have hz := Zmap_diff h t (x:=(0:Scene G c f)) (vary_zero _) hu
  have hb := smooth_base h hw t (U:=fun x : Scene G c f => vary 1 x.2) (x:=0) (vary_zero _) hu ((matDiffAt_const 1).vary contDiffAt_fst)
  rw [vector_flat h hw t] at hN
  have hi := (inv_contDiffAt _ (isUnit_iff_isUnit_det _ |>.mp hN))
  have hu' := (hu.comp (f:= Prod.fst) (show ContDiffAt ℝ ω Prod.fst ((0:Scene G c f),(0:Loops.Dual G c f)) from contDiffAt_fst)).vary contDiffAt_snd
  have hm := Zmap_diff h t (x:= ((0:Scene G c f),(0:Loops.Dual G c f))) (U:=fun x => vary (vary 1 x.1.2) x.2) (by simp) hu'
  have he := (hz.comp (f:= Prod.fst) (show ContDiffAt ℝ ω Prod.fst ((0:Scene G c f),(0:Loops.Dual G c f)) from contDiffAt_fst)).displacement hm (by simp)
  unfold response; simp_rw [Yresp_linear]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.const_smul
  refine ((Matrix.traceLinearMap (JointKey G c f) ℝ ℝ).toContinuousLinearMap.contDiff.contDiffAt).comp (f:=fun x : Scene G c f => (baseVector p W t (vary 1 x.1) (vary 1 x.2))⁻¹ * bilinearAt (fun a => localize (Zmap t) (vary 1 x.2) a i) 0) (0:Scene G c f) ?_
  apply smooth_mul ((show ContDiffAt ℝ ω _ (baseVector p W t (vary 1 (0:Scene G c f).1) (vary 1 (0:Scene G c f).2)) by simpa only [Prod.fst_zero,Prod.snd_zero,vary_zero] using! hi).comp 0 hb)
  have hf : ContDiffAt ℝ ω (uncurry fun (x : Scene G c f) (a : Loops.Dual G c f) => localize (Zmap t) (vary 1 x.2) a i) ((0:Scene G c f),0) :=
        contDiffAt_pi.mp (show ContDiffAt ℝ ω (uncurry fun (x : Scene G c f) a => localize (Zmap t) (vary 1 x.2) a) ((0:Scene G c f),0) from he) i
  exact (bilinearAt_diff hf).comp (f:=fun x => (x,0)) 0 (contDiffAt_id.prodMk contDiffAt_const)

lemma response_ward (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (hG : G.Simple) (hN : IsUnit (vector p W t 1 1)) (v w) :
    fderiv ℝ (response p W t w) 0 (generator S v) = 0 := by
  have h1 := (gauge_diff (x:= (0:Actors G c f)) ((matDiffAt_const 1).vary contDiffAt_fst) (matDiffAt_const 1)).continuousAt.tendsto
  have h2 := (gaugeJoint_diff (x:= (0:Actors G c f)) (S:=S) (matDiffAt_const 1) ((matDiffAt_const 1).vary contDiffAt_fst) ((matDiffAt_const 1).vary contDiffAt_snd)).continuousAt.tendsto
  simp only [Prod.fst_zero,Prod.snd_zero,vary_zero,gauge_one,gaugeJoint_one] at h1 h2
  let L := ContinuousLinearMap.inl ℝ (Actors G c f) (Scene G c f)
  have he : response p W t w ∘ switchGauge S ∘ L =ᶠ[𝓝 0] 0 := by
    have hb := (beam_near (t:=t) h).self_of_nhds
    filter_upwards [h1.eventually (vary_displacement 1),h2.eventually (vary_displacement 1), h2.eventually (beam_near h t)] with x hV hU hB
    let B := linkAdj (vary 1 x.1)
    have hl := Yresp_gauge h hw t (vary 1 x.2) (vary 1 x.1) 1 hb hB (B.transpose *ᵥ w)
    change Yresp p W t _ _ (B *ᵥ (B.transpose *ᵥ w)) = Yresp p W t 1 1 _ at hl
    rw [Matrix.mulVec_mulVec, (adjoints_ortho _).rev (A:=B),Matrix.one_mulVec, show Yresp p W t 1 1 _ = _ by
      simpa only [response,Prod.fst_zero, Prod.snd_zero,vary_zero] using response_zero (t:=t) h hw hG (B.transpose *ᵥ w)] at hl
    simpa only [response, Function.comp_apply, switchGauge,L,ContinuousLinearMap.inl_apply, Prod.fst_zero,Prod.snd_zero,vary_zero, hV,hU, Pi.zero_apply] using! hl
  have hh : switchGauge (G:=G) S 0 = 0 := by simp [switchGauge]
  have hi := he.fderiv_eq (𝕜:=ℝ)
  have hs : DifferentiableAt ℝ (switchGauge S) (L 0) := L.map_zero.symm ▸ switchGauge_diff.differentiableAt (by simp)
  rw [fderiv_zero, fderiv_comp 0 (show DifferentiableAt ℝ (response p W t w) _ by simpa only [Function.comp_apply,map_zero,hh] using!
    ((response_diff h hw hN w).differentiableAt (by simp))) (hs.comp 0 L.differentiableAt),
    fderiv_comp 0 hs L.differentiableAt,L.fderiv,Function.comp_apply,map_zero,hh] at hi
  exact DFunLike.congr_fun hi v

lemma fee_ward (hw : W.Bounds p σ C Λ) {μ : ℝ} (hμ : 0 < μ) (hv : IsUnit (reference μ p W (n:=n) 1)) (hG : G.Simple)
    (a : Nodes G n) v : iteratedFDeriv ℝ 2 (fee μ p W) 0 ![R_g 1 *ᵥ a,v] = 0 := by
  let H (v : Nodes G n × Loops.Links G n) := Lattice.gauge (vary 1 v.1) (vary 1 v.2)
  have hh : H 0 = 1 := by simp [H]
  have he : MatDiffAt H 0 := gauge_diff ((matDiffAt_const 1).vary contDiffAt_fst) ((matDiffAt_const 1).vary contDiffAt_snd)
  have ht := (matDiffAt_const _).displacement he hh
  rw [show R_g 1 *ᵥ a = fderiv ℝ (fun z => displacement 1 (H z)) 0 (a,0) from ?_]
  · apply ward_calculus ht (by rw [hh,displacement_self]) (fee_diff hw hμ hv) (fee_flat hw hμ hv hG)
    · simpa only [H,vary_zero,gauge_one] using displacement_vary (1:Config G n)
    have hi := he.continuousAt.tendsto; rw [hh] at hi
    filter_upwards [hi.eventually (vary_displacement (1:Config G n))] with x hx
    rw [fee,hx]; apply scalarRef_gauge hw
  symm
  have hi := side _ (ht.differentiableAt (by simp)) (a,0)
  simp only [H,Prod.smul_fst,Prod.smul_snd,smul_zero,vary_zero] at hi
  exact hi.unique (gauge_rate a)
end YM.Push.Loops
