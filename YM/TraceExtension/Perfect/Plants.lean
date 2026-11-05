import YM.TraceExtension.Perfect.Badge
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {V E J:Type} [NormedAddCommGroup V][NormedAddCommGroup E][NormedAddCommGroup J][NormedSpace ℝ V][NormedSpace ℝ E][NormedSpace ℝ J]
lemma criss (P:V→L[ℝ] E→L[ℝ] ℝ)(A:J→ V)(B:J→ E)(hA:ContDiffAt ℝ ω A 0)(hB:ContDiffAt ℝ ω B 0)(ha:A 0=0)(hb:B 0=0):
    let F:=fun x=>P (A x) (B x); let D:=fderiv ℝ A 0; let K:=fderiv ℝ B 0; F 0=0 ∧ fderiv ℝ F 0=0∧∀ x y,iteratedFDeriv ℝ 2 F 0 ![x,y]=P (D x) (K y)+P (D y) (K x):=by
 intro F D K
 have ht:= Work.F03.hessian_of_limit (Q:=fun x y=>P (D x) (K y)+P (D y) (K x)) (show ContDiffAt ℝ 2 F 0 from ((P.contDiff.contDiffAt.comp _ hA).clm_apply hB).of_le le_top)
 refine ht (fun x=> ?_) (fun x y z=> by simp only[map_add, _root_.add_apply]; abel) (fun x y=> add_comm ..)
 have h(v:J): HasDerivAt (fun s:ℝ=>s • v) v 0:=by simpa using (hasDerivAt_id (0:ℝ)).smul_const v
 let H:=fun s:ℝ=> s • x
 have hx : H 0=0:=zero_smul ..
 have hu : Tendsto (fun s:ℝ=> s⁻¹ • A (s • x)) (𝓝[≠] 0) (𝓝 (D x)):=by
    have he:=hasDerivAt_iff_tendsto_slope_zero.mp ((hx.symm ▸ (show HasFDerivAt A D 0 from (hA.differentiableAt (by simp)).hasFDerivAt) : HasFDerivAt A D (H 0)).comp_hasDerivAt 0 (show HasDerivAt H x 0 from h _))
    simpa only [Function.comp_apply,zero_add,hx,ha,sub_zero] using he
 have hy : Tendsto (fun s:ℝ=> s⁻¹ • B (s • x)) (𝓝[≠] 0) (𝓝 (K x)):=by
    have he:=hasDerivAt_iff_tendsto_slope_zero.mp ((hx.symm ▸ (show HasFDerivAt B K 0 from (hB.differentiableAt (by simp)).hasFDerivAt) : HasFDerivAt B K (H 0)).comp_hasDerivAt 0 (show HasDerivAt H x 0 from h _))
    simpa only [Function.comp_apply,zero_add,hx,hb,sub_zero] using he
 rw [show (P (D x) (K x)+P (D x) (K x))/2=P (D x) (K x) by ring]
 have hh:= (show Continuous (fun p: V× E=>P p.1 p.2) from (P.continuous.comp continuous_fst).clm_apply continuous_snd).continuousAt.tendsto.comp (hu.prodMk_nhds hy)
 refine hh.congr' ?_
 filter_upwards with s; change P (s⁻¹ • A (s • x)) (s⁻¹ • B (s • x)) = _; unfold F;simp only [map_smul,_root_.smul_apply,smul_eq_mul]; ring

variable {f:Side}{G:Gauge}
def tulip (o:Site f)(a b:Axis)(U : Config G f): G.Color:= G.curvature (travel U o (square a b))
def petal (o:Site f)(a b:Axis)(A:Link G f): G.Color:= edgeColor A (o,a)+edgeColor A (o+step a,b)-edgeColor A (o+step b,a)-edgeColor A (o,b)
lemma petal_swap (o:Site f)(a b:Axis)(A:Link G f): petal o a b A= -petal o b a A:=by unfold petal; abel
lemma tulip_gauge (o:Site f)(a b:Axis)(U:Config G f)(k:Site f→G.El): tulip o a b (Lattice.gauge k U)=G.adjoint (k o) (tulip o a b U):=by unfold tulip; rw[travel_gauge]; simp [G.curvature_conjugate]
lemma tulip_zero (o:Site f)(a b:Axis): tulip o a b (1:Config G f)=0:=by
 have hx:= Push.stroll_zero (G:=G) (square a b) o; rw [link_one] at hx; unfold tulip;rw [hx,G.curvature_unit]
private lemma tram_l (o:Site f)(w:Walk) : ContDiffAt ℝ ω (fun x:Link G f=> G.mat (travel (input G f x) o w)) 0:=by
 induction w generalizing o with
 | nil=> simp only[travel]; exact contDiffAt_const
 | cons a w ih=> simp only[travel,G.mat_mul]; apply ContDiffAt.mul _ (ih _); have he:Army (input G f) 0:=Army.powL contDiffAt_id; unfold Step.read; split; simp only [G.mat_inv]; exact (starL ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ (he _); exact he _
lemma tulip_cont (o:Site f)(a b:Axis): ContDiffAt ℝ ω (tulip (G:=G) o a b ∘ input G f) 0:=by
 unfold Function.comp; simp only[tulip,Gauge.curvature,G.mat_inv]; have H:=tram_l (G:=G) o (square a b); exact G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp _ (H.sub ((starL ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ H)|>.const_smul _)
lemma petal_plan (o:Site f)(a b:Axis)(x:Link G f): fderiv ℝ (tulip o a b∘input G f) 0 x=petal o a b x:=by
 let A:= arm G f 1 x
 have hk:= Work.F03.curvature_of_hasDerivAt (V:=fun t:ℝ=>travel (represent (t • A)) o (square a b)) (Push.travell (square a b) o A)
 have ht (t:ℝ) : t • A = arm G f 1 (t • x):=map_smul (arm G f 1) _ _|>.symm
 have hy:= Push.side (tulip (G:=G) o a b∘input G f) ((tulip_cont o a b).differentiableAt (by simp)) x
 simp_rw [ht] at hk; rw [hy.unique hk]; unfold petal; let u:=collect G A
 have he:o+step a+step b-step a=o+step b:=by abel
 have h:o+step a+step b+-step a=o+step b:=by abel
 simp only[square,linkSum,Step.vec,Step.used, negDir, posDir,Bool.false_eq_true,↓reduceIte,add_zero,h,he,add_sub_cancel_right]; change _ = _
 change edgeColor x _ + (edgeColor x _+(_+_))=_
 abel

def bornPair (o:Site f)(a b i:Axis): Peat G f:=fun U=> inner ℝ (tulip o a i U) (tulip o b i U)
lemma born_win (o:Site f)(a b i:Axis):bornPair (G:=G) o a b i∈loom G f ∧ ∀ u v:Link G f, iteratedFDeriv ℝ 2 (bornPair o a b i ∘ input G f) 0 ![u,v]= inner ℝ (petal o a i u) (petal o b i v)+inner ℝ (petal o a i v) (petal o b i u):=by
 let X:=bornPair (G:=G) o a b i
 let F:=tulip (G:=G) o a i ∘ input G f; let K:=tulip (G:=G) o b i∘input G f
 have ha:ContDiffAt ℝ ω F 0:=tulip_cont ..; have hb:ContDiffAt ℝ ω K 0:=tulip_cont ..
 obtain ⟨hv,hp,H⟩:= criss (innerSL ℝ (E:=G.Color)) F K ha hb (by simp[F,input_zero,tulip_zero]) (by simp[K,input_zero,tulip_zero])
 change fderiv ℝ (X ∘ input G f) 0=0 at hp
 refine ⟨⟨⟨((innerSL ℝ (E:=G.Color)).contDiff.contDiffAt.comp _ ha).clm_apply hb,fun T _ _ _ _ V k w _ _ _ _=> Filter.Eventually.of_forall fun t=>?_⟩,fun j hj=>?_⟩,fun u v=>?_⟩
 · unfold X at *
   change inner ℝ (tulip o a i (Lattice.gauge (k t) (V t))) _=inner ℝ _ _
   rw [tulip_gauge,tulip_gauge]; exact LinearIsometry.inner_map_map (⟨G.adjoint (k t o), G.norm_adjoint (k t o)⟩: G.Color →ₗᵢ[ℝ] G.Color) _ _
 · change iteratedFDeriv ℝ j (X∘input G f) 0=_; interval_cases j <;> ext1 m
   · simp only[iteratedFDeriv_zero_apply]; exact hv
   simp [iteratedFDeriv_one_apply,hp]
 have hh:= H u v; change iteratedFDeriv ℝ 2 (bornPair o a b i ∘ input G f) 0 ![u,v]=inner ℝ (fderiv ℝ F 0 u) (fderiv ℝ K 0 v)+inner ℝ (fderiv ℝ F 0 v) (fderiv ℝ K 0 u) at hh
 simpa only [F,K,petal_plan] using hh
end YM.Trace.Perfect
