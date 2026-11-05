import YM.TraceExtension.Lamp.Pious
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{Y:Gal G f}
-- deriv time at zero background
lemma tide_tilt (hp: Cloaked Y)(hy:Y 1=0): tidal Y 1=Tbody Y:=by
    let F:= Y ∘ input G f
    let K:= lyr Y (1:Config G f); have hx(s:ℝ)(z:Link G f):K s z= content (input G f (s • F z)*input G f z):=by
        unfold K lyr psm tendr; simp[hy,F]
    let H(s:ℝ)(z: Link G f):= fderiv ℝ (K s) 0 z
    have hx': F 0=0:=by simp[F,hy]
    -- want lyre = z time partial along cartMove z. D(0)=id
    let A(z:Link G f):= fderiv ℝ (cartMove z) 0
    have hA: ContDiffAt ℝ ω A 0:= (Work.F05.curve_partial cartDiff).comp (f:=fun z:Link G f=> (z,0)) 0 (by fun_prop)
    have h0: cartMove (0:Link G f) =ᶠ[𝓝 0] id:=by filter_upwards[input_encodes (G:=G) (m:=f)] with x hx; simp[cartMove,hx]
    have ht : lyre Y 1=ᶠ[𝓝 0] fun z=> A z (F z):=by
        filter_upwards [(show Tendsto (fun z:Link G f=>(z,(0:Link G f))) (𝓝 0) (𝓝 0) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually ((cartDiff (G:=G) (c:=f)).eventually (by simp))] with z hz
        unfold lyre; let L:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (F z)
        rw [show (fun s:ℝ=>lyr Y 1 s z)= cartMove z ∘ L from funext fun s=>hx s z, fderiv_comp 0 (by rw [map_zero]; exact ((Work.F05.hold_jet hz).differentiableAt (by simp))) L.differentiableAt,L.fderiv,map_zero]; simp[L];rfl
    have hv: fderiv ℝ (lyre Y 1) 0=fderiv ℝ F 0:=by
        rw [ht.fderiv_eq];ext1 u; rw [f_clm u 0 (show ContDiffAt ℝ ω F 0 from hp.dye) hA,hx',map_zero,add_zero]; unfold A; rw[h0.fderiv_eq, fderiv_id];rfl
    unfold Tbody tidal;rw[hv]
lemma walk_exp (p:Cover)(b:Axis): HasDerivAt (fun t:ℝ=> mode (axes (t • (step b:Track))) p) (Complex.I*p b) 0:=by
    let W(t:ℝ):= Complex.I *(t:ℂ)*(p b:ℂ)
    have hw:HasDerivAt W (Complex.I*(p b:ℂ)) 0:=by unfold W; simpa using! (((Complex.ofRealCLM.hasDerivAt (x:=0)).const_mul Complex.I).mul_const (p b:ℂ))
    rw[show (fun t:ℝ=> mode (axes (t • (step b:Track))) p)=fun t=> Complex.exp (W t) from ?_]; exact (by simpa [W] using hw.cexp)
    funext t; simp [axes,mode,W, mul_ite,apply_ite Complex.ofReal,mul_assoc,ite_mul]
-- identify quadratic+affine tester with plane coefficient. B cost not needed
lemma ktest (i j:Loc G 1)(b:Axis)(hv:Cloaked Y)(he:Y 1=0):
   let s:Tit G:=(.watch,i); let t:Tit G:=(.foot b,j)
   fderiv ℝ (tast Y i j) 0 ((step b:Track),(0:Track))=Complex.I* (↑(iteratedFDeriv ℝ 2 (bottom Y) 0 (![ballad s (0:Site f),ballad t 0] :Fin 2→_)):ℂ):=by
    intro s t
    let A:=Tane Y; let B(z:ℝ):=barca (0:Site f) (z • (step b:Track)) j; let C:=barca (0:Site f) (0:Track) i; let L:= tast Y i j
    have hV: DifferentiableAt ℝ (tast Y i j) (0:Track×Track):=by
       let V:=Tane Y
       have hx:∀ z:Track×Track,tast Y i j z= ∑ u,∑ v, V u v * barca (0:Site f) z.1 j v * barca (0:Site f) z.2 i u:=by
           intro x; simp[tast,dotProduct,Matrix.mulVec,Finset.sum_mul]; rfl
       rw [funext hx]; refine DifferentiableAt.fun_sum fun x _=> DifferentiableAt.fun_sum fun y _=> ?_
       have hm (i: Loc G 1)(x:Lines G f 1): ContDiffAt ℝ ω (fun z:Track=> barca (0:Site f) z i x) 0:=
           (((Firm.mode (lift (x.1-(0:Site f))) zero_lt_one).analytic_real 0).contDiffAt.mul contDiffAt_const)
       apply DifferentiableAt.mul
       · exact (DifferentiableAt.mul (differentiableAt_const _) (ContDiffAt.differentiableAt (𝕜:=ℝ) (n:=ω) ( (hm j y).comp (f:=(Prod.fst:Track × Track→ Track)) 0 contDiffAt_fst) (by simp)))
       exact ContDiffAt.differentiableAt (𝕜:=ℝ) (n:=ω) ( (hm i x).comp (f:=(Prod.snd:Track × Track→ Track)) 0 contDiffAt_snd) (by simp)
    obtain ⟨_,_,_,hf⟩:= rain_read (Y:=Y) (show Y∈rains G f from ⟨hv,he⟩)
    obtain ⟨hr,hg⟩:= ballad_water (f:=f) s 0 rfl; obtain ⟨he,hj⟩:=ballad_mix (f:=f) t 0 (by unfold t; simp)
    rw[hf,hg,hj, dotProduct_zero,zero_add,he,hr]
    let a:= strollT t (0:Site f);let k:=strollT s (0:Site f)
    have ht:C=axes k:=by ext1 u;unfold C k barca strollT s; by_cases he: u.2=i<;> simp [axes,he,mode,RowGrade.price]
    have hx: HasDerivAt B (Complex.I • axes a) 0:=by
        apply hasDerivAt_pi.mpr; intro i; have hv:=(walk_exp (lift (i.1-(0:Site f))) b).mul_const ((Pi.single (M:=fun _=>ℂ) j (1:ℂ)) i.2); unfold B;apply hv.congr_deriv
        by_cases h:i.2=j<;>simp[h,a,t,strollT,RowGrade.price,axes]
    let T:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) ((step b:Track),(0:Track)); let M:Phase (Lines G f 1) →ₗ[ℂ] ℂ:=
      let V:= Matrix.mulVecLin A; {
       toFun:=fun x=> dotProduct (V x) C
       map_add':=fun x y=>by rw [map_add,add_dotProduct]
       map_smul':=fun t x=>by rw [map_smul,smul_dotProduct];rfl }
    have hh:L ∘ T=M ∘ B:=funext fun x=>by
       change dotProduct _ (barca (0:Site f) ((x:ℝ) • (0:Track)) i)=_; rw [smul_zero];rfl
    let N:Phase (Lines G f 1)→L[ℝ]ℂ:= (M.toContinuousLinearMap).restrictScalars ℝ
    have hp': HasDerivAt (L ∘ T) (fderiv ℝ (tast Y i j) 0 ((step b:Track),0)) 0:=by apply HasFDerivAt.comp_hasDerivAt (f:=T) _ (map_zero T|>.symm ▸ hV.hasFDerivAt) (show HasDerivAt T _ _ from ray_id _)
    rw[hh] at hp';
    apply hp'.unique; have ha' := (N.hasFDerivAt.comp_hasDerivAt 0 hx)
    change HasDerivAt (M ∘ B) (M (Complex.I • axes a)) 0 at ha'; rw[M.map_smul] at ha';
    have hv: M (axes a)= ((dotProduct (Tbody Y*ᵥ a) k:ℝ):ℂ):=by change dotProduct (approached (Tbody Y)*ᵥ axes a) C= _; rw [ht,prom_vec,p_dot]
    rw[hv, Tbody, bill_pay] at ha';exact ha'
private lemma dot_peaked (A:G.Color)(i a:Axis)(j:G.ColorIndex) : inner ℝ A (peakD ((.watch,mood G i j):Tit G) a)=if a=i then A j else 0:=by
    rw[PiLp.inner_apply]; unfold peakD mood; simp[coord_iff,ite_mul]; split_ifs <;> simp_all
lemma mix_cost (b d a i:Axis)(j k:G.ColorIndex):
    missY b ((.watch,mood G a k):Tit G) (.foot d,mood G i j)=
    (if b=d ∧ a=i ∧ j=k then 1 else 0)-(if a=d ∧ b=i ∧ j=k then 1 else 0):=by
    let s:Tit G:=(.watch,mood G a k); let t:Tit G:=(.foot d,mood G i j)
    have hp(x:Axis): peakD t x=0:=by ext c; simp [peakD,t]
    unfold missY; change (∑ i,inner ℝ (mixB s _ b i) (peakD t i))+(∑ i,inner ℝ (mixB t _ b i) (peakD s i))=_; simp_rw [hp];simp only [inner_zero_right,Finset.sum_const_zero,zero_add]; unfold s; simp_rw[dot_peaked]; rw [sum_eq_single a,if_pos rfl]; swap; · intro i _ hi;rw[if_neg hi];
    swap; · simp
    unfold mixB t spill; simp only [PiLp.add_apply,PiLp.sub_apply]; simp[mood,RowGrade.price,coord_iff];
    congr 1 <;> split_ifs <;> simp_all

variable {W:Type*} {g:W→Side}{L:Filter W}{K:WickL G}{X:∀ w, Gal G (g w)}{ε:W→ℝ}
lemma analytic_p [L.NeBot] (b d a i:Axis)(j k:G.ColorIndex)(he:∀ w,X w ∈ rains G _)(h:Fleam L X K) (hp:∀ w, Testify (0:Site (g w)) (bottom (X w)) (missY b) 5 (ε w))(hL:Tendsto ε L (𝓝 0)):
    K (mood G a j) (mood G i k) (step d,0)= Complex.I*((if b=d∧a=i∧k=j then 1 else 0)-(if a=d∧b=i∧k=j then 1 else 0)):=by
    let x:Loc G 1:=mood G a j; let y:Loc G 1:= mood G i k
    let u:Tit G:=(.watch,x); let t:Tit G:=(.foot d,y)
    let F(w):ℝ:= iteratedFDeriv ℝ 2 (bottom (X w)) 0 (![ballad u 0,ballad t 0]:Fin 2→_)
    have hu:Tendsto F L (𝓝 (missY b u t)):=by
       apply Rose.alight (F:=F) (H:=fun _=>missY b u t) _ tendsto_const_nhds
       exact squeeze_zero_norm' (Eventually.of_forall (fun w=> (hp w).bill u t (by exact (show 3+2 ≤ 5 by norm_num)))) hL
    have hv := tendsto_nhds_unique (h.rise x y (step d,0)) (show Tendsto _ L (𝓝 (Complex.I*(missY b u t:ℝ))) from by
       refine Tendsto.congr' (f₁:=fun i=> Complex.I*(F i:ℂ)) ?_ (((Complex.ofRealCLM.continuous.tendsto _).comp hu).const_mul _)
       exact Eventually.of_forall fun w=>by obtain ⟨h,h'⟩:=he w; exact (ktest _ _ _ h h').symm)
    unfold u t x y at hv; rw [mix_cost] at hv
    rw [hv]; congr 1; push_cast;split_ifs<;>simp
lemma analytic_full [L.NeBot] (b i j:Axis)(a c:G.ColorIndex)(p q:Cover)(he:∀ w,X w∈ rains G _)(h:Fleam L X K) (hp:∀ w,Testify (0:Site (g w)) (bottom (X w)) (missY b) 5 (ε w))(hL:Tendsto ε L (𝓝 0))(hx:Kelly K):
    K (mood G i a) (mood G j c) (reel p,reel q)=Complex.I*((if i=j∧a=c then (p b:ℂ) else 0) - (if b=j∧a=c then (p i:ℂ) else 0)):=by
    let X(d:Axis):= K (mood G i a) (mood G j c) (step d,0)
    rw [hx.rear]
    have hh(S:Finset Axis): K (mood G i a) (mood G j c) (∑ k∈S,(reel p k) •step k,0)=∑ d∈S,(p d:ℂ)*X d:=by
       induction S using Finset.induction with
       | empty=> rw[sum_empty,sum_empty]; have ht:= hx.scale (mood G i a) (mood G j c) 0 0; simpa using ht
       | insert i' l hi ih=> rw [sum_insert hi,sum_insert hi,hx.plus,hx.scale,ih]; congr 2
    rw [show reel p=(∑ i,(reel p i) • step i) from by ext1 d; rw[Finset.sum_apply];simp [mul_ite],hh]
    have hu(d):= analytic_p b d i j a c he h hp hL; unfold X;simp_rw[hu]
    rw[show ∑ x:Axis,_= Complex.I * ((∑ d:Axis,(p d:ℂ)*(if b=d∧i=j∧c=a then 1 else 0))-(∑ d:Axis,(p d:ℂ)*(if i=d∧b=j∧c=a then 1 else 0))) from ?_]; swap; · rw[← sum_sub_distrib,mul_sum];exact sum_congr rfl (fun k _=>by ring)
    by_cases hv:a=c
    · subst c; by_cases hh:i=j<;>by_cases he:b=j<;>simp only[*,and_true,and_false,ite_true,ite_false,eq_self] <;> simp_all [mul_ite]
    simp [hv,Ne.symm hv]
end YM.Trace.Lamp
