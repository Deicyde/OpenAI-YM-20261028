import YM.TraceExtension.Pills.Dock
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Xo
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}
private abbrev V:=Link G n
private abbrev spin(U:Config G n): Link G n→L[ℝ] Link G n:=edgeColor.symm.toContinuousLinearMap ∘L ((ContinuousLinearMap.pi (fun i=> (G.adjoint (U i)).toContinuousLinearMap ∘L ContinuousLinearMap.proj i )) ∘L edgeColor.toContinuousLinearMap)
private lemma spin_at(U:Config G n)(x:V)(i): edgeColor (spin U x) i= G.adjoint (U i) (edgeColor x i):=by unfold spin;simp
private lemma spin_l(U:Config G n)(x:V) : U * input G n x*U⁻¹=input G n (spin U x):=by funext i; rw[input_color,spin_at,adjoint_exp,Pi.mul_apply,Pi.mul_apply, Pi.inv_apply,input_color]
private lemma spin_pay(U:Config G n)(x y:V): dotProduct (spin U x) (spin U y)= x ⬝ᵥ y:=by
   rw [dotEdge,dotEdge]; apply sum_congr rfl fun i _=>?_; rw [spin_at,spin_at]; exact (show G.Color→ₗᵢ[ℝ] G.Color from ⟨G.adjoint _,G.norm_adjoint _⟩).inner_map_map _ _
private lemma twine(X:V (G:=G) (n:=n)) : ContDiffAt ℝ ω (fun t:ℝ=> spin (input G n (t • X))) 0:=by
   let U(t:ℝ):= input G n (t • X); let F:=fun y:ℝ=>spin (U y)
   obtain ⟨C,hC,H⟩:= shaders G 0
   let M:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Lines G n 1=>ℝ))
   have hp:∀ x:V (G:=G) (n:=n),ContDiffAt ℝ ω (fun y=> F y x) 0:=by
      intro x; apply ContDiffAt.congr_of_eventuallyEq (f:=fun y=> edgeColor.symm (edgeColor (F y x)))
      · refine ContDiffAt.comp (g:=edgeColor.symm) (f:=fun y=> edgeColor (F y x)) 0 (edgeColor.symm.contDiff.contDiffAt) (contDiffAt_pi.mpr fun i=>?_)
        have hv: ContDiffAt ℝ ω (fun y=>G.mat (U y i)) 0:=Army.powL (v:=fun t:ℝ=> t • X) (by fun_prop) i
        unfold F; simp_rw[spin_at]; have he: ContDiffAt ℝ ω (fun y=> (G.adjoint (U y i)).toContinuousLinearMap) 0:=by simp_rw [turned]; exact ((H _).analytic.comp (f:=fun y=> G.mat (U y i)) _ hv)
        exact he.clm_apply contDiffAt_const
      filter_upwards with y; simp
   -- pi clm coordinate; use Finite smooth
   let L(e:Lines G n 1): ℝ→ V (G:=G) (n:=n):=fun y=> F y (bolt e)
   have h(y:ℝ):F y=∑ e:Lines G n 1,(ContinuousLinearMap.smulRight (M e) (L e y)):=by
       ext1 u; rw [_root_.sum_apply]; nth_rw 1 [show u=∑ i:Lines G n 1,u i • bolt i from ?_]; swap; · ext1 i; simp [bolt,Pi.single_apply,Finset.sum_apply]
       rw[map_sum]; exact sum_congr rfl (fun i _=> (F y).map_smul (u i) (bolt i))
   change ContDiffAt ℝ ω F 0; rw[funext h]; exact ContDiffAt.sum (fun i _=> ContDiffAt.smulRight contDiffAt_const (hp (bolt i)))
private lemma tonic(Y:Gal G n)(U:Config G n):
    let p:=Y U; let C (z:V):=Y (input _ _ z*U)-p; let L(t:ℝ):= spin (input G n (t • p))
    lyre Y U=ᶠ[𝓝 0] (fun z=> fderiv ℝ L 0 1 z + fderiv ℝ (cartMove z) 0 (C z)):=by
    intro p C L
    let Z(z:V (G:=G) (n:=n))(v:V (G:=G) (n:=n)×V (G:=G) (n:=n)):=content (input _ _ v.1*input _ _ z*(input G n v.2)⁻¹)
    have hx: ContDiffAt ℝ ω (uncurry Z) 0:= Army.logL (V:=fun p:V (G:=G) (n:=n)×(V (G:=G) (n:=n)×V (G:=G) (n:=n))=>input G n p.2.1*input G n p.1*(input G n p.2.2)⁻¹) (( (Army.powL (v:=fun p:Link G n×(Link G n×Link G n)=> p.2.1) (by fun_prop)).mul (Army.powL contDiffAt_fst)).mul (Army.powL (v:=fun q:Link G n×(Link G n×Link G n)=>q.2.2) (by fun_prop)|>.inv)) (by change input G n 0*input G n 0*(input G n 0)⁻¹=1; simp)
    have ht: ∀ᶠ v:ℝ × Link G n in 𝓝 0, Z v.2 (v.1 • (p,p)) = L v.1 v.2:=by
        let F(v:ℝ × Link G n):= L v.1 v.2
        have hL: ContDiffAt ℝ ω F 0:= ((show ContDiffAt ℝ ω L 0 from twine p).comp (f:=Prod.fst) 0 contDiffAt_fst).clm_apply contDiffAt_snd
        have hf:F 0=0:=map_zero _
        filter_upwards [(show Tendsto F (𝓝 0) (𝓝 0) from hf ▸ hL.continuousAt.tendsto).eventually input_encodes] with z hz; unfold Z; simp only [Prod.smul_fst,Prod.smul_snd]; rw [spin_l]; exact hz
    -- cond
    filter_upwards [(show Tendsto (fun z:Link G n=> (z,((0:Link G n),(0:Link G n)))) (𝓝 0) (𝓝 0) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually (hx.eventually (by simp)), el_slice ht] with z hz ht
    let F:=Z z; have hZ:ContDiffAt ℝ ω F 0:= Work.F05.hold_jet hz
    have hy(w: Link G n×Link G n) (t:ℝ):= Push.side F (hZ.differentiableAt (by simp)) w
    have he : (fun t=> lyr Y U t z)=(fun t:ℝ=> F (t • (Y (input _ _ z*U),p))):=by
       funext t; unfold F Z lyr psm tendr; apply congr_arg; simp only [Prod.smul_fst, Prod.smul_snd]; unfold p; group
    have hh: fderiv ℝ F 0 (p,p)= fderiv ℝ L 0 1 z:=by
        let H:=Push.side F (hZ.differentiableAt (by simp)) (p,p); let M:=ContinuousLinearMap.apply ℝ (Link G n) z; have ha': HasDerivAt L (fderiv ℝ L 0 1) 0:= (twine p|>.differentiableAt (by simp)).hasDerivAt
        exact (H.congr_of_eventuallyEq ((show (fun t:ℝ=> F (t • (p,p)))=ᶠ[𝓝 0] M ∘ L from ht).symm)).unique (M.hasFDerivAt.comp_hasDerivAt 0 ha')
    let B:=ContinuousLinearMap.inl ℝ (Link G n) (Link G n)
    have hp:F ∘ B=cartMove z:=by funext x;change content (input G n x*input G n z*(input G n 0)⁻¹)=_; simp only [input_zero,inv_one,mul_one]; rfl
    have hw: fderiv ℝ F 0 (C z,0)= fderiv ℝ (cartMove z) 0 (C z):=by rw [← hp, fderiv_comp 0 ( (map_zero B).symm ▸ (hZ.differentiableAt (by simp))) B.differentiableAt,B.fderiv,map_zero]; rfl
    unfold lyre; rw[he, show fderiv ℝ (fun t:ℝ=>F (t • (Y (input G n z*U),p))) 0 1= fderiv ℝ F 0 _ from (Push.side F (hZ.differentiableAt (by simp)) (Y (input G n z*U),p)).deriv, ← hh, ← hw,←map_add]; apply congr_arg; unfold C; ext1 <;> simp
private lemma mun(x: Link G n)(i:Lines G n 1) :
   let L(t:ℝ):= spin (input G n (t • x)); (fderiv ℝ L 0 1 (bolt i)) i=0:=by
    intro L; let b:Link G n:=bolt i
    let F(t:ℝ)(j:Lines G n 1):ℝ:= L t b j;let a:= fderiv ℝ L 0 1 b; let r(t:ℝ):=∑ j, F t j * F t j
    have he(t):r t=b ⬝ᵥ b:=spin_pay ..
    have hp(j):HasDerivAt (fun t=>F t j) (a j) 0:=by
        let Z: (Link G n→L[ℝ]Link G n) →L[ℝ] ℝ:= (ContinuousLinearMap.proj j) ∘L (ContinuousLinearMap.apply ℝ (Link G n) b)
        exact Z.hasFDerivAt.comp_hasDerivAt 0 (show HasDerivAt L (fderiv ℝ L 0 1) 0 from (twine x|>.differentiableAt (by simp)).hasDerivAt)
    have hh:HasDerivAt r _ 0:= HasDerivAt.fun_sum (fun j _=> (hp j).mul (hp j))
    have hv: L 0 b=b:=by
        unfold L; rw [zero_smul,input_zero]; apply edgeColor.injective; funext t; rw [spin_at]; simp
    have hz: (∑ j:Lines G n 1,((a j)* F 0 j+F 0 j*a j))=0:= by rw [funext he] at hh; exact hh.unique (hasDerivAt_const ..)
    have hf(t): F 0 t=bolt i t:= congr_fun hv t
    simp[ hf, bolt,Pi.single_apply,ite_mul,mul_ite] at hz; simp [sum_add_distrib] at hz; change a i=0; linarith
lemma tether (Y:Gal G n)(U:Config G n)(h:ContDiffAt ℝ ω (fun y=> Y (input G n y*U)) 0): lush Y U= ∑ i:Lines G n 1,outD (fun X=> Y X i) i U:=by
    unfold lush Matrix.trace; apply sum_congr rfl fun i _=> ?_; let Q:=tidal Y U; let H(z:Link G n):=Y (input _ _ z*U); let p:=Y U
    let L(t:ℝ):= spin (input G n (t • p)); let T (z:Link G n):= fderiv ℝ (cartMove z) 0; have hT:ContDiffAt ℝ ω T 0:= (Work.F05.curve_partial cartDiff).comp (f:=fun z:Link G n=> (z,0)) 0 (by fun_prop)
    have hs:= tonic Y U; let Z:= fderiv ℝ L 0 1; let V(z:Link G n):= H z - p; let A(z):=T z (V z)
    have hv:ContDiffAt ℝ ω V 0:=h.sub contDiffAt_const
    have hV:V 0=0:=by simp [V,H,p]
    have hZ: T 0=ContinuousLinearMap.id ℝ _:=by
        have ht: cartMove (0:Link G n) =ᶠ[𝓝 0] id:=by filter_upwards[input_encodes (G:=G) (m:=n)] with z hz; simp [cartMove,hz]
        exact ht.fderiv_eq.trans (fderiv_id)
    let b:Link G n:=bolt i
    have hx: fderiv ℝ A 0 b=fderiv ℝ H 0 b:=by
        unfold A; rw [f_clm b 0 hv hT,hV,map_zero,add_zero,hZ]; change fderiv ℝ V 0 b=_; unfold V; rw [fderiv_fun_sub (f:=H) (h.differentiableAt (by simp)) (differentiableAt_const _),fderiv_fun_const,Pi.zero_apply,sub_zero];
    have hh: fderiv ℝ (lyre Y U) 0 b=Z b+fderiv ℝ H 0 b:=by
        rw [show fderiv ℝ (lyre Y U) 0=fderiv ℝ (⇑Z+A) 0 from (show lyre Y U=ᶠ[𝓝 0] ⇑Z+A from hs).fderiv_eq,fderiv_add Z.differentiableAt ((hT.clm_apply hv).differentiableAt (by simp)),Z.fderiv, ContinuousLinearMap.add_apply,hx]
    change tidal Y U i i=_; rw [tidal,bill_def,cash_pocket, ← bockat]; let P:Link G n→L[ℝ] ℝ:= ContinuousLinearMap.proj i
    have hp: P ∘ H = (fun z=>Y (input _ _ z*U) i):=rfl
    rw [show bolt i=b from rfl,hh,Pi.add_apply, show Z b i=0 from mun p i,zero_add]; unfold outD; change _=fderiv ℝ (P ∘ H) 0 b; rw [fderiv_comp _ P.differentiableAt (h.differentiableAt (by simp)),P.fderiv]; rfl
end YM.Trace.Xo
