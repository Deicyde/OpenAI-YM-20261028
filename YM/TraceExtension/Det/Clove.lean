import YM.TraceExtension.Det.Port

/-! # Local gauge equivariance RIGHT determinant root. Carry full inhomogeneous transform. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{f:Side}{p:Clip}{R:PathData G}{Y:Gal G f}{α C D μ:ℝ}
    {T:Type}[NormedAddCommGroup T][NormedSpace ℝ T][FiniteDimensional ℝ T][CompleteSpace T]
    (U:Config G f)(k:Coats G f)
lemma shell_mat (μ:ℝ)(P:Funds (Lines G f 1))(Q:Funds (Lines G f 0))(W: Config G f)(ht:Military P)(hv:Military Q)(hk:mail W*Q=P*mail U)(hx:flare p R W*P=P*flare p R U): stock p R μ W*P=P*stock p R μ U ∧ ammo μ W*Q=Q*ammo μ U:=by
    have he:= hv.transpose_cross ht hk
    constructor
    · rw[stock,stock,Matrix.add_mul,Matrix.add_mul,Matrix.mul_add,Matrix.mul_add P,hx,smul_mul_assoc, Matrix.mul_smul,one_mul,mul_one]; congr 2; rw [Matrix.mul_assoc,he,← Matrix.mul_assoc (mail W),hk, Matrix.mul_assoc P]
    rw[ammo,tonic,ammo,tonic,Matrix.add_mul,Matrix.mul_add,smul_mul_assoc, Matrix.mul_smul,one_mul,mul_one]; congr 1; rw [Matrix.mul_assoc,hk,← Matrix.mul_assoc (mail W)ᵀ,he, Matrix.mul_assoc Q]
lemma shell_carry (μ:ℝ)(h:R.Bounds p α C D): let W:=Lattice.gauge k U; stock p R μ W*trench k=trench k*stock p R μ U ∧ ammo μ W*troop k=troop k*ammo μ U:= shell_mat U μ (trench k) (troop k) (Lattice.gauge k U) (trench_orthogonal _) (troop_orthogonal _) (mail_carry k U) ((trench_orthogonal _).pulls (flare_carry _ h _ (burn_cov _ h)))
lemma marke_cov (μ:ℝ)(h:R.Bounds p α C D): marke p R μ (Lattice.gauge k U)=marke p R μ U:=by
    unfold marke; rw [(trench_orthogonal _).turn_det ((trench_orthogonal _).back (shell_carry U k μ h|>.1)),(troop_orthogonal _).turn_det ((troop_orthogonal _).back (shell_carry U k μ h|>.2))]

section charge
variable {ι κ γ:Type}[Fintype ι][Fintype κ][Fintype γ][DecidableEq ι][DecidableEq κ][DecidableEq γ]
set_option linter.unusedSectionVars false in
lemma trap_guard {P:Funds ι}{Q:Funds κ}{F X: Corn ι →L[ℝ] Corn κ→L[ℝ] Corn γ}(C D:Matrix κ ι ℝ)(L:Corn γ →L[ℝ] Corn γ)
    (ht:Military P)(hv:Military Q)(hp:C*P=Q*D)(hf:∀ x y,F (P *ᵥ x) (Q *ᵥ y)= L (X x y)):
    trapw C (fun i j=> F ((pocket _) i) ((pocket _) j))=L (trapw D (fun i j=> X ((pocket _) i) ((pocket _) j))):=by
    ext1 g
    let O: Corn γ→ₗ[ℝ] ℝ:= LinearMap.proj g
    let Z:= L.toLinearMap
    let A:= of fun i j=> O (F ((pocket _) i) ((pocket _) j))
    let B:= of fun i j=> O (Z (X ((pocket _) i) ((pocket _) j)))
    have hN : Pᵀ*A*Q=B:=by
       apply testers
       intro x y
       have hh (F:Corn ι →L[ℝ] Corn κ→L[ℝ] Corn γ)(O:Corn γ→ₗ[ℝ]ℝ)(x:Corn ι)(y:Corn κ):
          dotProduct x (of (fun i j => O (F ((pocket _) i) ((pocket _) j))) *ᵥ y)=O (F x y):=by
          let U:= F.toLinearMap₁₂.compr₂ O
          have hU: of (fun i j => O (F ((pocket _) i) ((pocket _) j)))=LinearMap.toMatrix₂ (pocket _) (pocket _) U:=by ext; rw[LinearMap.toMatrix₂_apply]; rfl
          rw [hU]; conv_lhs=> rw [← cash_pocket x,← cash_pocket y]
          let W:= cash (pocket ι); let Z:=cash (pocket κ);
          have hh : dotProduct (W x) ((LinearMap.toMatrix₂ (pocket ι) (pocket κ) U) *ᵥ Z y)= U (W.symm (W x)) (Z.symm (Z y)):= dotProduct_toMatrix₂_mulVec _ _ U (W x) (Z y); rw[LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply] at hh; exact hh
       rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,transposes, show dotProduct x (B*ᵥ y)=_ from hh X (O ∘ₗ Z) x y]; rw [show dotProduct _ (A *ᵥ (Q *ᵥ y))=_ from hh F O _ _,hf]; rfl
    change O (trapw C _)= (O ∘ₗ Z) (trapw D _)
    rw [trap_pay,trap_pay]; change (C*A).trace=(D*B).trace
    have he:D*Pᵀ=Qᵀ*C:=by
       rw [show D=Qᵀ*C*P from by rw [Matrix.mul_assoc,hp,← Matrix.mul_assoc,hv.right,Matrix.one_mul], Matrix.mul_assoc (Qᵀ*C),ht.left,Matrix.mul_one]
    rw [← hN,← Matrix.mul_assoc D _ Q, ← Matrix.mul_assoc D,he,Matrix.trace_mul_comm _ Q, Matrix.mul_assoc (Qᵀ) C A, ← Matrix.mul_assoc,hv.left,Matrix.one_mul]
end charge

private lemma arm_content : ∀ᶠ V:Config G f in 𝓝 1, content (fun e : Edge (Site f)=> k e.1 *V e*(k e.1)⁻¹)= armor k (content V):=by
    have hG : ∀ᶠ V: Config G f in 𝓝 1, ∀ i:Edge (Site f), plogC G (k i.1*V i*(k i.1)⁻¹)=G.adjoint (k i.1) (plogC G (V i)):=
       eventually_all.mpr fun i=> (show Tendsto (fun V:Config G f=> V i) (𝓝 1) (𝓝 1) from (continuous_apply i).tendsto (1: Config G f)).eventually (plog_conj _)
    filter_upwards [hG] with V hv
    apply edgeColor.injective; ext1 i
    have hh(z:Config G f): edgeColor (content z) i=plogC G (z i):=content_at z i.1 i.2
    rw [armor_at,hh,hh]; exact hv i
lemma lull_trip (u:BaseSites G f):
    (fun z=> juke (Lattice.gauge k U) (armorG k u) (armor k z))=ᶠ[𝓝 0] fun z=> armor k (juke U u z):=by
    let L:=armor k; let P:=armorG k; let V:= Lattice.gauge k U
    have ht(p)(z): lyric V (P p) (L z)= fun i : Edge (Site f)=> k i.1 * lyric U p z i*(k i.1)⁻¹:=by
       funext i; unfold lyric; rw[show input _ _ (L _)*_= _ from armor_go k z U]
       simp only [Lattice.gauge,V,Pi.mul_apply,Pi.inv_apply,switch_color,P,armorG_at,adjoint_exp]; group
    have hm: Tendsto (uncurry (lyric U)) (𝓝 0) (𝓝 1):=(show lyric U 0 0=1 by rw [lyric_axis,input_zero]) ▸ (lullArmy U).cont.tendsto
    have hv: ∀ᶠ z:BaseSites G f × Link G f in 𝓝 0, lull V (P z.1) (L z.2)= L (lull U z.1 z.2):=by
       filter_upwards [hm.eventually (arm_content k)] with z hz; rw[lull,ht]; exact hz
    have he: ∀ᶠ z : Link G f in 𝓝 0, ContDiffAt ℝ ω (fun u=> lull V u (L z)) 0 ∧ ContDiffAt ℝ ω (fun u=>lull U u z) 0:=by
        have he(z:Config G f)(l:Link G f→L[ℝ]Link G f): ∀ᶠ x : Link G f in 𝓝 0, ContDiffAt ℝ ω (fun u=> lull z u (l x)) 0:=by
           have hx:Tendsto l (𝓝 0) (𝓝 0):=by simpa using l.continuous.tendsto 0
           filter_upwards [(show Tendsto (fun x=> ((0:BaseSites G f),l x)) (𝓝 0) (𝓝 0) from tendsto_const_nhds.prodMk_nhds hx).eventually ((lull_analytic z).eventually (by simp))] with x hx; exact hx.comp (f:=fun u=>(u,l x)) 0 (by fun_prop)
        exact (he V L).and (he U (ContinuousLinearMap.id ℝ _))
    filter_upwards [he,el_slice hv] with x hx h
    let A(u):=lull U u x; let W(u):= lull V u (L x)
    have hp: W ∘ P=ᶠ[𝓝 0] L ∘ A:=h; have hh:=hp.fderiv_eq (𝕜:=ℝ)
    rw [fderiv_comp (g:=W) 0 (by rw[map_zero]; exact hx.1.differentiableAt (by simp)) P.differentiableAt, fderiv_comp (g:=L) 0 L.differentiableAt (hx.2.differentiableAt (by simp)), P.fderiv,L.fderiv,map_zero] at hh
    exact congr($(hh) u)
lemma lull_turn (z:Link G f)(u:BaseSites G f): jukebox (Lattice.gauge k U) (armor k z) (armorG k u)=armor k (jukebox U z u):=by
    let V:=Lattice.gauge k U
    let L:=armor k; let B:=juke V (armorG k u); let A:=juke U u
    have hp: B ∘ L=ᶠ[𝓝 0] L ∘ A:= lull_trip U k u
    have hh:=hp.fderiv_eq (𝕜:=ℝ); have ht: ContDiffAt ℝ ω B 0:= keep_l (lull_analytic V) _; have hx: ContDiffAt ℝ ω A 0:= keep_l (lull_analytic U) _
    rw[fderiv_comp 0 (by rw [map_zero]; exact ht.differentiableAt (by simp)) L.differentiableAt,map_zero, L.fderiv,fderiv_comp 0 L.differentiableAt (hx.differentiableAt (by simp)),L.fderiv] at hh
    exact congr($(hh) z)
lemma shell_guard (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ U).det≠0): let W:=Lattice.gauge k U; shellB p R μ W*trench k=trench k*shellB p R μ U ∧ shellG μ W*troop k= troop k*shellG μ U:=by
    intro W
    obtain ⟨hp,hq⟩:=shell_carry U k μ h; exact ⟨Military.inverse_cross (((trench_orthogonal k).turn_det ((trench_orthogonal k).back hp)).symm ▸ he.isUnit) he.isUnit hp,Military.inverse_cross (ammo_safe W hμ).det_pos.ne'.isUnit (ammo_safe U hμ).det_pos.ne'.isUnit hq⟩
def accord (Y:Gal G f) (k:Coats G f)(U:Config G f): Prop:=
    ∀ᶠ z:Link G f in 𝓝 0,Y (Lattice.gauge k (input G f z*U))=armor k (Y (input G f z*U))
lemma tidal_w (h:Tune Y U)(he:accord Y k U):
    (fun z=> lyre Y (Lattice.gauge k U) (armor k z))=ᶠ[𝓝 0] fun z=> armor k (lyre Y U z):=by
    let V:=Lattice.gauge k U; let L:=armor k
    have hp : ∀ᶠ z:ℝ× Link G f in 𝓝 0, psm Y V z.1 (armor k z.2)=fun i:Edge (Site f)=> k i.1*psm Y U z.1 z.2 i*(k i.1)⁻¹:=by
       have hz: Y V=L (Y U):=by have hp:=(show (fun z=>Y (Lattice.gauge k (input G f z*U)))=ᶠ[𝓝 0] (fun z=>L (Y (input G f z*U))) from he).eq_of_nhds; simpa using hp
       filter_upwards [(show Tendsto (Prod.snd:ℝ × Link G f→Link G f) (𝓝 0) (𝓝 0) from continuous_snd.tendsto _).eventually he] with z hz'
       unfold psm tendr
       rw [← show Lattice.gauge k U=V from rfl, armor_go k z.2, hz', ← map_smul, armor_go]; rw [show Y (Lattice.gauge k U)=_ from hz, show z.1 • L (Y U)=armor k (z.1 • Y U) from (L.map_smul ..).symm,armor_go]; funext i
       simp only [Lattice.gauge,Pi.mul_apply,Pi.inv_apply]; group
    let G':= lyr Y U
    have hi : ∀ᶠ z:ℝ× Link G f in 𝓝 0, lyr Y V z.1 (armor k z.2)=L (G' z.1 z.2):=by
       have hx := (show Army (uncurry (psm Y U)) 0 from h).cont.tendsto
       have hz: uncurry (psm Y U) 0=1:= ps_z U _; rw [hz] at hx
       filter_upwards[hp,hx.eventually (arm_content k)] with z hz hf; rw[lyr,hz]; exact hf
    filter_upwards[el_slice hi,(show Tendsto (fun z:Link G f=> ((0:ℝ),z)) (𝓝 0) (𝓝 0) from tendsto_const_nhds.prodMk_nhds tendsto_id).eventually ((tune_diff U h).eventually (by simp))] with z hz hv
    let K(s):= G' s z
    have ht:ContDiffAt ℝ ω K 0:= hv.comp (f:=fun s:ℝ=> (s,z)) 0 (by fun_prop)
    unfold lyre; rw [(show (fun s=> lyr Y (Lattice.gauge k U) s (armor k z))=ᶠ[𝓝 0] L ∘ K from hz).fderiv_eq,fderiv_comp 0 L.differentiableAt (ht.differentiableAt (by simp)),L.fderiv]; rfl
structure SwapCh (Y:Gal G f)(k:Coats G f)(U:Config G f)(p:Clip)(R:PathData G)(μ:ℝ): Prop where
    armV: tidal Y (Lattice.gauge k U)*trench k= trench k *tidal Y U
    reef : shoreX p R μ Y (Lattice.gauge k U)=armor k (shoreX p R μ Y U)
    reed : shoreZ p R μ Y (Lattice.gauge k U)= armor k (shoreZ p R μ Y U)
lemma swapping (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ U).det≠0)(h₁:Tune Y U)(h₂:Tune Y (Lattice.gauge k U))(hy:accord Y k U): SwapCh Y k U p R μ:=by
    let V:=Lattice.gauge k U; let L:=armor k; let J:=armorG k; let A:=trench k; let B:=troop k
    have hh: lyre Y V ∘ L=ᶠ[𝓝 0] L ∘ lyre Y U:= tidal_w U k h₁ hy
    have hv: ContDiffAt ℝ ω (lyre Y V) 0:= keep_l (tune_diff _ h₂) _
    have hu: ContDiffAt ℝ ω (lyre Y U) 0:= keep_l (tune_diff _ h₁) _
    have ha(z): A*ᵥ z=L z:= bill_pay ..; have hb(z): B*ᵥ z=J z:= bill_pay ..
    have hp: tidal Y V*A=A*tidal Y U:=by
        apply testers; intro x y
        have hf:=hh.fderiv_eq (𝕜:=ℝ)
        rw[fderiv_comp 0 (by rw[map_zero];exact hv.differentiableAt (by simp)) L.differentiableAt,L.fderiv,map_zero,fderiv_comp 0 L.differentiableAt (hu.differentiableAt (by simp)), L.fderiv] at hf
        rw [← mulVec_mulVec,← mulVec_mulVec,ha,ha]; unfold tidal; rw[bill_pay,bill_pay]; exact congr_arg (dotProduct x) (congr($(hf) y))
    obtain ⟨hs,ht⟩:=shell_guard U k h hμ he
    have hA: Military A:= trench_orthogonal _; have hB:Military B:=troop_orthogonal _
    refine ⟨hp,?_,?_⟩
    · let F(u:Config G f):= fderiv ℝ (fderiv ℝ (lyre Y u)) 0
      have he(u): refrain Y u = fun i j=> F u ((pocket _) i) ((pocket _) j):= by unfold refrain; simp only[iteratedFDeriv_two_apply]; rfl
      unfold shoreX; rw[he,he]; apply trap_guard _ _ L hA hA hs
      intro x y
      have hr := ((hh.iteratedFDeriv ℝ 2).eq_of_nhds)
      have hx := DFunLike.congr_fun hr (![x,y])
      rw [L.iteratedFDeriv_comp_left hu (by exact le_top)] at hx
      rw [wired L (by rw[map_zero]; exact hv.analyticAt),map_zero] at hx
      rw[ha,ha]
      change iteratedFDeriv ℝ 2 (lyre Y V) _ _=L (iteratedFDeriv ℝ 2 (lyre Y U) _ _) at hx
      simp only [iteratedFDeriv_two_apply] at hx; exact hx
    let Z(u:Config G f):= tidal Y u+(tidal Y u)ᵀ; let T:=shoreM p R μ Y
    have hc : T V*A=B*T U:=by
       have hf: (mail V)ᵀ*A=B*(mail U)ᵀ:= hB.transpose_cross hA (mail_carry _ _)
       have hx: Z V*A=A*Z U:=by rw[show Z V*A=_+ _ from Matrix.add_mul ..,show A*Z U=_+ _ from Matrix.mul_add .., hp, hA.transpose_cross hA hp]
       change shellG μ V*(mail V)ᵀ*Z V*shellB p R μ V*A=_; rw [Matrix.mul_assoc _ (shellB p R μ V), show shellB p R μ V*A = _ from hs, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Z V),hx, ← Matrix.mul_assoc, Matrix.mul_assoc (shellG μ V) (mail V)ᵀ,hf, ← Matrix.mul_assoc, show shellG μ V*B=_ from ht]; change B*shellG μ U*(mail U)ᵀ*Z U*shellB p R μ U=_; unfold T shoreM Z; simp only [Matrix.mul_assoc]
    obtain ⟨F,hF⟩:= juke_form U; obtain ⟨F',hF'⟩:= juke_form V
    change trapw (T V) (fun i j=> jukebox V ((pocket _) i) ((pocket _) j)) = L (trapw (T U) _)
    unfold jeps; simp_rw [hF,hF']; refine trap_guard (P:=A) (Q:=B) _ _ L hA hB hc ?_; intro x y; rw[ha,hb,← hF,← hF']; exact lull_turn U k x y
end YM.Trace.Det
