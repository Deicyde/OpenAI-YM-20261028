import YM.TraceExtension.Det.Calx
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{f:Side}{p:Clip}{R:PathData G}{Y:Gal G f}{α C D:ℝ}
    {T:Type}[NormedAddCommGroup T][NormedSpace ℝ T][FiniteDimensional ℝ T][CompleteSpace T]
    (U:Config G f)
abbrev Onus (G:Gauge)(f:Side):= Link G f×Link G f

def tendr (Y:Gal G f) (s:ℝ) (U:Config G f):Config G f:= input G f (s • Y U)* U
@[simp] lemma tendr_o : tendr Y 0 U=U:=by simp [tendr]
def psm (Y:Gal G f)(U:Config G f)(s:ℝ)(z:Link G f):= tendr Y s (input G f z*U)*(tendr Y s U)⁻¹
def lyr (Y:Gal G f)(U:Config G f)(s:ℝ)(z:Link G f): Link G f:=content (psm Y U s z)
def lyre (Y:Gal G f)(U:Config G f)(z:Link G f): Link G f := fderiv ℝ (fun s=> lyr Y U s z) 0 1
def tidal (Y:Gal G f)(U:Config G f):= billsM (pocket _) (pocket _) (fderiv ℝ (lyre Y U) 0)
def refrain (Y: Gal G f)(U:Config G f)(i j: Lines G f 1):Link G f:= iteratedFDeriv ℝ 2 (lyre Y U) 0 ![(pocket _) i,(pocket _) j]
lemma ps_z (s:ℝ): psm Y U s 0=1:=by simp[psm]
lemma ps_o (z:Link G f): psm Y U 0 z=input G f z:=by simp [psm]
lemma ly_o : lyr Y U 0 =ᶠ[𝓝 0] id:=by filter_upwards [input_encodes (G:=G) (m:=f)] with z hz; simp only [lyr,ps_o];exact hz
lemma ly_z (s:ℝ): lyr Y U s 0=0:=by rw[lyr,ps_z,content_one]
lemma lyre_z : lyre Y U 0=0:=by unfold lyre; simp_rw [ly_z]; simp

def bal (U:Config G f)(V:Peat G f)(z:Link G f):= V (input G f z*U)
def beamH (V:Peat G f)(U:Config G f):= damage (pocket _) (bal U V) 0
def beamG (V:Peat G f)(U:Config G f):= fderiv ℝ (bal U V) 0
lemma beam_p (V:Peat G f)(U:Config G f)(i j): beamH V U i j=iteratedFDeriv ℝ 2 (bal U V) 0 ![(pocket _) i,(pocket _) j]:=by rw [beamH,damage,LinearMap.toMatrix₂_apply,Work.F05.bend_apply]
lemma burn_p (p:Clip)(R:PathData G)(i j): flare p R U i j=iteratedFDeriv ℝ 2 (burn p R U) 0 ![(pocket _) i,(pocket _) j]:= beam_p (G:=G) (mainTerm p R) U _ _
lemma rate_burn (h:R.Bounds p α C D): ContDiffAt ℝ ω (uncurry (fun s=> burn p R (tendr Y s U))) 0:=by
    have hh : Army (fun z:ℝ × Link G f=> input G f z.2 * tendr Y z.1 U) 0:=
       (Army.powL (v:=Prod.snd) contDiffAt_snd).mul ((Army.powL (v:=fun z:ℝ × Link G f=> z.1 • Y U) (by fun_prop)).mul (Army.park _ _))
    exact Work.F02.mainTerm_contDiffAt (A:=_) h hh
lemma burn_cov (h:R.Bounds p α C D): ContDiffAt ℝ ω (burn p R U) 0:=Work.F02.mainTerm_contDiffAt (A:=fun z:Link G f=> input G f z*U) h ((Army.powL (v:=id) contDiffAt_id).mul (Army.park _ _))
def Tune (Y:Gal G f)(U:Config G f):= Army (uncurry (psm Y U)) 0
lemma tune_diff (h:Tune Y U): ContDiffAt ℝ ω (uncurry (lyr Y U)) 0:= ( (show Army (uncurry (psm Y U)) 0 from h)|>.logL (ps_z U 0))
lemma el_slice {M N:Type*}[TopologicalSpace M][TopologicalSpace N]{m:M}{n:N}{P:M×N→Prop}(h : ∀ᶠ z in 𝓝 (m,n), P z): ∀ᶠ x in 𝓝 n, ∀ᶠ s in 𝓝 m, P (s,x):=by
    rw[nhds_prod_eq] at h; obtain ⟨u,v,a,b,h⟩:= Filter.mem_prod_iff.mp h
    filter_upwards[b] with z hz; filter_upwards[v] with x hx; exact h ⟨hx,hz⟩
lemma orchestra (h:R.Bounds p α C D)(he:Tune Y U):
    bal U (aroma p R Y)=ᶠ[𝓝 0] fun z=> fderiv ℝ (fun s=> burn p R (tendr Y s U) z) 0 1+fderiv ℝ (burn p R U) z (lyre Y U z):=by
    let F(s):= burn p R (tendr Y s U)
    let P:= lyr Y U
    let pitch:= psm Y U
    have h1: ∀ᶠ z in 𝓝 ((0:ℝ),(0:Link G f)), mainTerm p R (tendr Y z.1 (input G f z.2*U))= F z.1 (P z.1 z.2):=by
       have hx : Tendsto (uncurry pitch) (𝓝 0) (𝓝 1):=(ps_z (Y:=Y) U (0:ℝ)) ▸ (show Army (uncurry pitch) 0 from he).cont.tendsto
       filter_upwards [hx.eventually content_encodes] with z hz; change _=mainTerm _ _ (input G f (content (uncurry pitch z))*_); rw [hz]; change _=mainTerm p R (tendr Y _ _*(tendr Y z.1 U)⁻¹*tendr Y z.1 U); simp
    have hP: ContDiffAt ℝ ω (uncurry P) 0:=tune_diff U he
    have hF: ContDiffAt ℝ ω (uncurry F) 0:=rate_burn U h
    let L (z:Link G f):= ((0:ℝ),z); have hi: Tendsto L (𝓝 0) (𝓝 0):= tendsto_const_nhds.prodMk_nhds tendsto_id
    filter_upwards[el_slice h1, hi.eventually (hP.eventually (by simp)),hi.eventually (hF.eventually (by simp)),ly_o (Y:=Y) U] with z hz ht hi hh
    change P 0 z=z at hh; let Q s:= P s z
    have he' : ContDiffAt ℝ ω Q 0:= ht.comp (f:=fun x:ℝ=>(x,z)) 0 (by fun_prop)
    let S:= input G f z*U
    let G':= fun s:ℝ=> s • Y S
    have hQ: HasDerivAt (fun s=> F s (Q s)) (fderiv ℝ (uncurry F) (0,z) (1,fderiv ℝ Q 0 1)) 0:=by
        let g:=fun s:ℝ=>(s,Q s)
        have hv: HasDerivAt g _ 0:= (hasDerivAt_id ..).prodMk ((he'.differentiableAt (by simp)).hasDerivAt)
        have hx : HasFDerivAt (uncurry F) (fderiv ℝ (uncurry F) (0,z)) (g 0):=by unfold g Q;rw[hh]; exact (hi.differentiableAt (by simp)).hasFDerivAt
        exact hx.comp_hasDerivAt 0 hv
    have he'' : HasDerivAt (fun s=> burn p R S (G' s)) (aroma p R Y S) 0:= HasFDerivAt.comp_hasDerivAt 0
        (show HasFDerivAt (burn p R S) (fderiv ℝ (burn p R S) 0) (G' 0) from by unfold G'; rw [zero_smul]; exact ((burn_cov S h).differentiableAt (by simp)).hasFDerivAt)
        (show HasDerivAt G' _ 0 from ray_id _)
    have hh' := he''.unique (hQ.congr_of_eventuallyEq hz)
    change aroma p R Y S=_
    rw[hh',show ((1,fderiv ℝ Q 0 1):ℝ × Link G f)= (1,0)+(0,fderiv ℝ Q 0 1) by simp,map_add,← d_l (F:=F) hi,← d_r (F:=F) hi,show F 0=burn p R U from by unfold F; rw[tendr_o]]; rfl
abbrev tensw (p:Clip)(R:PathData G)(Y:Gal G f)(U:Config G f):= of fun i j=> fderiv ℝ (burn p R U) 0 (refrain Y U i j)
lemma solo (h:R.Bounds p α C D)(he:Tune Y U):
    beamH (aroma p R Y) U= directionM (fun s=>flare p R (tendr Y s U)) 0 1+ flare p R U * tidal Y U+(tidal Y U)ᵀ*flare p R U+ tensw p R Y U:=by
    let F s:= burn p R (tendr Y s U); let V:=flare p R U; let T:=tidal Y U
    have hU:= burn_cov U h; have hF:ContDiffAt ℝ ω (uncurry F) 0:=rate_burn U h
    have hv := orchestra U h he; have hL:ContDiffAt ℝ ω (lyre Y U) 0:=keep_l (tune_diff U he) _
    ext i j
    let x: Link G f:= (pocket _) i; let y:Link G f:=(pocket _) j; let L:=fderiv ℝ (lyre Y U) 0
    rw [beamH,damage_congr _ hv,damage,LinearMap.toMatrix₂_apply,Work.F05.bend_apply]
    let D:= fun z=> fderiv ℝ (fun s=> F s z) 0 1
    let M:= fun z=> fderiv ℝ (burn p R U) z (lyre Y U z)
    change iteratedFDeriv ℝ 2 (D+M) 0 ![x,y]= fderiv ℝ (fun s=> flare p R (tendr Y s U) i j) 0 1+(V*T) i j+(Tᵀ*V) i j+_
    have hx : ContDiffAt ℝ ω D 0:=keep_l hF 1; have hm:ContDiffAt ℝ ω M 0:= ((hU.fderiv_right (m:=ω) (by simp)).clm_apply hL)
    rw [iteratedFDeriv_add_apply (hx.of_le le_top) (hm.of_le le_top), _root_.add_apply]
    unfold D M; rw [exchange_bend hF,clm_h hU hL (lyre_z U)]
    have ha: iteratedFDeriv ℝ 2 (burn p R U) 0 ![x,L y]=(V*T) i j:=by
        rw [← detracts (pocket _),cash_pocket,cash_pocket, ← bill_pay L y, Matrix.mulVec_mulVec]; change dotProduct x ((V*T) *ᵥ y) = _; rw [show x=Pi.single i 1 by simp[x],show y=Pi.single j 1 by simp [y]]; simp
    have hy : iteratedFDeriv ℝ 2 (burn p R U) 0 ![L x,y]=(Tᵀ*V) i j:=by
        rw [← detracts (pocket _),cash_pocket,cash_pocket, ← bill_pay L x, ← transposes,Matrix.mulVec_mulVec]; change dotProduct x ((Tᵀ*V)*ᵥ y)=_; rw [show x=Pi.single i 1 by simp[x],show y=Pi.single j 1 by simp[y]]; simp
    rw [show fderiv ℝ (lyre Y U) 0=L from rfl,ha,hy]; simp_rw [burn_p]; change fderiv ℝ (fun a=> iteratedFDeriv ℝ 2 (F a) 0 ![x,y]) 0 1+((V*T) i j+(Tᵀ*V) i j+tensw p R Y U i j)= fderiv ℝ (fun a=> iteratedFDeriv ℝ 2 (F a) 0 ![x,y]) 0 1+(V*T) i j+(Tᵀ*V) i j+ tensw p R Y U i j
    ring

lemma nod_z (h:Cloaked Y)(V:T→ Config G f)(hv:Army V 0)(hu:V 0=1):
    Army (fun z:T × (ℝ × Link G f)=> psm Y (V z.1) z.2.1 z.2.2) 0:=by
    let M:=T × (ℝ × Link G f)
    let p(z:M):=V z.1; let N(z:M):=input G f z.2.2*p z
    have he: Army p 0:= Army.comp (w:=Prod.fst) hv contDiffAt_fst; have hx: p 0=1:= hu
    have hp: Army N 0:= (Army.powL (v:=fun z:M=> z.2.2) contDiffAt_snd.snd).mul he
    have hh (U:M→ Config G f)(hU:Army U 0)(hu:U 0=1): Army (fun z:M=> tendr Y z.2.1 (U z)) 0:=by
       unfold tendr; exact (Army.powL ((show ContDiffAt ℝ ω (fun z:M=> z.2.1) 0 from contDiffAt_snd.fst).smul (h.put U hU hu))).mul hU
    have hf:N 0=1:=by unfold N; rw [hx]; simp
    exact (hh N hp hf).mul (hh p he hx).inv
lemma tune_n (h:Cloaked Y)(V:T→ Config G f)(hv:Army V 0)(hu:V 0=1): ∀ᶠ x in 𝓝 0,Tune Y (V x):=by
    have hp(i:Edge (Site f)):= (nod_z h V hv hu) i
    refine eventually_all.mpr fun i=>?_
    let L(x:T):= (x,(0:ℝ×Link G f)); have ht: Tendsto L (𝓝 0) (𝓝 0):= tendsto_id.prodMk_nhds tendsto_const_nhds
    filter_upwards [ht.eventually ((hp i).eventually (by simp))] with x hx; exact hx.comp (f:=fun y=> (x,y)) 0 (by fun_prop)
lemma tuned_c (h:Cloaked Y)(V:T→ Config G f)(hv:Army V 0)(hu:V 0=1):
    ContDiffAt ℝ ω (uncurry (fun s=> lyre Y (V s))) 0:=by
    let R(x:T)(s:ℝ)(z:Link G f):= lyr Y (V x) s z
    have hR: ContDiffAt ℝ ω (fun z:T× (ℝ × Link G f)=> R z.1 z.2.1 z.2.2) 0:=
        (nod_z h V hv hu|>.logL (ps_z _ _))
    let M(s:ℝ)(z:T×Link G f):= R z.1 s z.2
    exact keep_l (F:=M) (hR.comp (f:=fun z:ℝ × (T×Link G f)=> (z.2.1,z.1,z.2.2)) 0 (by fun_prop)) _
lemma memo_t (h:Cloaked Y)(V:T→ Config G f)(hv:Army V 0)(hu:V 0=1): Memo (tidal Y ∘ V) 0:=memo_rate _ _ (tuned_c h V hv hu)
lemma memo_y (h:Cloaked Y)(V:T→ Config G f)(hv:Army V 0)(hu:V 0=1)(i j:Lines G f 1): ContDiffAt ℝ ω (fun z=> refrain Y (V z) i j) 0:=by
    let u:Link G f:=(pocket _) i; let v:Link G f:=(pocket _) j; let D(x:T):=fderiv ℝ (lyre Y (V x))
    have hx:= Work.F05.curve_partial (tuned_c h V hv hu); have he:= Work.F05.curve_partial (F:=D) hx
    simp only[refrain,iteratedFDeriv_two_apply]
    exact ((he.comp (f:=fun x:T=> (x,(0:Link G f))) 0 (by fun_prop)).clm_apply (g:=fun _=> u) contDiffAt_const).clm_apply (g:=fun _=> v) contDiffAt_const

end YM.Trace.Det
