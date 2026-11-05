import YM.TraceExtension.Det.Tend

/-!
# Gauge along moving left link. Off shell curvature equation. HM bled into EOM insert
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{f:Side}{p:Clip}{R:PathData G}{Y:Gal G f}{α C D:ℝ}
    {T:Type}[NormedAddCommGroup T][NormedSpace ℝ T][FiniteDimensional ℝ T][CompleteSpace T]
    (U:Config G f)

def lyric (u:BaseSites G f)(z:Link G f):= Lattice.gauge (switchSite u) (input G f z*U) * U⁻¹
def lull (u:BaseSites G f)(z:Link G f): Link G f:=content (lyric U u z)
def juke (u:BaseSites G f)(z:Link G f): Link G f:= fderiv ℝ (fun h=> lull U h z) 0 u
def jukebox (U:Config G f)(x:Link G f)(u:BaseSites G f):Link G f:=fderiv ℝ (juke U u) 0 x
abbrev jeps (U:Config G f)(i:Lines G f 1)(j:Lines G f 0):= jukebox U ((pocket _) i) ((pocket _) j)
abbrev tuneM (p:Clip)(R:PathData G)(U:Config G f): Matrix (Lines G f 1) (Lines G f 0) ℝ:= of fun i j => fderiv ℝ (burn p R U) 0 (jeps U i j)
lemma lullArmy : Army (uncurry (lyric U)) 0:=by
    exact ((Army.powG (v:=Prod.fst) contDiffAt_fst).slant ((Army.powL (v:=Prod.snd) contDiffAt_snd).mul (Army.park _ _))).mul (Army.park _ _)
lemma lyric_axis (z:Link G f) : lyric U 0 z=input G f z:=by simp [lyric]
lemma lull_analytic : ContDiffAt ℝ ω (uncurry (lull U)) 0:= (lullArmy U|>.logL (show lyric U 0 0=1 by rw[lyric_axis,input_zero]))
lemma lull_o : lull U 0 0=0:=by rw[lull,lyric_axis,input_zero,content_one]
lemma lyric_enc : ∀ᶠ u:BaseSites G f in 𝓝 0,input G f (lull U u 0)*U= Lattice.gauge (switchSite u) U:=by
    let F u:= lyric U u 0
    have hh : Army F 0:=(lullArmy U).comp (g:=uncurry (lyric U)) (w:=fun u=>(u,0)) (by fun_prop)
    have hF: F 0=1:=by unfold F; rw [lyric_axis,input_zero]
    filter_upwards [(show Tendsto F (𝓝 0) (𝓝 1) from hF ▸ hh.cont.tendsto).eventually content_encodes] with u hu; rw[lull,show input G f (content (lyric U u 0))=lyric U u 0 from hu,lyric];simp
lemma lull_home (u:BaseSites G f) : juke U u 0=cant U u:=by
    have hp: HasDerivAt (fun v:ℝ=> lull U (v • u) 0) (cant U u) 0:=by
       refine ray_content (show lyric U ((0:ℝ) • u) 0=1 by rw [zero_smul,lyric_axis,input_zero]) (fun i => ?_)
       simp only [lyric,input_zero,one_mul,Lattice.gauge,Pi.mul_apply,Pi.inv_apply,G.mat_mul,G.mat_inv]
       convert! (((ray_power u i.1).mul_const (G.mat (U i))).mul (ray_power u (i.1+step i.2)).star).mul_const (star (G.mat (U i))) using 1
       simp [cant_at,G.colorMat_skew,Gauge.conjugate,add_mul, Matrix.mul_assoc]; rfl
    have ht: ContDiffAt ℝ ω (fun h:BaseSites G f=> lull U h 0) 0:= (lull_analytic U).comp (f:=fun u:BaseSites G f=> (u,0)) 0 (by fun_prop)
    exact (Push.side _ (ht.differentiableAt (by simp)) u).unique hp
lemma juke_form : ∃ B: Link G f →L[ℝ] BaseSites G f →L[ℝ] Link G f, ∀ u v, jukebox U u v=B u v:=by
    let T:= fun z:Link G f=> fderiv ℝ (fun h=> lull U h z) 0; let B:= fderiv ℝ T 0
    have hT: ContDiffAt ℝ ω T 0:=by
        let M:=(fun x:Link G f=>fun u:BaseSites G f=>lull U u x)
        have he: ContDiffAt ℝ ω (uncurry M) 0:= (lull_analytic U).comp (f:=fun z:Link G f× BaseSites G f=>(z.2,z.1)) 0 (by fun_prop)
        exact (Work.F05.curve_partial he).comp (f:=fun x:Link G f=> (x,0)) 0 (by fun_prop)
    refine ⟨B,fun u v=>?_⟩; let L:= ContinuousLinearMap.apply ℝ (Link G f) v
    unfold jukebox; rw[show juke U v=L∘ T from rfl, fderiv_comp 0 L.differentiableAt (hT.differentiableAt (by simp)),L.fderiv]; rfl
lemma hum (h:R.Bounds p α C D): flare p R U * mail U = - tuneM p R U:=by
    let V:=burn p R U; let T:=lull U
    have ht:= lull_analytic U; have hv:= burn_cov U h
    have hi: ∀ᶠ z:BaseSites G f × Link G f in 𝓝 0, V (T z.1 z.2)= V z.2:=by
        have hp: lyric U 0 0=1:=by rw [lyric_axis,input_zero]
        filter_upwards [(show Tendsto (uncurry (lyric U)) (𝓝 0) (𝓝 1) from hp ▸ (lullArmy U).cont.tendsto).eventually content_encodes] with z hz; unfold T V; rw [lull, burn, show input _ _ (content (lyric U z.1 z.2))=_ from hz]; change mainTerm p R (lyric _ _ _*_)=_;rw [lyric,inv_mul_cancel_right]; exact Work.F05.mainTerm_gauge h ..
    ext i j; let x:Link G f:=(pocket _) i; let y:BaseSites G f:=(pocket _) j
    have he: (fun z=> fderiv ℝ V z (juke U y z))=ᶠ[𝓝 0] fun _=>0:=by
        let g(z:Link G f):= ((0:BaseSites G f),z); have hG: Tendsto g (𝓝 0) (𝓝 0):= tendsto_const_nhds.prodMk_nhds tendsto_id
        filter_upwards [el_slice hi,hG.eventually (ht.eventually (by simp)),hv.eventually (by simp),input_encodes (G:=G) (m:=f)] with z hz ht hv hl
        let L(u:BaseSites G f):= lull U u z
        have hL: ContDiffAt ℝ ω L 0:=ht.comp (f:=fun u:BaseSites G f=> (u,z)) 0 (by fun_prop)
        have hk: L 0=z:=by unfold L;rw[lull,lyric_axis,hl]
        have hh := fderiv_comp (g:=V) (f:=L) 0 (by rw[hk]; exact hv.differentiableAt (by simp)) (hL.differentiableAt (by simp))
        rw [(show V ∘ L =ᶠ[𝓝 0] fun _=>V z from hz).fderiv_eq, fderiv_fun_const,hk] at hh; exact congr($(hh.symm) y)
    have hp:= f_clm (u:=juke U y) (L:=fderiv ℝ V) x 0 (keep_l ht y) (hv.fderiv_right (by simp))
    rw[he.fderiv_eq,fderiv_fun_const] at hp
    have hz : fderiv ℝ V 0 (jukebox U x y)+ iteratedFDeriv ℝ 2 V 0 ![x,cant U y]=0:=by
       rw[← lull_home,iteratedFDeriv_two_apply]; exact hp.symm
    have hw : iteratedFDeriv ℝ 2 V 0 ![x,cant U y]=(flare p R U *mail U) i j:=by
        rw[← detracts (pocket _),cash_pocket,cash_pocket, ← mailed,mulVec_mulVec]; change dotProduct x ((flare p R U *mail U) *ᵥ y)=_; rw [show x=Pi.single i 1 by simp[x], show y=Pi.single j 1 by simp [y]]; simp
    exact hw ▸ (eq_neg_of_add_eq_zero_right hz)

lemma meet_mail_n (V:T → Config G f)(h:Army V 0)(hp:V 0=1)(hx:Cloaked Y):
    ∀ᶠ z in 𝓝 0,∀ᶠ u:BaseSites G f in 𝓝 0,
    Y (Lattice.gauge (switchSite u) (V z))=armor (switchSite u) (Y (V z)):=by
    let F (z:BaseSites G f × T):= V z.2
    let k (z:BaseSites G f × T):= switchSite z.1
    have hv : Army F 0:= Army.comp (g:=V) (w:=Prod.snd) h contDiffAt_snd
    have ht:= hx.jacket (BaseSites G f × T) F k 1 hv hp (Army.powG contDiffAt_fst) (by unfold k;simp;rfl)
    exact el_slice ht

lemma ps_lull (hY: ∀ᶠ u:BaseSites G f in 𝓝 0,Y (Lattice.gauge (switchSite u) U)=armor (switchSite u) (Y U))(s:ℝ):
    (fun u:BaseSites G f=> lyr Y U s (lull U u 0))=ᶠ[𝓝 0] fun u=> lull (tendr Y s U) u 0:=by
    filter_upwards [hY,lyric_enc U] with x hx hv
    rw [lyr,psm,hv, lull]; congr 2
    unfold tendr; rw [hx,← map_smul, armor_go,input_zero,one_mul]
lemma rising (h:Tune Y U)(hY:∀ᶠ u:BaseSites G f in 𝓝 0,Y (Lattice.gauge (switchSite u) U)=armor (switchSite u) (Y U)) : directionM (fun s=> mail (tendr Y s U)) 0 1 = tidal Y U * mail U:=by
    let W(s):=tendr Y s U
    let P:=lyr Y U
    have hP : ContDiffAt ℝ ω (uncurry P) 0:= tune_diff U h
    have ht: ContDiffAt ℝ ω (fun u:BaseSites G f=> lull U u 0) 0:= (lull_analytic U).comp (f:=fun u:BaseSites G f=> (u,(0:Link G f))) 0 (by fun_prop)
    ext i j
    let x:BaseSites G f:=(pocket _) j; let L(s:ℝ):= fderiv ℝ (P s) 0 (cant U x)
    have hh: (fun s:ℝ=> cant (W s) x)=ᶠ[𝓝 0] L:=by
        filter_upwards [(show Tendsto (fun s=> (s,(0:Link G f))) (𝓝 (0:ℝ)) (𝓝 0) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually (hP.eventually (by simp))] with s hs
        have hv : ContDiffAt ℝ ω (P s) 0:= hs.comp (f:=fun v=>(s,v)) 0 (by fun_prop)
        let g:= fun u:BaseSites G f=> lull U u 0
        rw [← lull_home]; unfold L; rw [← lull_home U]; unfold juke
        have hx : fderiv ℝ (fun u=> lull (W s) u 0) 0 = (fderiv ℝ (P s) 0) ∘L fderiv ℝ g 0:=by
           rw [← (show P s ∘ g=ᶠ[𝓝 0] fun u=>lull (W s) u 0 from ps_lull U hY s).fderiv_eq, fderiv_comp (0:BaseSites G f) _ (ht.differentiableAt (by simp)), lull_o U]
           rw [lull_o U]; exact hv.differentiableAt (by simp)
        exact congr($(hx) x)
    let N:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Lines G f 1=>ℝ) i
    have hp: ContDiffAt ℝ ω L 0:= (analytic_r hP (cant U x)).comp (f:=fun s=> (s,(0:Link G f))) 0 (by fun_prop)
    change fderiv ℝ (fun s=> mail (W s) i j) 0 1=(tidal Y U * mail U) i j
    rw [(show (fun s=>mail (W s) i j)=ᶠ[𝓝 0] N ∘ L from hh.mono fun s hs=>by change mail (W s) i j=N (L s); rw[← hs]; rw [mail,bill_def,cash_pocket]; rfl).fderiv_eq,fderiv_comp _ N.differentiableAt (hp.differentiableAt (by simp)), N.fderiv]
    change N (fderiv ℝ L 0 1)= _; rw [show fderiv ℝ L 0 1=fderiv ℝ (lyre Y U) 0 (cant U x) from (exchange hP _ _).symm,← bill_pay, ← mailed, mulVec_mulVec]
    rw [show x=Pi.single j 1 by simp [x],Matrix.mulVec_single_one]; rfl
end YM.Trace.Det
