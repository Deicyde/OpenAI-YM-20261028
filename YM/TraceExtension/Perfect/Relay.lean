import YM.TraceExtension.Perfect.Ordinal

/-! # Actual price-matched directional Ward lift; preserve stationary representatives off shell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {c f:Side}{S:StepData c f}{G:Gauge}{p u:Clip}{M R:PathData G}{η α D:ℝ}
variable {ρ : BaseSites G f → ℝ}{F:Forest S.ratio}
variable (r : Bid.Dir G c→AxisChart G F)
variable (t:S.Choices)

def fineRelay (S:StepData c f) (t:S.Choices)(U:Joint G c f) : Link G f→L[ℝ] Link G c := fderiv ℝ (worn S t 1 U) 0 ∘L ContinuousLinearMap.inl ℝ _ _

def inureL (S:StepData c f)(V Y:Config G c)(x:Link G c):=tickets S (input _ _ x*V) Y

omit t r in
lemma payer (S:StepData c f) (V Y:Config G c)(x : Link G c) : inureL S V Y (-x)=inure S V Y x:=by
    let Q := input _ _ x
    have he : input G c (-x)=Q⁻¹ := by funext i; simp only [Q, Pi.inv_apply,input_color,map_neg,Pi.neg_apply,Work.F03.exp_neg_color]
    unfold inureL inure tickets; apply congr_arg; apply Finset.sum_congr rfl; intro i _; rw [he, Pi.mul_apply,Pi.inv_apply]
    rw [← G.price_conj ((Q i)⁻¹) (V i*((input _ _ x*Y) i)⁻¹)]
    simp only [Pi.mul_apply]; dsimp only [Q]; group

omit r in
lemma duo_close (V:Config G c) (U:Joint G c f) (x:Link G f)(h : Shell S t p M V U) (he : Teller S t p M 1 U):
    fderiv ℝ (burn p M U.1) 0 x=fderiv ℝ (inureL S V (ribbon S t U)) 0 (fineRelay S t U x) :=by
    let H:=burn p M U.1; let B:= inure S V (ribbon S t U); let Y:= inureL S V (ribbon S t U)
    let Q:= worn S t 1 U; let L:=ContinuousLinearMap.fst ℝ (Link G f) (BaseSites G c)
    have hw : canon S t p M V U=ᶠ[𝓝 0] (H ∘ L)+(B ∘ Q) := by
        filter_upwards [he.shown] with v hv
        simp only [dress_one,atire] at hv
        change mainTerm p M ((Stationary.extend v*U).1) + _=H v.1+ tickets S V (input G c (Q v)*ribbon S t U)
        rw [show input G c (Q v)*ribbon S t U=_ from hv]; rfl
    have hh : DifferentiableAt ℝ H (L 0):=by rw [map_zero]; exact he.known.differentiableAt (by simp)
    have hP : Q 0=0 := worn_zero ..; have hx : DifferentiableAt ℝ B (Q 0):=by rw [hP]; exact (teller_fee ..).differentiableAt (by simp)
    have hz : DifferentiableAt ℝ Q 0:=he.wist.differentiableAt (by simp)
    let A:= -(ContinuousLinearMap.id ℝ (Link G c))
    have hy : Y=B ∘ A:= funext (fun v=> by change inureL _ _ _ v=inure _ _ _ (-v); nth_rewrite 1 [← neg_neg v]; exact payer S _ _ (-v))
    change fderiv ℝ H 0 x=fderiv ℝ Y 0 (fineRelay S t U x)
    have hf := hw.fderiv_eq (𝕜:=ℝ)
    rw [h.2,fderiv_add (hh.comp 0 L.differentiableAt) (hx.comp 0 hz), fderiv_comp 0 hh L.differentiableAt, L.fderiv,fderiv_comp 0 hx hz,map_zero,hP] at hf
    have he := DFunLike.congr_fun hf (x,0)
    rw [hy, fderiv_comp 0 (show DifferentiableAt ℝ B (A 0) by rwa [map_zero,← hP]) A.differentiableAt,map_zero,A.fderiv]
    change _ = fderiv ℝ B 0 (- (fderiv ℝ Q 0 (x,0))); rw [map_neg]; exact eq_neg_of_add_eq_zero_left (show fderiv ℝ H 0 x+_ = 0 from he.symm)

-- variation about arbitrary fields near the encamping graph
abbrev ramp (F:Forest S.ratio) (r:Bid.Dir G c→AxisChart G F)(t:S.Choices)(p : Clip)(M:PathData G)(z:Link G c):=muster S t p M (input G c z) (encamp F r z)

def cartMove (x y:Link G c):= content (input G c y* input G c x)
lemma cartDiff : ContDiffAt ℝ ω (uncurry (cartMove (G:=G) (c:=c))) 0:= (Army.mul (Army.powL (v:= Prod.snd) (contDiffAt_snd (p:=(0: Link G c × Link G c)))) (Army.powL contDiffAt_fst)).logL (by simp)
lemma cart_current : ∀ᶠ x : Link G c in 𝓝 0, cartMove x 0 = x:= by filter_upwards [input_encodes (G:=G) (m:=c)] with x hx; rw [cartMove,input_zero,one_mul,hx]

section
variable (hS:S.patch.Branches S.kernel G)
    (h:Critical F p M r)(hp:M.Bounds p η α D)
include h hp hS t
lemma rent_scene : ∀ᶠ x:Link G c in 𝓝 0, fderiv ℝ (ramp F r t p M) x ∘L fderiv ℝ (cartMove x) 0 = fderiv ℝ (inureL S (input G c x) (ribbon S t (encamp F r x))) 0:=by
    let f (X:Link G c × Link G c):=muster S t p M (input G c X.1) (encamp F r X.2)
    have hf : ContDiffAt ℝ ω f 0:=by
       let U := fun z:Link G c × Link G c => encamp F r z.2
       have ha : Thaw U 0:= Thaw.comp (g:=encamp F r) (w:=Prod.snd) (camp_thaw h) contDiffAt_snd
       exact ha.earn hS t (show (U 0).1=1 from congr_arg Prod.fst (encamp_zero h)) (Army.powL contDiffAt_fst) hp
    let B : Link G c→L[ℝ] (Link G c × Link G c):= (ContinuousLinearMap.id ..).prod (ContinuousLinearMap.id ..)
    have ht: (ramp F r t p M)= f ∘ B:=rfl
    have hX : Tendsto B (𝓝 0) (𝓝 0):=by simpa using B.continuous.tendsto 0
    have hv: Tendsto (fun x:Link G c=> (x,(0:Link G c))) (𝓝 0) (𝓝 0):=tendsto_id.prodMk_nhds tendsto_const_nhds
    have hc : ∀ᶠ v : Link G c × Link G c in 𝓝 0, input G c (cartMove v.1 v.2)=input G c v.2*input G c v.1:=by
        refine (show Tendsto (fun v : Link G c × Link G c =>input G c v.2*input G c v.1) (𝓝 0) (𝓝 1) from ?_).eventually content_encodes
        have hC : Army (fun v : Link G c × Link G c=>input G c v.2 *input G c v.1) 0:= (Army.powL contDiffAt_snd).mul (Army.powL contDiffAt_fst)
        simpa using hC.cont.tendsto
    have hT : ∀ᶠ x in 𝓝 (0:Link G c), Thaw (encamp F r) x:=by
      exact (eventually_all.mpr fun i=> (camp_thaw h|>.1 i).eventually (by simp)).and (eventually_all.mpr fun i=> (camp_thaw h|>.2 i).eventually (by simp))
    filter_upwards [camp_station h hS hp t,hX.eventually (hf.eventually (by simp)), cart_current (c:=c) (G:=G),hv.eventually (cartDiff (c:=c) (G:=G) |>.eventually (by simp)),hv.eventually (eventually_eventually_nhds.mpr hc),hT] with x hh hF hy hy' hx hZ
    let V:=input G c x; let D:=cartMove x; let z:=encamp F r x
    let J : Link G c → Link G c × Link G c:=fun v => (x,v)
    have hv : DifferentiableAt ℝ D 0:=Work.F05.hold_jet hy' |>.differentiableAt (by simp)
    have h₀ : D 0=x:=hy
    let U : Link G c → Link G c × Link G c:= fun i =>(D i,x)
    have hu : U 0=B x:=by rw [show U 0=(D 0,x) from rfl,h₀];rfl
    have hD: HasFDerivAt U ((fderiv ℝ D 0).prod 0) 0 :=hv.hasFDerivAt.prodMk (hasFDerivAt_const ..)
    have hw: (fun i:Link G c=> mainTerm p M z.1)+inureL S V (ribbon S t z)=ᶠ[𝓝 0] f ∘ U:=by
        have H : ∀ᶠ a : Link G c in 𝓝 0, input G c (D a) = input G c a*input G c x:= Work.F05.hold_near (V:=fun j: Link G c× Link G c=>input G c (cartMove j.1 j.2)=input G c j.2*input G c j.1) hx
        filter_upwards [H] with a ha
        change _= mainTerm p M z.1 + tickets S (input _ _ (D a)) _
        rw [ha];rfl
    have h' : DifferentiableAt ℝ f (B x):=hF.differentiableAt (by simp)
    have hg : fderiv ℝ (fun i : Link G c=> f (x,i)) x=0:= hh.chain hZ rfl
    have hz: DifferentiableAt ℝ (inureL S V (ribbon S t z)) 0:=by
       -- subtract const
       let u :Link G c→ℝ:=fun _=> mainTerm p M z.1
       apply DifferentiableAt.congr_of_eventuallyEq (f:= f ∘ U-u) ((DifferentiableAt.comp 0 (hu.symm ▸ h') hD.differentiableAt).sub (differentiableAt_const _))
       filter_upwards [hw] with a ha; rw [Pi.sub_apply,← ha]; change inureL S V (ribbon S t z) a=u a+inureL S V (ribbon S t z) a-u a; abel
    have hR:=hw.fderiv_eq (𝕜:=ℝ); rw [fderiv_add (differentiableAt_const _) hz, show fderiv ℝ (fun _ : Link G c=> mainTerm p M z.1) 0=0 from (hasFDerivAt_const ..).fderiv, zero_add,fderiv_comp 0 (hu.symm ▸ h') hD.differentiableAt,hD.fderiv,hu] at hR
    change _=fderiv ℝ (inureL S V (ribbon S t z)) 0
    rw [hR,ht,fderiv_comp x h' B.differentiableAt,B.fderiv]; ext1 y
    let W:= fderiv ℝ f (B x); let X:= fderiv ℝ D 0 y
    have hP:W (0,X)=0:=by
        let L:=(0:Link G c→L[ℝ]Link G c).prod (ContinuousLinearMap.id ..)
        have hk: J x=B x:= rfl; have he : HasFDerivAt J L x:= (hasFDerivAt_const ..).prodMk (hasFDerivAt_id x)
        have hf: fderiv ℝ (f ∘ J) x=0:= hg
        rw [fderiv_comp _ (hk.symm ▸ h') he.differentiableAt, he.fderiv,hk] at hf; exact DFunLike.congr_fun hf X
    change W (X,X)=W (X,0); rw [show ((X,X):Link G c×Link G c)=(X,0)+(0,X) by simp,map_add,hP,add_zero]
end

section
variable (hS:S.patch.Branches S.kernel G)
    (h:Critical F p M r)(hp:M.Bounds p η α D)(he:ClassicalMatch F p u M R r)
include h hp hS t
local notation "K"=>fun v:Link G c=> mainTerm u R (input G c v)

include he
omit hp h hS in
lemma ramps_equal : braid (ramp F r t p M) (K) 0 4 ∧ ContDiffAt ℝ ω (ramp F r t p M) 0 ∧ ContDiffAt ℝ ω (K) 0:=by
 let A := fun x=> tested F t p M x (r x)
 let H := fun (x:fieldDir G c 1)=> mainTerm u R (represent x)
 let L := arm G c 1
 have hv : ramp F r t p M=A ∘ L:= funext fun x=> camp_claim ..
 have hf : ContDiffAt ℝ ω A (L 0):=by rw [map_zero]; exact (he 0 (by decide) t).1
 have hh : ContDiffAt ℝ ω H (L 0):=by rw [map_zero]; exact (he 0 (by decide) t).2.1
 rw [hv]; change braid (A ∘ L) (H ∘ L) _ _ ∧ _ ∧ ContDiffAt ℝ ω (H ∘ L) _
 refine ⟨wove ?_ hf hh L.contDiff.contDiffAt,hf.comp (f:=L) _ L.contDiff.contDiffAt,hh.comp (f:=L) _ L.contDiff.contDiffAt⟩
 intro i hi; rw [map_zero]; exact (he _ hi t).2.2

omit t hp h hS he in
lemma slope_links {R:PathData G} {u} (hm:ContDiffAt ℝ ω (fun x: Link G c=> mainTerm u R (input G c x)) 0) :
  ∀ᶠ x:Link G c in 𝓝 0, fderiv ℝ (fun z: Link G c=> mainTerm u R (input G c z)) x ∘L fderiv ℝ (cartMove x) 0=fderiv ℝ (burn u R (input G c x)) 0 ∧ ContDiffAt ℝ ω (burn u R (input G c x)) 0:=by
 let Z : Link G c× Link G c→ Config G c:= fun p=>input G c p.2*input G c p.1
 have hz: Tendsto (fun x:Link G c=> (x,(0:Link G c))) (𝓝 0) (𝓝 0):=tendsto_id.prodMk_nhds tendsto_const_nhds
 have ht : Tendsto Z (𝓝 0) (𝓝 1):= by
      let U : Army Z 0:= (Army.powL contDiffAt_snd).mul (Army.powL contDiffAt_fst)
      simpa [Z] using U.cont.tendsto
 filter_upwards [hm.eventually (by simp),cart_current (G:=G) (c:=c),hz.eventually ((cartDiff (G:=G) (c:=c)).eventually (by simp)), hz.eventually (eventually_eventually_nhds.mpr (ht.eventually content_encodes))] with x ha hu hc hh
 have hv : ContDiffAt ℝ ω (cartMove x) 0:=Work.F05.hold_jet hc
 let H := fun z:Link G c=> mainTerm u R (input G c z)
 have he : H ∘ cartMove x=ᶠ[𝓝 0] burn u R (input G c x):=by
     filter_upwards [Work.F05.hold_near (V:=fun p:Link G c× Link G c=> input G c (content (Z p))=Z p) hh] with a ht;  exact congr_arg (mainTerm u R) ht
 have h0: ContDiffAt ℝ ω H (cartMove x 0):= hu.symm ▸ ha
 have hf:= he.fderiv_eq (𝕜:=ℝ)
 rw [fderiv_comp 0 (h0.differentiableAt (by simp)) (hv.differentiableAt (by simp)),hu] at hf
 exact ⟨hf,(h0.comp _ hv).congr_of_eventuallyEq he.symm⟩
theorem recoup {Y:Link G c→Link G f} (hY : ContDiffAt ℝ ω Y 0)(hb:Y 0=0) :
    braid (fun x=> fderiv ℝ (burn p M (encamp F r x).1) 0 (Y x))
       (fun x=> fderiv ℝ (burn u R (input G c x)) 0 (fineRelay S t (encamp F r x) (Y x))) 0 4:=by
   let U:=encamp F r
   let A (x:Link G c) := fineRelay S t (U x) (Y x)
   let B (x:Link G c):= fderiv ℝ (cartMove x) 0 (A x)
   have ht : ContDiffAt ℝ ω A 0 := by
        have hp:= Work.F05.curve_partial (F:=fun x=> worn S t 1 (U x)) (worn_wear hS t U (camp_thaw h) (encamp_zero h))
        let f (x:Link G c):=(Y x,(0:BaseSites G c)); have hh :ContDiffAt ℝ ω f 0:= hY.prodMk contDiffAt_const
        exact (hp.comp (f:=fun x:Link G c=>(x,0)) 0 (by fun_prop)).clm_apply hh
   have hB :ContDiffAt ℝ ω B 0:=
      ((Work.F05.curve_partial (cartDiff (c:=c) (G:=G))).comp (f:=fun x:Link G c=>(x,0)) 0 (by fun_prop)).clm_apply ht
   obtain ⟨hp',hf,hy⟩:= ramps_equal r t he
   have hv := spirals hp' hf hy (show B 0=0 by unfold B A;rw [hb,map_zero,map_zero]) hB
   refine (braid.trans (braided ?_) hv).trans (braided ?_)
   · filter_upwards [rent_scene r t hS h hp,camp_station h hS hp t,Stationary.awake t hp (camp_thaw h) (by rw [encamp_zero h]; rfl) hS root_customs] with x h₀ hb' hx
     exact (duo_close t _ _ _ hb' hx).trans (DFunLike.congr_fun h₀.symm (A x))
   filter_upwards [(slope_links (G:=G) (c:=c) hy)] with x hx; exact DFunLike.congr_fun hx.1 (A x)
end
lemma cant_zero_slope {p : Clip}{G:Gauge}{R:PathData G}{c: Side} {V : Config G c}{σ A Λ:ℝ}(hr:R.Bounds p σ A Λ)(hx:ContDiffAt ℝ ω (burn p R V) 0)(y:BaseSites G c) :
    fderiv ℝ (burn p R V) 0 (cant V y) = 0:=by
 -- intrinsic support costs later. use exp-gauge
 let Y (k:ℝ):= Lattice.gauge (switchSite (k • y)) V
 have hV : Y (0:ℝ)=V:=by rw [show Y (0:ℝ)=_ from rfl]; change Lattice.gauge _ _=_; simp [gauge_one]
 let D(k:ℝ):=content (Y k*V⁻¹)
 have he : HasDerivAt D (cant V y) 0:=by
    refine ray_content (show Y (0:ℝ)*V⁻¹=1 by rw [hV,mul_inv_cancel]) (fun i => ?_)
    simp only [Y,Lattice.gauge,Pi.mul_apply,Pi.inv_apply,G.mat_mul,G.mat_inv]
    convert! (((ray_power y i.1).mul_const (G.mat (V i))).mul (ray_power y (i.1+step i.2)).star).mul_const (star (G.mat (V i))) using 1
    simp [cant_at,G.colorMat_skew,Gauge.conjugate,add_mul, Matrix.mul_assoc]; rfl
 have hw : Tendsto (fun k:ℝ=> Y k*V⁻¹) (𝓝 0) (𝓝 1):= by
    rw [show (1:Config G c)=Y 0*V⁻¹ from by rw [hV,mul_inv_cancel]]; refine ContinuousAt.tendsto (ContinuousAt.mul ?_ continuousAt_const); unfold Y; apply Army.cont (Army.slant ?_ (Army.park V _)); exact Army.powG (by fun_prop)
 have hK : (burn p R V) ∘ D =ᶠ[𝓝 0] fun _ : ℝ=> mainTerm p R V:=by
    filter_upwards [hw.eventually content_encodes] with a ha; change mainTerm p R (input G c (D a)*V)=_; rw [show input G c (D a)=_ from ha,inv_mul_cancel_right]; exact Work.F05.mainTerm_gauge hr ..
 have hD : D 0=0:=by unfold D; rw [hV,mul_inv_cancel,content_one]
 have h' := ((show HasFDerivAt (burn p R V) (fderiv ℝ (burn p R V) 0) (D 0) from hD.symm ▸ (hx.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 he)
 exact h'.unique ((hasDerivAt_const ..).congr_of_eventuallyEq hK)

end YM.Trace.Perfect
