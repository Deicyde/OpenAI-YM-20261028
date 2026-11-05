import YM.TraceExtension.Lamp.Piston
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W} (d i b:Axis)(q:G.ColorIndex)
variable {Y:Gal G f}{F:Peat G f}
lemma dyed0 (h:Cloaked Y)(hp:G.Simple): Y 1=0:=by
    apply edgeColor.injective; ext1 i; rw[map_zero]; apply color_fixed_at hp
    intro u; let k:Coats G f := fun _=>u
    have ht:=h.jacket ℝ (fun _=>1) (fun _=>k) u (Army.park _ _) rfl (Army.park _ _) rfl; have hx:=ht.eq_of_nhds
    rw[show Lattice.gauge k 1=1 from strip_roots ..] at hx
    rw[show u=k i.1 from rfl, ← armor_at]; exact congr_arg (fun u=>edgeColor (G:=G) u i) hx.symm
lemma dyed_hold (h: Cleric F)(hp:G.Simple): fderiv ℝ (F ∘ input G f) 0=0:=by
    let H:= F ∘ input G f; ext1 x; apply oneFlag hp _ _ x
    intro u v; let k:Coats G f:= solid u; apply chain_fixed (A:=armor k) (F:=H) _ (h.dye.differentiableAt (by simp))
    have ht:= h.jacket (Link G f) (input G f) (fun _=>k) u (Army.powL (v:=id) contDiffAt_id) (input_zero ..) (Army.park _ _) rfl
    filter_upwards [ht] with x hx; exact (congr_arg F (show input G f (armor k x)=Lattice.gauge k (input G f x) from by
         have hp:=armor_go k x (1:Config G f); rw [show Lattice.gauge k 1=1 from strip_roots ..,mul_one,mul_one] at hp; exact hp)).trans hx
lemma dyed_cant (h:Cloaked Y)(hp:G.Simple)(x:BaseSites G f): fderiv ℝ (Y ∘ input G f) 0 (cant 1 x)=0:=by
    let W(a:BaseSites G f):=lull (1:Config G f) a 0; have ht := h.jacket (BaseSites G f) (fun _=>1) switchSite 1 (Army.park _ _) rfl (Army.powG (v:=id) contDiffAt_id) switch_zero
    have hW: ContDiffAt ℝ ω W 0:=(lull_analytic (1:Config G f)).comp (f:=fun x:BaseSites G f=> (x,0)) 0 (by fun_prop)
    let F:=Y ∘ input G f; have he: W 0=0:=lull_o _
    have hv:F∘ W=ᶠ[𝓝 0] (fun _=> 0):=by filter_upwards[ht,lyric_enc (1:Config G f)] with x hx hW; rw [dyed0 h hp,map_zero] at hx; rw [mul_one] at hW;exact (congr_arg Y hW).trans hx
    have hx:=hv.fderiv_eq (𝕜:=ℝ); rw[fderiv_comp _ (by rw[he];exact h.dye.differentiableAt (by simp)) (hW.differentiableAt (by simp)),he,fderiv_fun_const] at hx
    rw[← lull_home]; exact congr($(hx) x)
lemma dyed_beam (h:Cleric F)(hp:G.Simple): beamH F 1 * mail (1:Config G f)=0:=by
    let V:= input G f
    let A:=F ∘ V; have hx:ContDiffAt ℝ ω A 0:=h.dye; have hv:=dyed_hold h hp
    let T:= fun u=> lull (1:Config G f) u
    let L:= uncurry T;have hL:ContDiffAt ℝ ω L 0:=lull_analytic _; have ht: L 0=0:=lull_o _
    let J:= BaseSites G f×Link G f
    have hm: A ∘ L=ᶠ[𝓝 0] A ∘ Prod.snd:=by
       let K(z:J):=input G f z.2
       have ht : Army K 0:=Army.powL contDiffAt_snd
       have hf:= h.jacket J K (fun z:J=>switchSite z.1) 1 ht (by simp[K]) (Army.powG contDiffAt_fst) switch_zero
       let U:=uncurry (lyric (1:Config G f))
       have he:Tendsto U (𝓝 0) (𝓝 (U 0)) := (show Army U 0 from lullArmy (1:Config G f)).cont.tendsto
       rw [show U 0=1 from by change lyric _ 0 0=1; rw [lyric_axis,input_zero]] at he
       have hy:= he.eventually (content_encodes (G:=G) (m:=f))
       filter_upwards [hf,hy] with z hf hh; change input _ _ (L z)= _ at hh; unfold U at hh; simp only [uncurry,lyric,mul_one,inv_one] at hh; exact (congr_arg F hh).trans hf
    have he:= Work.F05.bend_comp_stationary (F:=A) (x:=0) (g:=L) (ht.symm ▸ hx) hL (ht.symm ▸ hv)
    have hg(u: BaseSites G f): fderiv ℝ L 0 (u,0)=cant 1 u:= Eq.trans (d_l (F:=T) hL u).symm (lull_home ..)
    have hz(u: Link G f): fderiv ℝ L 0 (0,u)=u:=by rw[← show fderiv ℝ (lull (1:Config G f) 0) 0 u= fderiv ℝ L 0 (0,u) from d_r (F:=T) hL u, (show lull (1:Config G f) 0 =ᶠ[𝓝 0] id from by filter_upwards[input_encodes (G:=G) (m:=f)] with a ha; rw [lull,lyric_axis]; exact ha).fderiv_eq,fderiv_id]; rfl
    rw [Work.F05.bend_congr hm, Work.F05.bend_comp_stationary (x:=(0:J)) hx (g:=Prod.snd) contDiffAt_snd hv, fderiv_snd, ht] at he
    apply testers; intro x y; rw[← mulVec_mulVec,mailed,zero_mulVec,dotProduct_zero, beamH]
    have hx := DFunLike.congr_fun (DFunLike.congr_fun he ((0,x):J)) ((y,0):J)
    simp only[LinearMap.compl₁₂_apply] at hx; change Work.F05.bend A 0 x 0=Work.F05.bend A 0 _ _ at hx; rw[map_zero] at hx
    rw[show bal (1:Config G f) F=A from funext fun x=> by unfold bal; rw[mul_one];rfl]; have he:= detracts (pocket (Lines G f 1)) A 0 x (cant 1 y); rw[cash_pocket,cash_pocket,← Work.F05.bend_apply, ← hg,← hz (u:=x)] at he
    rw[← hg, ← hz (u:=x)]; exact he.trans hx.symm
-- insertion kinetic
abbrev rill (F:Peat G f)(Y:Gal G f)(U:Config G f):= beamG F U (Y U)
def Kbody (F:Peat G f):= beamH F 1
def Tbody (Y:Gal G f):= billsM (pocket _) (pocket _) (fderiv ℝ (Y ∘ input G f) 0)
lemma body_sy (h:Cleric F): (Kbody F)ᵀ=Kbody F:=by unfold Kbody beamH; apply damage_symm (pocket (Lines G f 1)) (F:=bal 1 F) (by rw [show bal 1 F=F ∘ input G f from funext (fun i=>by simp[bal])]; exact h.dye)
private lemma slope_g (h:Cleric F):
  ∀ᶠ x:Link G f in 𝓝 0, fderiv ℝ (F ∘ input G f) x ∘L fderiv ℝ (cartMove x) 0=fderiv ℝ (bal (input G f x) F) 0:=by
 let Z : Link G f × Link G f→ Config G f:= fun p=>input G f p.2*input G f p.1
 have hz: Tendsto (fun x:Link G f=> (x,(0:Link G f))) (𝓝 0) (𝓝 0):=tendsto_id.prodMk_nhds tendsto_const_nhds
 have ht : Tendsto Z (𝓝 0) (𝓝 1):= by
      let U : Army Z 0:= (Army.powL contDiffAt_snd).mul (Army.powL contDiffAt_fst)
      simpa [Z] using U.cont.tendsto
 filter_upwards [h.dye.eventually (by simp),cart_current (G:=G) (c:=f),hz.eventually ((cartDiff (G:=G) (c:=f)).eventually (by simp)), hz.eventually (eventually_eventually_nhds.mpr (ht.eventually content_encodes))] with x ha hu hc hh
 have hv : ContDiffAt ℝ ω (cartMove x) 0:=Work.F05.hold_jet hc
 let H := F ∘ input G f
 have he : H ∘ cartMove x=ᶠ[𝓝 0] bal (input G f x) F:=by
     filter_upwards [Work.F05.hold_near (V:=fun p:Link G f× Link G f=> input G f (content (Z p))=Z p) hh] with a ht; exact congr_arg F ht
 have h0: ContDiffAt ℝ ω H (cartMove x 0):= hu.symm ▸ ha
 have hf:= he.fderiv_eq (𝕜:=ℝ)
 rw [fderiv_comp 0 (h0.differentiableAt (by simp)) (hv.differentiableAt (by simp)),hu] at hf; exact hf
lemma rill_state (h:G.Simple)(hf:Cleric F)(hv:Cloaked Y): ContDiffAt ℝ ω (rill F Y ∘ input G f) 0 ∧∀ x y, iteratedFDeriv ℝ 2 (rill F Y ∘ input G f) 0 ![x,y] = dotProduct (Tbody Y *ᵥ x) (Kbody F *ᵥ y)+dotProduct (Tbody Y *ᵥ y) (Kbody F *ᵥ x):=by
 let D:= Y ∘ input G f
 let X (y: Link G f):=fderiv ℝ (cartMove y) 0
 have ho : cartMove (G:=G) (c:=f) 0=ᶠ[𝓝 0] id:= by filter_upwards [input_encodes (G:=G) (m:=f)] with i hh; rw [cartMove,input_zero,mul_one,hh];rfl
 have ht(v:Link G f) : X 0 v=v:=by unfold X; rw [ho.fderiv_eq (𝕜:=ℝ), fderiv_id];rfl
 have hA : ContDiffAt ℝ ω X 0:= (Work.F05.curve_partial cartDiff).comp (f:=fun y:Link G f=>(y,0)) _ (by fun_prop)
 let L:=fun i=>X i (D i); have hD0:D 0=0:=by simp [D,dyed0 hv h];
 have hY: ContDiffAt ℝ ω L 0:= hA.clm_apply hv.dye
 have hp: L 0=0:=by unfold L; rw[hD0,map_zero];
 let A:=F ∘ input G f
 have hL(v): fderiv ℝ L 0 v=Tbody Y*ᵥ v:=by
    have he:= (hA.differentiableAt (by simp)).hasFDerivAt.clm_apply ((hv.dye.differentiableAt (by simp)).hasFDerivAt); rw [he.fderiv]; change X 0 (fderiv ℝ D 0 v)+ (fderiv ℝ X 0 v) (D 0)=_ ; rw[hD0,map_zero,add_zero,ht]; exact (bill_pay _ v).symm
 let R(x):= fderiv ℝ A x (L x)
 have hT: ContDiffAt ℝ ω R 0:= (hf.dye.fderiv_right (m:=ω) (by simp)).clm_apply hY
 have he:rill F Y ∘ input G f=ᶠ[𝓝 0] R:=by filter_upwards [slope_g hf] with i hh; exact DFunLike.congr_fun hh.symm (D i)
 have hW: Kbody F=damage (pocket _) A 0:=by unfold Kbody beamH; rw [show bal 1 F=A from funext (fun x=>by simp [bal,A])]
 have hm(x y:Link G f): dotProduct x (Kbody F*ᵥ y)=iteratedFDeriv ℝ 2 A 0 ![x,y]:=by rw[hW]; have ht':=detracts (pocket (Lines G f 1)) A 0 x y; rwa [cash_pocket,cash_pocket] at ht'
 refine ⟨hT.congr_of_eventuallyEq he,fun x y=>?_⟩; rw[(he.iteratedFDeriv ℝ 2).eq_of_nhds]; unfold R; rw [clm_h hf.dye hY hp x y,hL,hL,hm,hm,show fderiv ℝ A 0=0 from dyed_hold hf h]; rw [show iteratedFDeriv ℝ 2 (F ∘ input G f) 0 ![x,Tbody Y *ᵥ y]= iteratedFDeriv ℝ 2 A 0 ![Tbody Y *ᵥ y,x] from ?_]
 · change (_+_)+0=_+_; rw[add_zero, add_comm]
 rw[iteratedFDeriv_two_apply,iteratedFDeriv_two_apply]; exact hf.dye.isSymmSndFDerivAt_of_omega ..
end YM.Trace.Lamp
