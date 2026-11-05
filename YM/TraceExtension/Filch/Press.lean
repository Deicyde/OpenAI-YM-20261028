import YM.TraceExtension.Filch.Brad
set_option autoImplicit false
set_option maxHeartbeats 180000
noncomputable section
namespace YM.Trace.Filch
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295.Cases Lamp
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{o:Site n}{r:ℕ}

variable (o r)
def lakesC (F:Peat G n): Peat G n:= fun U=>cloud (ballX F) o r U 0
def lakesY (Y:Gal G n):Gal G n:=fun U x =>cloud (bottom Y) o r U (bolt x)
variable {F:Peat G n}(h:F∈loom G n) {Y:Gal G n}(hY:Y∈rains G n)
private abbrev L(A:Link G n): Acr G n:= takea G n A
private abbrev P(o:Site n)(r:ℕ): Acr G n →L[ℝ] Acr G n := stone (landW o) r
private def f'(W:Config G n)(z:Link G n): Acr G n:= P o r (patio o 4 W z)
private abbrev fx:=ballX F
private abbrev fy:=bottom Y
private lemma same(o:Site n)(r:ℕ)(U:Config G n)(v w:Link G n): aleft G n (f' o r U v)=aleft G n (f' o r U w):=by
    ext1 i; change P o r _ (.inl i)=P o r _ (.inl i); rw [stone_at (landW o),stone_at (landW o)]; rfl
include h in
lemma cloudF_eq (U:Config G n)(v:Link G n): cloud (ballX F) o r U v=lakesC o r F U:=by
   unfold cloud; have hv a k:neap k (ballX F) 0 a=neap k (F ∘ input G n) 0 (aleft G n a):=by
       unfold neap; change _=_ ; rw[show ballX F=(F ∘ input G n) ∘ aleft G n from rfl,iter_lin_at (L:=aleft G n) ((map_zero (aleft G n)).symm ▸ (show Cleric _ from (show Cleric F∧_ from h).1).dye.of_le (m:=k) le_top),map_zero];rfl
   change choral 4 _ (f' o r U v)= choral 4 _ (f' o r U _); rw [reverberate,reverberate]; apply sum_congr rfl fun i _=>?_ ; rw [hv,hv,same o r U v 0]
private lemma tenor (U:Config G n):∃ L: Link G n→L[ℝ] Link G n,∀ v,L v=aright G n (f' o r U v):=by
    let L:= aright G n ∘L (P o r ∘L ((bite G n).symm.toContinuousLinearMap ∘L (ContinuousLinearMap.inr ℝ (Link G n) (Link G n) ∘L armor (march o U))))
    refine ⟨L,fun v=>?_⟩; ext1 i; change P o r ((bite G n).symm (0,_)) (.inr i)=f' o r U v (.inr i);rw[f',stone_at (landW o),patio,stone_at (landW o)]; rfl
include hY
private lemma forge (U: Config G n): ∃ L: Link G n→ₗ[ℝ]ℝ,∀ v: Link G n,cloud (bottom Y) o r U v = L v :=by
    obtain ⟨Lₛ,hL⟩:=tenor o r U
    let A:Link G n:=aleft G n (f' o r U 0)
    have he(v:Link G n)(t:ℝ): bottom Y (t • f' o r U v)=t • (dotB (Y (input G n (t • A))) (Lₛ v)):=by
        change Y (input G n (aleft G n (t • f' o r U v))) ⬝ᵥ _ = _
        rw[hL, map_smul]; change Y (input G n _) ⬝ᵥ aright G n (t • f' o r U v)=_; rw [map_smul,dotProduct_smul,same o r U v 0, fast_dot]
    let M: ℝ→ Link G n→L[ℝ] ℝ:= fun t=> t • ((dotB (Y (input G n (t • A)))) ∘L Lₛ)
    obtain ⟨hp,hy01⟩:=hY; change Cloaked Y at hp
    have hm:ContDiffAt ℝ ω M 0:=by
       have hv: ContDiffAt ℝ ω (fun t:ℝ=>Y (input G n (t • A))) 0:=by
          apply ContDiffAt.comp (g:=Y ∘ input G n) (f:=fun t:ℝ=>t • A) (0:ℝ)
          · rw[zero_smul]; exact hp.dye
          fun_prop
       exact contDiffAt_id.smul ((dotB.contDiff.contDiffAt.comp _ hv).clm_comp contDiffAt_const)
    refine ⟨(choral 4 M 1).toLinearMap,fun v=>?_⟩
    let B:ℝ→L[ℝ] Acr G n:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ..) (f' o r U v)
    let E: (Link G n→L[ℝ] ℝ)→L[ℝ] ℝ:= ContinuousLinearMap.apply ℝ ℝ v
    have hy:E ∘ M =ᶠ[𝓝 0] bottom Y ∘ B:=Eventually.of_forall fun t=>(he v t).symm
    have hz:= intoned B _ _ hy 4 (rain_read (Y:=Y) ⟨hp,by assumption⟩).2.2.1 1
    have hb:B 1=f' o r U v:=show (1:ℝ) • _=_ from one_smul ..
    rw[hb] at hz; exact hz.symm.trans (slice_tone E M 4 hm 1)
lemma liftY (U:Config G n)(v:Link G n): cloud (bottom Y) o r U v=(lakesY o r Y U) ⬝ᵥ v:=by
    obtain ⟨K,hK⟩:= forge o r hY U; rw [hK,dotProduct]; apply Eq.trans (b:=K (∑ i:Lines G n 1,v i • bolt i)); rotate_left
    · rw [map_sum]; refine sum_congr rfl (fun i _=> ?_); rw[map_smul]; unfold lakesY; rw[hK]; exact mul_comm ..
    apply congr_arg; ext1 i; simp [bolt,Finset.sum_apply, Pi.single_apply]
omit hY in
private lemma bead(o:Site n)(U V:Link G n)(h:∀ v:Link G n, U ⬝ᵥ v=V ⬝ᵥ v): U=V:=by ext1 i; simpa [dotProduct,bolt, Pi.single_apply] using h (bolt i)
omit hY in
private lemma widthV(W:Coats G n)(v:Link G n): armor W (armor W⁻¹ v)=v:=by
    apply edgeColor.injective; funext i; rw[armor_at,armor_at,← G.adjoint_mul,Pi.inv_apply,mul_inv_cancel,G.adjoint_one]
lemma Y_swept(U:Config G n)(W:Coats G n): lakesY o r Y (Lattice.gauge W U) = armor W (lakesY o r Y U):=by
    apply bead o; intro v
    obtain ⟨hp,ha,hc,-⟩:=rain_read hY; have hC: Cloaked Y:= (show Cloaked _ ∧ _ from hY).1
    let p:=armor W⁻¹ v
    rw [← show armor W p=v from widthV W v,loyS, ← liftY _ _ hY, ← liftY _ _ hY, cloud_r hc (bloomY hC)]
omit hY
variable {X : Type} [NormedAddCommGroup X][NormedSpace ℝ X]
lemma Y_warm(U:X→ Config G n)(x:X)(hp:Army U x)(Y:Gal G n) : ContDiffAt ℝ ω (lakesY o r Y ∘ U) x:= contDiffAt_pi.mpr fun i=>cloudful (bottom Y) _ _ U (fun _=>bolt i) _ hp contDiffAt_const
lemma J_warm(U:X→ Config G n)(x:X)(hp:Army U x)(F:Peat G n): ContDiffAt ℝ ω (lakesC o r F ∘ U) x:= cloudful _ _ _ U (fun _=>0) x hp contDiffAt_const
lemma J_take(F:Peat G n): LocalOn (feed o (r+1)) (lakesC o r F):=cloud_local (ballX F) o r 0
lemma Y_take (Y:Gal G n) : LocalOn (feed o (r+1)) (lakesY o r Y):=fun U V H=>funext fun v=> cloud_local (bottom Y) o r (bolt v) U V H
include hY in
lemma Y_dry (U:Config G n)(e:Edge (Site n))(h:¬separation o e.1≤r): edgeColor (lakesY o r Y U) e=0:=by
    have hs (i:G.ColorIndex): lakesY o r Y U (e.1,coord e.2,i)=0:=by
       let x:=e.1; let v:Link G n:= bolt (e.1,coord e.2,i)
       have hp(d:Edge (Site n))(hd:separation o d.1 ≤r):edgeColor v d=edgeColor (0:Link G n) d:=by
           have hx:e.1≠d.1:=fun he=>h (he.symm ▸ hd)
           ext j; change bolt (ι:=Lines G n 1) (e.1,coord e.2,i) (d.1,coord d.2,j)=(0:ℝ); simp[bolt,Pi.single_apply,hx,hx.symm]
       change cloud _ _ _ _ v=_; rw [cloudV _ _ _ _ 0 U hp, liftY o r hY, dotProduct_zero]
    ext i; exact hs i
private lemma nozero {A:Acr G n→ℝ}(h:ContDiffAt ℝ ω A 0)(ht:A 0=0)(hp:fderiv ℝ A 0=0): braid A (fun _=>0) 0 1:=by
    intro i hi; interval_cases i <;> ext1 v; simpa [iteratedFDeriv_zero_apply] using ht; simp [hp,iteratedFDeriv_one_apply]
include h in
lemma C_swept (U:Config G n)(W:Coats G n): lakesC o r F (Lattice.gauge W U)=lakesC o r F U:=by simpa only[lakesC,map_zero] using cloud_r ((loom_read h).2.2) (glowB (show Cleric _∧_ from h).1) o r U W 0
include h in
lemma pinch : ballX (lakesC o r F)= (choral 4 (ballX F) ∘ P o r) ∘ par o 4:=funext fun z=>(cloudF_eq o r h (input G n (bite G n z).1) (aright G n z)).symm
include hY in
lemma pinchY : bottom (lakesY o r Y)=(choral 4 (bottom Y) ∘ P o r) ∘ par o 4:=funext fun z=> (liftY o r hY (input G n (bite G n z).1) (aright G n z)).symm
lemma rain_null {A:Acr G n→ℝ}(h:ContDiffAt ℝ ω A 0)(hh:braid A (fun _=>0) 0 1) : braid ((choral 4 A ∘ P o r) ∘ par o 4) (fun _=>0) 0 1:=by
    let T:Acr G n→ Acr G n:= P o r ∘ par o 4; have hz:T 0=0:=by rw[show T 0=P o r (par o 4 0) from rfl,parZ,map_zero]
    have hx:= braid.trans (F:=choral 4 A) (Z:=fun _=>0) (show braid _ A 0 1 from fun i hi=> ((repitch h 4) i (by omega)).symm) hh
    exact wove (a:=0) (w:=T) (hz.symm ▸ hx) ((rhythm A 4).contDiffAt) contDiffAt_const ((P o r).contDiff.contDiffAt.comp _ (parW ..))
include h in
lemma lake_lo : lakesC o r F∈ loom G n:=by
    let A:=lakesC o r F
    have hd:ContDiffAt ℝ ω (A ∘ input G n) 0:= J_warm o r (input G n) 0 (Army.powL (v:=id) contDiffAt_id) F
    have hb: Cleric A:= ⟨hd, fun T _ _ _ _ V d u hv hy he hz => Eventually.of_forall fun x=> C_swept o r h _ _⟩
    obtain ⟨hp,hx,he⟩:=loom_read h
    have hP:braid (ballX A) (fun _=>0) 0 1:=by unfold A; rw[pinch o r h]; exact rain_null o r he (nozero he hp hx)
    refine ⟨hb,?_⟩; let T:=takea G n
    have hh:A ∘ input G n=ballX A ∘ T:= funext (fun x=> by simp [T,ballX])
    change braid (A ∘ input G n) _ _ _; rw [hh]
    have hc:ContDiffAt ℝ ω (ballX A) 0:=ContDiffAt.comp (g:=A ∘ input G n) (f:=aleft G n) _ ((map_zero (aleft G n)).symm ▸ hd) (aleft G n).contDiff.contDiffAt; exact wove (w:=T) ((map_zero T).symm ▸ hP) ((map_zero T).symm ▸ hc) contDiffAt_const T.contDiff.contDiffAt
include hY in
lemma lake_y: lakesY o r Y∈ rains G n:=by
   let A:=lakesY o r Y; have hc:Cloaked A:= ⟨Y_warm o r _ _ (Army.powL (v:=id) contDiffAt_id) Y, fun T _ _ _ _ V d u hv hy he hz=> Eventually.of_forall fun x=>Y_swept o r hY (V x) (d x)⟩
   obtain ⟨hp,hx,he,-⟩:= rain_read hY
   have hv:braid (bottom A) (fun _=>0) 0 1:=by unfold A;rw[pinchY o r hY]; exact rain_null o r he (nozero he hp hx)
   refine ⟨hc,?_⟩; apply bead o; intro v
   let u: Acr G n:= (bite G n).symm (0,v)
   have ha (t:ℝ): bottom A (t • u)=t • (A 1 ⬝ᵥ v):=by unfold bottom; rw[map_smul,show bite G n u=_ from (bite G n).apply_symm_apply _]; simp
   have ht : iteratedFDeriv ℝ 1 (bottom A) 0 ![u]=0:=by rw [hv 1 le_rfl];simp
   have hZ:ContDiffAt ℝ ω (bottom A) 0:=by rw [show bottom A=_ from pinchY o r hY]; exact (((rhythm ..).comp (P o r).contDiff).contDiffAt.comp _ (parW ..))
   change A 1 ⬝ᵥ v=0 ⬝ᵥ v; rw [zero_dotProduct]
   have hb:= Push.side (bottom A) (hZ.differentiableAt (by simp)) u
   simp only[iteratedFDeriv_one_apply,cons_val_zero] at ht
   rw [ht,funext ha] at hb; exact HasDerivAt.unique (by simpa using! (hasDerivAt_id (x:=(0:ℝ))).smul_const (A 1 ⬝ᵥ v)) hb
end YM.Trace.Filch
