import YM.TraceExtension.Det.Hub
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k l m n r:ℕ}{α a b τ A C D:ℝ}
variable (G f)
abbrev Poz:= Lines G f 1 ⊕ Lines G f 0 ⊕ Lines G f 1
abbrev Seas:=Perfect.Rays (Poz G f)
abbrev seau: Seas G f→L[ℝ] Link G f:= ContinuousLinearMap.pi (fun i=> ContinuousLinearMap.proj (Sum.inl i))
abbrev seag: Seas G f→L[ℝ] BaseSites G f:= ContinuousLinearMap.pi (fun i=>ContinuousLinearMap.proj (Sum.inr (Sum.inl i)))
abbrev seatx: Seas G f→L[ℝ] Link G f:= ContinuousLinearMap.pi (fun i=> ContinuousLinearMap.proj (Sum.inr (Sum.inr i)))
def cox(z:Seas G f):= lull (input G f (seau G f z)) (seag G f z) (seatx G f z)
abbrev dcox(i:Poz G f):= i.elim Prod.fst (Sum.elim Prod.fst Prod.fst)
abbrev sead: Seas G f→L[ℝ] (Link G f × (BaseSites G f× Link G f)):= (seau G f).prod ((seag G f).prod (seatx G f))
def capix: (Link G f×(BaseSites G f × Link G f)) →L[ℝ] Seas G f:=
    ContinuousLinearMap.pi fun i:Poz G f=> i.elim (fun i=> ContinuousLinearMap.proj i ∘L ContinuousLinearMap.fst ..) (Sum.elim (fun j=> ContinuousLinearMap.proj j ∘L (ContinuousLinearMap.fst .. ∘L ContinuousLinearMap.snd ..)) (fun j=> ContinuousLinearMap.proj j ∘L (ContinuousLinearMap.snd .. ∘L ContinuousLinearMap.snd ..)))
abbrev capu: Link G f→L[ℝ] Seas G f:= capix G f ∘L ContinuousLinearMap.inl ..
abbrev capt: (BaseSites G f × Link G f)→L[ℝ] Seas G f:= capix G f ∘L ContinuousLinearMap.inr ..
lemma bead (p): sead G f (capix G f p)=p:=by ext i <;> rfl
lemma butt_u (v:Lines G f 1): capu G f (bolt v)=bolt (.inl v):=by
    ext1 i
    rcases i with i|i|i
    · change bolt v i=bolt (ι:=Poz G f) (.inl v) (.inl i); simp [bolt,Pi.single_apply]
    · change 0=bolt (ι:=Poz G f) (.inl v) (.inr (.inl i)); simp [bolt]
    change 0=bolt (ι:=Poz G f) (.inl v) (.inr (.inr i));simp[bolt]
lemma butt_g (v:Lines G f 0): capt G f (bolt v,0)= bolt (.inr (.inl v)):=by
    ext1 i; rcases i with i|i|i
    · change 0=bolt (ι:=Poz G f) _ (.inl i); simp [bolt]
    · change bolt v i=bolt (ι:=Poz G f) _ (.inr (.inl i)); simp [bolt,Pi.single_apply]
    change 0=bolt (ι:=Poz G f) _ (.inr (.inr i));simp [bolt]
lemma butt_t (v:Lines G f 1): capt G f (0,bolt v)=bolt (.inr (.inr v)):=by
    ext1 i; rcases i with i|i|i
    · change 0=bolt (ι:=Poz G f) _ (.inl i);simp [bolt]
    · change 0=bolt (ι:=Poz G f) _ (.inr (.inl i));simp [bolt]
    change bolt v i= bolt (ι:=Poz G f) _ (.inr (.inr i));simp [bolt,Pi.single_apply]
variable {G f}
abbrev anthem (G:Gauge):= G.Color × G.Color × G.Color × G.Color
abbrev flute (a:anthem G):=
    G.plog (G.mat (G.lieExp a.1*((G.lieExp a.2.2.1)*(G.lieExp a.2.2.2))*(G.lieExp a.2.1)⁻¹*(G.lieExp a.2.2.2)⁻¹))
def jugw (e:Edge (Site f))(z:Seas G f): anthem G:= (gaugeColor (seag G f z) e.1,gaugeColor (seag G f z) (e.1+step e.2),edgeColor (seatx G f z) e,edgeColor (seau G f z) e)
lemma gong (e:Edge (Site f))(z:Seas G f): edgeColor (cox G f z) e=flute (jugw e z):=by
    unfold cox lull;rw [show edgeColor (content _) e=_ from content_at _ e.1 e.2]; unfold lyric Lattice.gauge; simp only [Pi.mul_apply,Pi.inv_apply,switch_color, input_color];rfl
lemma gongK (G:Gauge): ContDiffAt ℝ ω (flute (G:=G)) 0:=by
    have h (f:anthem G→ G.Color)(hf:f 0=0)(hd:ContDiffAt ℝ ω f 0): ContDiffAt ℝ ω (fun z=> G.mat (G.lieExp (f z))) 0 ∧ ContDiffAt ℝ ω (fun z=> G.mat ((G.lieExp (f z))⁻¹)) 0:=by
       have he: ContDiffAt ℝ ω (fun z=> G.mat (G.lieExp (f z))) 0:=ContDiffAt.comp (g:=fun x=> G.mat (G.lieExp x)) (f:=f) 0 (hf.symm ▸ catexp G) hd; exact ⟨he,(show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ he⟩
    unfold flute; simp_rw [G.mat_mul]; apply G.plog_diff.comp_of_eq
    · have h1:= h Prod.fst rfl contDiffAt_fst; have h2:= h (fun z:anthem G=>z.2.1) rfl (by fun_prop); have h3:= h (fun z=>z.2.2.1) rfl (by fun_prop); have h4:= h (fun z=>z.2.2.2) rfl (by fun_prop); exact ((h1.1.mul (h3.1.mul h4.1)).mul h2.2).mul h4.2
    · simp
    change G.mat (G.lieExp 0)*(G.mat (G.lieExp 0)*G.mat (G.lieExp 0))*G.mat ((G.lieExp 0)⁻¹)* G.mat ((G.lieExp 0)⁻¹)=1; simp [G.mat_lieExp_zero]
lemma portCost (G:Gauge) (n:ℕ):∃ A,0≤A ∧ ∀ f (e:Edge (Site f)), Allows n (jugw (G:=G) e) 0 A:=by
    let L: (G.ColorIndex→ℝ)→L[ℝ] G.Color:= (WithLp.linearEquiv 2 ℝ _).symm.toContinuousLinearMap
    refine ⟨‖L‖*1,by positivity,fun f e=>?_⟩
    have hx {V:Seas G f→ G.Color}{k:G.ColorIndex→Poz G f}(h:∀ z i,V z i=z (k i)): Allows n V 0 (‖L‖*1):=by
       let p:=(fun z:Seas G f=>fun i:G.ColorIndex=> z (k i)); rw[show V=(fun z=>L (p z)) from funext (fun x=>by ext i; exact h x i)]
       apply (Allows.linear (f:=p) L _ le_rfl); exact allows_pi zero_le_one (fun i=> by
           let T:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _: Poz G f=>ℝ) (k i)
           exact allows_linear (L:=T) (T.opNorm_le_bound zero_le_one (fun x=>by rw [one_mul];exact norm_le_pi_norm x _)) (by rw [map_zero,norm_zero];norm_num))
    apply Allows.pair ?_ (Allows.pair ?_ (Allows.pair ?_ ?_))
    · apply hx (k:=fun i=>Sum.inr (Sum.inl (e.1,vac,i))); intros;rfl
    · apply hx (k:=fun i=>Sum.inr (Sum.inl (e.1+step e.2,vac,i)));intros;rfl
    · apply hx (k:=fun i=>Sum.inr (Sum.inr (e.1,coord e.2,i)));intros;rfl
    apply hx (k:=fun i=>Sum.inl (e.1,coord e.2,i));intros;rfl
lemma cox_jet (G:Gauge)(k:ℕ)(a:ℝ)(ha:0≤a):∃ A, 0≤A∧∀ f (i:Lines G f 1), Pet (dcox G f) i.1 (fun z=> cox G f z i) a A k:=by
    obtain ⟨C,hC,h⟩:=exists_allows (f:=flute (G:=G)) (s:={(0:anthem G)}) isCompact_singleton (fun x hx=> hx.symm ▸ gongK G) k
    obtain ⟨D,hD,hx⟩:= portCost G k
    let L(x:G.ColorIndex): G.Color→L[ℝ]ℝ:= EuclideanSpace.proj x; let α:= ∑ i,‖L i‖; let P:=α*composeCost k C D
    refine ⟨P*Real.exp (a*k),by unfold P α composeCost; positivity,fun f ⟨i,r,b⟩=>?_⟩
    obtain ⟨p,rfl⟩:= axisEquiv.surjective r;let e:Edge (Site f):=(i,p)
    let V:Seas G f→anthem G:=jugw e
    have he: (fun z=>cox G f z (i,axisEquiv p,b))=fun z=> L b (flute (V z)):=funext (fun z=> congr_arg (L b) (gong e z));rw [he]
    have hV: V 0=0:=by unfold V jugw; simp only [map_zero,Pi.zero_apply]; rfl
    have hp:=Allows.linear (L b) ((h (V 0) (Set.mem_singleton_iff.mpr hV)).comp (hx f e)) (single_le_sum (fun i _=>norm_nonneg (L i)) (mem_univ b))
    have ht: Requests Set.univ V (dcox G f) i 1:=by
       intro p' _ q' _ ht
       refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
       · ext k; exact ht (.inr (.inl (i,vac,k))) (show separation i i≤1 by simp)
       · ext k; refine ht (.inr (.inl (i+step p,vac,k))) ?_; change separation i (i+step p)≤1; rw [separation_comm,separation, add_comm i,add_sub_cancel_right]; exact pdist_step p
       · ext k; exact ht (.inr (.inr (i,coord p,k))) (show separation i i≤1 by simp)
       ext k; exact ht (.inl (i,coord p,k)) (show separation i i≤1 by simp)
    have hv: Requests Set.univ (fun z=>L b (flute (V z))) (dcox G f) i 1:= fun u hu v hv h=> congr_arg (fun z:anthem G=>L b (flute z)) (ht u hu v hv h)
    refine ⟨hp.analytic,?_⟩; have hh:=hp.beacon hv univ_mem ha; rw[Nat.mul_one] at hh;exact hh
lemma jug_ask {V: BaseSites G f→ Link G f → Link G f}(i:BaseSites G f)(k:Link G f)(h:ContDiffAt ℝ ω (uncurry V) 0): fderiv ℝ (fun z=> fderiv ℝ (fun x=> V x z) 0 i) 0 k=iteratedFDeriv ℝ 2 (uncurry V) 0 ![((0:BaseSites G f),k),(i,0)]:=by
    let F(y):=fderiv ℝ (uncurry V) y (i,0)
    have he : (fun z=> fderiv ℝ (fun x=> V x z) 0 i)=ᶠ[𝓝 0] (fun z=> F (0,z)):=by
       filter_upwards [(show Tendsto (fun z:Link G f=> ((0:BaseSites G f),z)) (𝓝 0) (𝓝 0) from tendsto_const_nhds.prodMk_nhds tendsto_id).eventually (h.eventually (by simp))] with z hz;exact d_l hz i
    let K:=ContinuousLinearMap.inr ℝ (BaseSites G f) (Link G f)
    have ht : ContDiffAt ℝ ω F 0:= (h.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const
    rw [he.fderiv_eq,show (fun z=> F (0,z))=F ∘ K from rfl,fderiv_comp 0 (by rw[map_zero];exact ht.differentiableAt (by simp)) K.differentiableAt,map_zero,K.fderiv];exact divided (0,k) (i,0) h
lemma seatKey (i:Lines G f 1) (x:Link G f) (z:BaseSites G f × Link G f): cox G f (capix G f (x,z)) i=(lull (input G f x) z.1 z.2) i:=by
    have hz:=bead G f (x,z); let F:=capix G f (x,z); change lull (input G f (seau G f F)) (seag G f F) (seatx G f F) i = _; rw [show seau G f F=x from congr_arg Prod.fst hz, show seag G f F=z.1 from congr_arg Prod.fst (congr_arg Prod.snd hz), show seatx G f F=z.2 from congr_arg Prod.snd (congr_arg Prod.snd hz)]
lemma koel (i:Lines G f 1) (x:Link G f) (z:BaseSites G f × Link G f): cox G f (capu G f x+capt G f z) i=(lull (input G f x) z.1 z.2) i:=by
    rw [← seatKey i x z]; rw [show capu G f x+capt G f z=capix G f (x,z) from by change capix G f (x,0)+capix G f (0,z)=_; rw[← map_add]; simp]
lemma koan_m (k:Lines G f 1)(h:ContDiffAt ℝ ω (fun z=> cox G f z k) 0)(i:Lines G f 1)(j:Lines G f 0):
    ∀ᶠ z in 𝓝 (0: Link G f),
      mail (input G f z) k j=fderiv ℝ (fun z=>cox G f z k) (capu G f z) (bolt (Sum.inr (.inl j))) ∧
      jeps (input G f z) i j k=fderiv ℝ (fun v=> fderiv ℝ (fun z=>cox G f z k) v (bolt (Sum.inr (.inl j)))) (capu G f z) (bolt (Sum.inr (.inr i))):=by
    let V:=(capu G f)
    filter_upwards [(show Tendsto V (𝓝 0) (𝓝 0) from by simpa using V.continuous.tendsto 0).eventually (h.eventually (by simp))] with x hx
    let L:=capt G f; let U:=input G f x; let N:Link G f→L[ℝ]ℝ:= ContinuousLinearMap.proj k; let A(v:Seas G f):= cox G f v k; let P:=fun z: Seas G f=>A (V x+z)
    let S:=uncurry (lull U); have hS: ContDiffAt ℝ ω S 0:= lull_analytic U
    have hP:ContDiffAt ℝ ω P 0:= ContDiffAt.comp (g:=A) (f:=fun z=> V x+z) 0 (by rw[add_zero]; exact hx) (by fun_prop)
    have hp: N ∘ S=P∘ L:=funext (fun i=> (koel k x i).symm)
    constructor
    · rw [mail,bill_def,cash_pocket, ← bockat,← lull_home]
      rw [← butt_g]
      have hx': fderiv ℝ P 0=fderiv ℝ A (V x):=by unfold P; rw[fderiv_comp_add_left]; simp
      let Ut (u):= lull U u 0
      change N (fderiv ℝ Ut 0 (bolt j))=fderiv ℝ A (V x) (L (bolt j,0)); rw [d_l (F:=lull U),← hx']
      · have he:= congr_arg (fun t=> fderiv ℝ t 0) hp; rw[fderiv_comp 0 N.differentiableAt (hS.differentiableAt (by simp)), fderiv_comp 0 _ L.differentiableAt,map_zero,N.fderiv,L.fderiv] at he; exact congr($(he) (bolt j,0)); rw [map_zero];exact hP.differentiableAt (by simp)
      exact hS
    rw [divided _ _ hx]
    change N (jukebox U ((pocket _) i) ((pocket _) j))=_
    rw [← bockat,← bockat, jukebox, show fderiv ℝ (juke U (bolt j)) 0 (bolt i) =_ from jug_ask (V:=lull U) (bolt j) (bolt i) hS]
    let q:=( ![((0:BaseSites G f),bolt i),(bolt j,(0:Link G f))] : Fin 2→ BaseSites G f × Link G f)
    change N (iteratedFDeriv ℝ 2 S 0 q)=_
    rw [show N (iteratedFDeriv ℝ 2 S 0 q)=iteratedFDeriv ℝ 2 (N ∘ S) 0 q from congr($((N.iteratedFDeriv_comp_left hS (by exact le_top)).symm) q),hp,wired L (by rw[map_zero]; exact hP.analyticAt),map_zero]
    unfold P; rw [iteratedFDeriv_comp_add_left,add_zero]; apply congr_arg; ext1 b; fin_cases b; exact butt_t ..; exact butt_g ..
lemma mail_p (G:Gauge)(n:ℕ)(a:ℝ)(ha:0≤a):∃ A,0≤A ∧∀ f, Park (mail ∘ input G f) a A n:=by
    obtain ⟨A,hA,h⟩:=cox_jet G (n+1) a ha; refine ⟨A,hA,fun f i j=>?_⟩
    refine (((h f i).halp (.inr (.inl j))).compL (butt_u G f)).grows ?_
    filter_upwards[koan_m i (h f i |>.1) i j] with x hx; exact hx.1.symm
lemma jolt_p (G:Gauge)(n:ℕ)(a:ℝ)(ha:0≤a):∃ A, 0≤ A ∧∀ f:Side,∀ (i j)(k:Lines G f 1), Pet Prod.fst k.1 (fun z=> jeps (input G f z) i j k) a (A*Decay a k.1 j.1 * Decay a k.1 i.1) n:=by
    obtain ⟨A,hA,h⟩:=cox_jet G (n+2) a ha; refine ⟨A,hA,fun f i j k=>?_⟩
    refine ((((h f k).halp (.inr (.inl j))).halp (.inr (.inr i))).compL (butt_u G f)).grows ?_; filter_upwards[koan_m k (h f k |>.1) i j] with x hx; exact hx.2.symm
end YM.Trace.Det
