import YM.TraceExtension.Det.Piper

/-!
# Project/extras alike. Pet bounds for beam and larch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}
    {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
    {k m n:ℕ}{α C D A:ℝ}{Y:Gal G f}
variable (o:Site f)
section peering
variable (F:Acr G f→X)
def snip (x:Link G f)(z:Link G f):= F ((bite G f).symm (x,z))
lemma soft_snip (h:ContDiffAt ℝ ω F 0): ∀ᶠ x:Link G f in 𝓝 0,
    ContDiffAt ℝ ω (snip F x) 0 ∧ fderiv ℝ (snip F x) 0= (fderiv ℝ F (takea G f x)) ∘L ((bite G f).symm.toContinuousLinearMap ∘L ContinuousLinearMap.inr ℝ _ _):=by
    filter_upwards [(show Tendsto (takea G f) (𝓝 0) (𝓝 0) from by simpa using (takea G f).continuous.tendsto 0).eventually (h.eventually (by simp))] with x hx
    let L:= ContinuousLinearMap.inr ℝ (Link G f) (Link G f)
    let P:= (bite G f).symm.toContinuousLinearMap
    let K(z:Link G f):= P (x,z)
    have h0: K 0=takea G f x:=rfl
    have ht: ContDiffAt ℝ ω K 0:=by unfold K; fun_prop
    have hK: HasFDerivAt K (P ∘L L) 0:= P.hasFDerivAt.comp 0 ((hasFDerivAt_const x (0:Link G f)).prodMk (hasFDerivAt_id _))
    have hf : ContDiffAt ℝ ω F (K 0):= h0.symm ▸ hx; exact ⟨hf.comp 0 ht, ( (hf.differentiableAt (by simp)).hasFDerivAt.comp _ hK).fderiv⟩
lemma soft_hx [CompleteSpace X] (h:ContDiffAt ℝ ω F 0): ∀ᶠ x:Link G f in 𝓝 0,∀ i j:Lines G f 1, iteratedFDeriv ℝ 2 (snip F x) 0 ![bolt i,bolt j]=fderiv ℝ (fun z=> fderiv ℝ F z (bolt (.inr j))) (takea G f x) (bolt (.inr i)):=by
    filter_upwards [(show Tendsto (takea G f) (𝓝 0) (𝓝 0) from by simpa using (takea G f).continuous.tendsto 0).eventually (h.eventually (by simp))] with x hx i j
    let L:= ContinuousLinearMap.inr ℝ (Link G f) (Link G f);let P:= (bite G f).symm.toContinuousLinearMap; let A:= P ∘L L; let V:= takea G f x
    have he : snip F x=(fun z=> F (V+z)) ∘ A:=by funext i; change F (P (x,i))=F (P (x,(0:Link G f))+P (0,i));rw[← map_add]; simp
    have hv(t): A (bolt t)=bolt (Sum.inr t):=by
       apply (bite G f).injective; change bite G f ((bite G f).symm ((0,_)))=_; rw [(bite G f).apply_symm_apply]; exact Prod.ext (bite_lr ..).symm (bite_r ..).symm
    rw[divided (h:=hx),he,wired A ?_,map_zero,iteratedFDeriv_comp_add_left,add_zero]; swap
    · rw [map_zero]; exact AnalyticAt.comp (x:=(0:Acr G f)) (g:=F) (f:=fun z=>V+z) (by rw [add_zero]; exact hx.analyticAt) (by fun_prop)
    congr 1; ext1 q; fin_cases q; exact hv _; exact hv _
lemma Pet.picked {F:Acr G f→X}(h:Pet (af G f) o F α C (m+1))(i:Lines G f 1): Pet Prod.fst o (fun z=> fderiv ℝ (snip F z) 0 (bolt i)) α (C*Decay α o i.1) m:=by
    refine ((h.halp (Sum.inr i)).compL (taken G f)).grows ?_
    filter_upwards [soft_snip F h.1] with x hx; simp only[Function.comp_apply,hx.2]; change _= fderiv ℝ F (takea G f _) ((bite G f).symm (0,bolt i)); congr 1; apply (bite G f).injective; rw [(bite G f).apply_symm_apply]; exact Prod.ext (bite_lr ..) (bite_r ..)
lemma Pet.prickle [CompleteSpace X] {F:Acr G f→X}(h:Pet (af G f) o F α C (m+2))(i j:Lines G f 1): Pet Prod.fst o (fun z=> iteratedFDeriv ℝ 2 (snip F z) 0 ![bolt i,bolt j]) α (C*Decay α o j.1*Decay α o i.1) m:= (((h.halp (Sum.inr j)).halp (Sum.inr i)).compL (taken G f)).grows (by filter_upwards [soft_hx F h.1] with x hx; exact (hx i j).symm)
end peering
abbrev WildM (G:Gauge)(f:Side)(r b:ℕ):=Link G f→ Matrix (Lines G f r) (Lines G f b) ℝ
def PetW {r b:ℕ}(V:WildM G f r b)(α C:ℝ)(m:ℕ): Prop:= ∀ i j, Pet Prod.fst o (fun z=> V z i j) α (C*Decay α o i.1*Decay α o j.1) m
lemma bockat (i:Lines G f n) : bolt i=(pocket _) i:=by
    ext a;by_cases e:i=a
    · simp [e,bolt]
    simp [bolt,Ne.symm e]
lemma beamer (G:Gauge)(m:ℕ): ∃ E:ℝ,0≤E ∧∀ f:Side,∀ (x:Site f)(F:Peat G f)(α C:ℝ),0≤α→0≤C → Pet Prod.fst x (F ∘ input G f) α C (m+2)→ PetW x (beamH F ∘ input G f) (α/(m+2+1:ℝ)) (E*C) m:=by
    obtain ⟨E,hE,h⟩:= cocoa_m (X:=ℝ) G (m+2); refine ⟨E,hE,fun f x F a C ha hC hf i j=>?_⟩
    have ht:=Pet.prickle (G:=G) x (h f x F a C hC ha hf) i j; simp only[Nat.cast_add,Nat.cast_ofNat,bockat] at ht
    rw[mul_right_comm _ (Decay _ _ _),mul_comm C] at ht
    refine ht.grows (F:=fun z=> iteratedFDeriv ℝ 2 (snip (F ∘ splitp G f) z) 0 ![(pocket _) i,(pocket _) j]) ?_
    refine Eventually.of_forall fun v=>?_
    simp only[Function.comp_apply,beam_p]; congr 2
lemma tidal_pay (h:Cloaked Y)(he:∀ i, Pet (af G f) o (fun z=> larch Y z i) α (C*Decay α o i.1) (m+1)): PetW o (tidal Y ∘ input G f) α C m:=by
    intro i j; let F(z:Acr G f):= larch Y z i
    refine (Pet.picked o (he i) j).grows ?_; let L:Link G f→L[ℝ] ℝ:= ContinuousLinearMap.proj i
    have ht:=tune_n h (input G f) (Army.powL (v:=id) contDiffAt_id) (input_zero _ _)
    filter_upwards [ht] with x hx
    let U:= input G f x; let K:=lyre Y U
    have hp: snip F x=L ∘ K:=by ext1 j; unfold F larch snip; simp[aleft,aright]; rfl
    change fderiv ℝ (snip F x) 0 _ = _; rw [hp,fderiv_comp _ L.differentiableAt ((show ContDiffAt ℝ ω K 0 from keep_l (tune_diff _ hx) 1).differentiableAt (by simp)), L.fderiv]
    rw [Function.comp_apply,tidal,bill_def,cash_pocket, bockat]; rfl
lemma refrain_pay (h:Cloaked Y)(he:∀ i,Pet (af G f) o (fun z=> larch Y z i) α (C*Decay α o i.1) (m+2))(b i j:Lines G f 1) : Pet Prod.fst o (fun z=> refrain Y (input G f z) i j b) α (C*Decay α o b.1*Decay α o j.1*Decay α o i.1) m:=by
    let F(z:Acr G f):=larch Y z b; let L : Link G f→L[ℝ] ℝ:= ContinuousLinearMap.proj b
    refine (Pet.prickle o (he b) i j).grows ?_
    filter_upwards [tune_n h (input G f) (Army.powL (v:=id) contDiffAt_id) (input_zero _ _)] with x hx
    let K:= lyre Y (input G f x); have hp: snip F x=L ∘ K:=by ext1 j; unfold F larch snip; simp[aleft,aright]; rfl
    change iteratedFDeriv ℝ 2 (snip F x) _ _=_; rw [hp,L.iteratedFDeriv_comp_left (show ContDiffAt ℝ ω K 0 from keep_l (tune_diff _ hx) _) le_top,bockat,bockat];rfl
lemma pet_lush (h:PetW o (tidal Y ∘ input G f) α C m)(ha:0 < α)(hp:0≤C): Pet Prod.fst o (lush Y ∘ input G f) α (C*(Fintype.card (Loc G 1))*countCost α) m:=by
    let F i(z:Link G f):= tidal Y (input G f z) i i
    have ht(i): Pet Prod.fst o (F i) α (C*Decay α o i.1) m:= (h i i).tilt (mul_le_of_le_one_right (mul_nonneg hp (decay_pos ..).le) (decay_le ha.le ..)) le_rfl le_rfl
    have hh: Beacon Prod.fst α m (fun z=> ∑ i:Lines G f 1,F i z) o 0 (∑ i:Lines G f 1,C*Decay α o i.1):= beacon_sum (fun i _=>(ht i).2) (fun i _=>(ht i).1)
    refine ⟨ContDiffAt.sum (f:=F) (fun i _=>(ht i).1),hh.mono ?_⟩
    rw[← mul_sum,mul_assoc];exact mul_le_mul_of_nonneg_left ((pay_gate G f|>.count _ ha o)) hp
end YM.Trace.Det
