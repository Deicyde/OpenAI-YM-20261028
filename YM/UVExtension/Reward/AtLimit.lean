import YM.UVExtension.Reward.Earth

/-! Every one-step limit reached, comparison modulo the vanishing waveform.
Coincidences at finite stage not assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Reward
open Lattice RG Supply Stationary Projection Precision Bloch Laurent Exterior Wilson Tree Filter Function Finset MenuView
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G} {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L} {D : Knobs a} {ε : ℝ} {m N :ℕ}

def EdgeLaw (V : Horizon a)(P : Knobs a)(Q:PostCost L)(Z:ChartRatio G)(ε:ℝ)(m:ℕ)(x y:Cube G)(b:ℝ) :=
    ∃ t:ℕ→ℕ,Tendsto t atTop atTop∧ ∃ f g:ℕ→ Cube G, ∃ α :ℕ→ℝ, ∃ z:ℕ→GainWire a m,(∀ i,Tried V P Q Z ε m (t i) (f i) (g i) (α i) (z i)) ∧ HLimit f x ∧ HLimit g y ∧ Tendsto α atTop (𝓝 b)

lemma common {x y y':Cube G}{b b'} (p:G.ColorIndex)(hZ:LocalRatio Z)(h:Buried V)(hv:Working D V P m)(hp:EdgeLaw V D Q Z ε m x y b)(he:EdgeLaw V D Q Z ε m x y' b'): y=y' ∧ b=b':=by
  obtain ⟨B,hB,hT⟩:=reading_line h hv
  obtain ⟨t,ht,f,g,α,z,ha,hx,hy,hα⟩:=hp; obtain ⟨w,hw,r,q,β,u,hr,hx',hy',hβ⟩:=he
  let F:=UVExtension.concat f r; let T:=UVExtension.concat t w
  let g':=UVExtension.concat g q; let a':=UVExtension.concat α β
  let u':=UVExtension.concat z u
  have H n: Tried V D Q Z ε m (T n) (F n) (g' n) (a' n) (u' n):=by
    apply split_all (p:=fun n=> Tried V D Q Z ε m (T n) (F n) (g' n) (a' n) (u' n)) _ _ n
    · intro i; simpa only [g',u',F,T,a',concat_castE] using! ha i
    intro i; simpa only [g',u',F,T,a',concat_castO] using! hr i
  have heT:Tendsto T atTop atTop:=tendsto_atTop.mpr fun i=> split_ev (p:=fun n=> i≤ T n) (by simpa only [T,concat_castE] using! ht.eventually (eventually_ge_atTop i)) (by simpa only [T,concat_castO] using! hw.eventually_ge_atTop i)
  obtain ⟨c,hc⟩:=hx.bound; obtain ⟨s,hs⟩:= hx'.bound
  have hf: HLimit F x:= by
    refine ⟨⟨max c s, split_ev (p:=fun i=> ‖F i‖ ≤ max c s) ?_ ?_⟩,fun i=> split_go ?_ ?_⟩
    · exact hc.mono (fun i hi => by rw [show F _=_ from concat_castE f r i]; exact le_trans hi (le_max_left ..))
    · exact hs.mono (fun i hi => by rw [show F _=_ from concat_castO f r i]; exact le_trans hi (le_max_right ..))
    · simpa only [F,comp_def,concat_castE] using! hx.hit i
    simpa only [F,comp_def,concat_castO] using! hx'.hit i
  obtain ⟨⟨v,Hv⟩,u,Hu⟩:=starters h heT hv hZ hf H
  have H' : Aligns (label D m) B (y,b) v u:=moving hv ht ha hT hy hα (by simpa only [T,F,u',comp_def,concat_castE] using! Hv.comp upE) (by simpa only [T,F,u',comp_def,concat_castE] using! Hu.comp upE)
  have hL:=Aligns.unicity H' (moving hv hw hr hT hy' hβ (by simpa only [T,F,u',comp_def,concat_castO] using! Hv.comp upO) (by simpa only [T,F,u',comp_def,concat_castO] using! Hu.comp upO)) p (organized hv) hB
  exact Prod.mk.inj hL

lemma collect_run {t:ℕ→ℕ}{f g:ℕ→Cube G}{u:ℕ→ℝ}{z:ℕ→ GainWire a m} (h:∀ i,Tried V D Q Z ε m (t i) (f i) (g i) (u i) (z i)):∃ s:ℕ→ℕ,Tendsto s atTop atTop ∧ ∃ x b,HLimit (g∘s) x∧ Tendsto (u∘s) atTop (𝓝 b):=by
  let r:= G.slopeConstant*Real.log (a.S.block m).val
  let p:= (a.params (m+1)).drift+ |r|
  have hz i:= driving_abs (u i) r _ (h i|>.run.bubble.earns)
  have hT : ∀ i,u i ∈ Metric.closedBall 0 p:=fun i=> Metric.mem_closedBall.mpr ((dist_zero_right _).trans_le (hz i))
  obtain ⟨v,hv,x,H⟩:=hs_subseq (I:=Crates G) (fun i=> (h i).run.toll)
  obtain ⟨b,hb,t,ht,hB⟩:= (isCompact_closedBall (0:ℝ) p).tendsto_subseq (x:=u∘v) (fun i=> hT _)
  exact ⟨v∘t,hv.tendsto_atTop.comp ht.tendsto_atTop,x,b,H.upon ht.tendsto_atTop,hB⟩
lemma step_contracted {x y u v: Cube G}{b b' : ℝ}(p:G.ColorIndex)(hz:LocalRatio Z)(hp:Ahead wavePulse ε)(h:Mints D P V Q Z ε)(hr:Buried V)(hx: x∈(label D (m+1)).valid)(hy: y∈ (label D (m+1)).valid)(hf: ‖x‖≤ε)(hg:‖y‖≤ε)(he:EdgeLaw V D Q Z ε m x u b)(hv:EdgeLaw V D Q Z ε m y v b'): ‖v-u‖≤ 1/2*‖y-x‖:=by
  let T i := m+1+i
  have ht:Tendsto T atTop atTop := tendsto_atTop_mono (fun i=> (show i≤ T i by unfold T; omega)) tendsto_id
  have hh i : m<T i:=by unfold T; omega
  have hb:ε ≤1:=by linarith [hp.small]
  have hP {x:Cube G}(hx:x ∈ (label D (m+1)).valid)(hf: ‖x‖≤ε)(i:ℕ):∃ v u z,Tried V D Q Z ε m (T i) x v u z:=by
    have hr:=(h.work (m+1)).paid _ (hh i) x hx (hf.trans hb)
    obtain ⟨v,a,ρ,h⟩:=h.pays _ _ (hh i) _ hr; exact ⟨v,a,ρ,hh i,hr,h⟩
  choose f g z h1 using hP hx hf; choose F G' Z' h2 using hP hy hg
  obtain ⟨s,hs,U,A,H,H'⟩:= collect_run h1
  obtain ⟨r,hr',V',A',Hy,Hx⟩:= collect_run (f:=fun _=> y) (t:=T∘s) (g:=F∘s) (u:=G'∘s) (z:=Z'∘s) fun i=>h2 _
  let n:=s∘r; have hu:=H.upon hr'
  have heT:=ht.comp (hs.comp hr'); let x' := fun _ : ℕ=> x; let y':=fun _:ℕ=> y
  have hf1:=common p hz hr (h.work m) he (b':=A) (y':=U) ⟨T∘n,heT,x',f∘n,g∘n,z∘n,fun i=> h1 _,HLimit.strong tendsto_const_nhds, hu,H'.comp hr'⟩
  have hf2:=common p hz hr (h.work m) hv (b':=A') (y':=V') ⟨T∘n,heT,y',F∘n,G'∘n,Z'∘n,fun i=>h2 _,HLimit.strong tendsto_const_nhds,Hy,Hx⟩
  rw [hf2.1,hf1.1, ← neg_add_eq_sub] -- better norm_le_of_tendsto
  have he := hu.linear (-1)
  have hh := he.add Hy
  rw [← neg_one_smul ℝ]; refine hh.norm_le (Eventually.of_forall fun i=>?_)
  change ‖(-1:ℝ) • f (n i)+F (n i)‖≤_
  rw [neg_one_smul,add_comm, ← sub_eq_add_neg]; exact paced p hz hp h hx hy hf hg (h1 _) (h2 _)
end YM.UVExtension.Reward
