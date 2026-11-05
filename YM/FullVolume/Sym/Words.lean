import YM.FullVolume.Sym.Snippet
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Jams
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {K : Teller G} {p a W U : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' Q : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi} {F : Tree.Forest S.ratio}
variable {P:BudgetPoint}
variable {v δ e b γ B η:ℝ} {n d:ℕ} {C:Tune H v δ}
/-!
# Recovery under BILL chosen *after ANY* weight
Essential to cumulative H01 after reset. Strong coefficient at labels.
-/
open FullVolume.Ray
section one
variable {v:ℝ}
set_option quotPrecheck false
local notation "X"=> (FullVolume.Ray.Rebar.smear v).range
local notation "Y"=> FullVolume.Ray.Rebar.spans v
abbrev groundUp (v:ℝ)(w:Rung): Rebar.spans v:=⟨Rebar.smear v w,(Rebar.smear v).range.le_topologicalClosure (LinearMap.mem_range_self ..)⟩
lemma thick (v:ℝ) : DenseRange (groundUp v) := by
  intro x; apply Metric.mem_closure_iff.2; intro ε he
  obtain ⟨k,hk,hp⟩:= Metric.mem_closure_iff.1 (show x.val∈ closure ((Rebar.smear v).range :Set Rebar.Wire) from x.property) ε he
  obtain ⟨i,rfl⟩:= hk; exact ⟨_,⟨i,rfl⟩,hp⟩
lemma stripes (hp:1<v) (w:Rung) : Stripe w v ‖groundUp v w‖:=by
  intro i
  have hh:(Rebar.smear v w) i= FullVolume.Ray.trace w (fun x=>(x/v)^i):= by
    unfold Rebar.smear FullVolume.Ray.trace; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,Rebar.fil hp]
  rw [← hh]; exact lp.norm_apply_le_norm (by simp) _ _
set_option maxHeartbeats 600000 in
set_option synthInstance.maxHeartbeats 100000 in
lemma snapshots (hp:1<v) {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]{f:sun→E}(h:Rebar v (phraseS f) B):∃ L : (Rebar.spans v) →L[ℝ] E,∀ w:Rung,L (groundUp v w)=mix w f:=by
  obtain ⟨L,hL,ht⟩:= Rebar.linear_snapshot h hp
  have hK : (X) ≤ (Y):=(X).le_topologicalClosure
  let q:(X)→ₗ[ℝ](Y):= Submodule.inclusion hK; have hu z: ‖q z‖≤1*‖z‖:= by rw [one_mul]; rfl
  let V:= q.mkContinuous 1 hu; have hz w: groundUp v w = V ((Rebar.smear v).rangeRestrict w):=rfl
  have hV:DenseRange V:= fun x=> closure_mono (show Set.range (groundUp v)⊆Set.range V from (by rintro i ⟨w,rfl⟩; exact ⟨_,(hz w).symm⟩)) ((thick v) x)
  exact ⟨ContinuousLinearMap.extend L V,fun w=> by rw [hz,ContinuousLinearMap.extend_eq L hV (show Isometry V from fun _ _=> rfl).isUniformInducing,ht,mix_made]⟩
noncomputable abbrev unitP (n:ℕ) (hp:1<v): (Rebar.spans v) := ⟨Rebar.single n, Rebar.speck hp n⟩
lemma assembles (hp:1<v) {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f:sun→E}(T : (Rebar.spans v) →L[ℝ] E)(ht:∀ w, T (groundUp v w)=mix w f) (x:sun): HasSum (fun i=>(x.val/v)^i • T (unitP i hp)) (f x):=by
  have hK : IsClosed ((Y) : Set Rebar.Wire):= (Rebar.smear v).range.isClosed_topologicalClosure; letI :CompleteSpace (Y):= hK.isComplete.completeSpace_coe
  let u(i:ℕ):= (x.val/v)^i • unitP i hp; have hx i:‖unitP i hp‖=1:= Rebar.points i
  have hh: Summable u:= by apply Summable.of_norm; unfold u; simp_rw [norm_smul, hx,mul_one,norm_pow]; exact summable_geometric_of_lt_one (norm_nonneg _) (Rebar.radius hp x)
  let w:= Finsupp.single x (1:ℝ)
  have h : ∑' i,u i=groundUp v w:=Subtype.ext (Eq.trans ((Y).subtypeL.hasSum hh.hasSum).tsum_eq.symm (Eq.symm (show (groundUp v w).val=Rebar.wire v x from Rebar.start v x)))
  have he: f x = T (∑' i,u i):=by rw [h,ht,← combo_eq,combo]; simp [w]
  rw [he]; exact (T.hasSum hh.hasSum).congr_fun (fun i=> by unfold u; rw [map_smul])
end one
section many
open Set
variable {F:sun→ℕ→ Config G c→ℝ} {C:ℕ→Support c} {q:ℕ}
def voted (f:sun→ℕ→ Config G c→ℝ)(C:ℕ→Support c)(q:ℕ)(e v b:ℝ): Prop:= ∀ w η, Stripe w v η→ ∃ k:ℕ→ℝ,Ac.Hit C q k e (η*b) ∧ ∀ i U, ‖mix w (fun x=> f x i U)‖ ≤ k i
variable (h:voted F C q e v b) (he:∀ i,(C i).Nonempty) (hs:1<v) (hb:0≤e)
include h he hs hb
lemma snapC : ∃ T:ℕ → Config G c → (Rebar.spans v) →L[ℝ] ℝ,∀ i U w,T i U (groundUp v w)=mix w (fun x=> F x i U):=by
   have hh (i:ℕ)(U:Config G c): Rebar v (phraseS (fun y=> F y i U)) b:= by
     have hw : 0≤b:= by
       have hu: Stripe 0 v 1:= fun _=> by simp [FullVolume.Ray.trace]
       obtain ⟨k,hk,-⟩:= h 0 1 hu; simpa only [one_mul] using budget_nonneg (hk 0)
     refine ⟨hs.le,hw,fun w η hv=>?_⟩; obtain ⟨k,hk,hL⟩:= h w η hv; have hl:= (norm_nonneg _).trans (hL i U); obtain ⟨x,hx⟩:= he i; have hp:= budget_single (hk x) i; rw [if_pos hx] at hp; rw [mix_made]; exact (hL i U).trans ((le_mul_of_one_le_right hl (Real.one_le_exp (mul_nonneg hb (Nat.cast_nonneg _)))).trans hp)
   choose T hT using fun i U=> snapshots hs (hh i U); exact ⟨T,hT⟩
lemma assetC (T:ℕ→ Config G c→ (Rebar.spans v)→L[ℝ] ℝ)(ht:∀ i U w,T i U (groundUp v w)=mix w (fun x=>F x i U)) (n:ℕ) : ∃ f:ℕ→ℝ, Ac.Hit C q f e b ∧ ∀ i U,‖T i U (unitP n hs)‖ ≤ f i:=by
   let u:= unitP n hs; have hv : ‖u‖=1:= Rebar.points n
   obtain ⟨φ,hφ,hy⟩:= mem_closure_iff_seq_limit.mp ((thick v) u)
   choose w hw using hφ; choose k hk hL using fun i=> h (w i) _ (stripes hs (w i))
   have h0 i t:0≤ k t i:= (norm_nonneg _).trans (hL t i 1)
   let a i := ‖φ i‖*b; have he' i:Ac.Hit C q (k i) e (a i):=by unfold a; rw [← hw i]; exact hk i
   have ha : Tendsto a atTop (𝓝 b):= by simpa only [hv,one_mul] using hy.norm.mul_const b
   obtain ⟨A,hA⟩ := ha.bddAbove_range; let B:= Set.Icc (0:ℝ) A; have hK t i:k t i∈ B:=by
     obtain ⟨x,hx⟩:= he i; have ht:= budget_single (he' t x) i; rw [if_pos hx] at ht; exact ⟨h0 i t, ((le_mul_of_one_le_right (h0 i t) (Real.one_le_exp (mul_nonneg hb (Nat.cast_nonneg _)))).trans ht).trans (hA (Set.mem_range_self _))⟩
   obtain ⟨f,hf,g,hg,H⟩:= (isCompact_univ_pi (fun _ : ℕ => show IsCompact B from isCompact_Icc)).tendsto_subseq (x:=k) (fun i z _=> hK i z) -- check
   have hx i:Tendsto (fun j=> k (g j) i) atTop (𝓝 (f i)):= tendsto_pi_nhds.mp H i
   refine ⟨f,fun i=>?_,fun i U=>?_⟩
   · refine budget_of_sum ?_ fun S=>?_
     · intro j; split; exact mul_nonneg ((hf _ (Set.mem_univ _)).1) (Real.exp_nonneg _); rfl
     let p (k:ℕ→ℝ) j:=if i∈C j then k j * Real.exp (e*coverNumber q (C j)) else 0
     apply le_of_tendsto_of_tendsto (g:=a∘g) _ (ha.comp hg.tendsto_atTop) (show ∀ᶠ j in atTop, ∑ i∈S,p (k (g j)) i≤ a (g j) from Eventually.of_forall fun j=> budget_sum (he' _ i) S)
     refine tendsto_finsetSum _ fun j _=>?_; by_cases ht:i∈C j
     · exact (show _ from (by unfold p; simp only [ht,if_true]; exact (hx j).mul_const _))
     simp only [p,ht,if_false]; exact tendsto_const_nhds
   refine le_of_tendsto_of_tendsto (f:=fun j=> ‖T i U (φ (g j))‖) ( ((T i U).continuous.continuousAt.tendsto.comp (hy.comp hg.tendsto_atTop)).norm) (hx i) (Eventually.of_forall fun j=>?_)
   dsimp only; rw [← hw (g j),ht]; exact hL (g j) i U
variable {r:ℝ}
lemma unions (hr:1≤r) (hV:r<v):league C q F e r ((1-r/v)⁻¹*b):=by
   obtain ⟨T,hT⟩:= snapC h he hs hb; choose f hf hX using assetC h he hs hb T hT
   let d:=r/v; have hd : 0<d:= div_pos (zero_lt_one.trans_le hr) (zero_lt_one.trans hs); have hp: d<1:= (div_lt_one (zero_lt_one.trans hs)).mpr hV
   have h0 n i:= (norm_nonneg _).trans (hX n i (1:Config G c)); have ha n i:f n i≤b:=by obtain ⟨x,hx⟩:= he i; have ht:= budget_single (hf n x) i; rw [if_pos hx] at ht; exact (le_mul_of_one_le_right (h0 n i) (Real.one_le_exp (mul_nonneg hb (Nat.cast_nonneg _)))).trans ht
   let p n i:= d^n*f n i; have hE n i :0≤p n i:= mul_nonneg (pow_nonneg hd.le _) (h0 _ _)
   let k i := ∑' n,p n i; have hv := (hasSum_geometric_of_norm_lt_one (ξ:=d) (by rw [Real.norm_of_nonneg hd.le]; exact hp)).mul_right b; have hw i:Summable (fun n=> p n i):= hv.summable.of_nonneg_of_le (fun n=> hE n i) (fun n=> mul_le_mul_of_nonneg_left (ha _ _) (pow_nonneg hd.le _))
   have hK n:Ac.Hit C q (p n) e (d^n*b):= hit_scale (pow_nonneg hd.le n) (hf n) -- ambiguous
   refine ⟨k,fun i=>?_,fun i U=> ⟨hr,(fun n=> d^n*T i U (unitP n hs)),?_,?_⟩⟩
   · let w (f:ℕ→ℝ) j:=if i∈ C j then f j*Real.exp (e*coverNumber q (C j)) else 0
     refine budget_of_sum (fun i=> ?_) fun s=>?_
     · split; exact mul_nonneg (tsum_nonneg fun n=>hE n _) (Real.exp_nonneg _); rfl
     have hx i' : w k i'= ∑' n,w (p n) i':= by unfold w k; split_ifs; rw [tsum_mul_right]; rw [tsum_zero]
     change ∑ j∈s,w k j≤ _; simp_rw [hx]; have he':∀ j,Summable (fun n=> w (p n) j) := fun j=> by unfold w; split_ifs; exact (hw j).mul_right _; exact summable_zero
     rw [← Summable.tsum_finsetSum (s:=s) (fun j _=> he' j)] -- signature
     exact (Summable.tsum_le_tsum (fun j=> budget_sum (hK j i) s) (summable_sum fun j _=> he' j) hv.summable).trans_eq hv.tsum_eq
   · exact budget_mono (show SumBudget (fun n=> p n i) (k i) from ⟨fun n=> hE n i,hw i,le_rfl⟩) (fun i=>norm_nonneg _) fun n=> by rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hd.le _)]; exact mul_le_mul_of_nonneg_left (hX n i U) (pow_nonneg hd.le _)
   intro t ht; let x:sun:=⟨t,ht⟩
   rw [show phraseS _ t=F x i U from phrased (fun t=>F t i U) x]; refine (assembles hs _ (hT i U) x).congr_fun (fun n=> ?_)
   dsimp only; rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_pow]; unfold x d; field_simp
end many
end YM.PhysicalNext.Repeat.Jams
