import YM.FullVolume.Glide.Duty
/-! One-step norms & betas. On Common orbit, not required balanced. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lark.Glide
open Function Filter Set MeasureTheory Lattice RG Pressure RG.Shoot Wilson Precision RG.Supply Input Org
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Song Geo
open ConnectedActivityE6
open Push.PriceCompiler Further.StrongStartup UniformSpace
open WilsonStartup Progress.DirectedRecipe Time UVNext.CouplingReset Roof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f:Side}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A} {p m N n:ℕ}
open Muse Pass FullVolume.Urns FullVolume.Shadow FullVolume.Amp
variable {t ξ w d q:ℝ} {L:Lyrics R t t}
    (Y:Plato L q w d ξ)(O:Ops L N p)
-- layout norm at all periods does not forget Reads; val if proof.
local notation "Ω"=> A.B.a.clock.hatBeta
local notation "B"=> A.B.a
local notation "K"=> A.B.kin
namespace Window
-- complete.Lim criteria. Arbitrary sequence mixed implies full. no Ops definitions needed
lemma held {X:Type}[PseudoMetricSpace X][CompleteSpace X]{s:ℕ→X}(h:∀ u v:ℕ→ℕ,Tendsto u atTop atTop→ Tendsto v atTop atTop→ Tendsto (fun i=>dist (s (u i)) (s (v i))) atTop (𝓝 0)): ∃ x,Tendsto s atTop (𝓝 x):=by
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.mpr ?_); intro ε he; by_contra! hp
    choose f hf g hg H using hp; obtain ⟨i,hi⟩:= ((h f g (tendsto_atTop_mono (f:=id) hf tendsto_id) (tendsto_atTop_mono (f:=id) hg tendsto_id)).eventually (gt_mem_nhds he)).exists; exact (H i).not_gt hi
lemma wait {X:Type}[NormedAddCommGroup X][CompleteSpace X][NormedSpace ℝ X]{s t:ℕ→ X}(h:∀ u v:ℕ→ℕ,Tendsto u atTop atTop→Tendsto v atTop atTop→ Tendsto (fun n=> s (u n)-t (v n)) atTop (𝓝 0)): Glints atTop s t:=by
    have he:=h id id tendsto_id tendsto_id
    obtain ⟨x,hx⟩:= held (s:=s) fun u v hu hv=> by
         have hh: Tendsto (fun i=> s (u i)-s (v i)) atTop (𝓝 0):= (sub_self (0:X) ▸ ((h u v hu hv).sub (he.comp hv))).congr' (Eventually.of_forall fun i=>by dsimp only [Function.comp_def,id]; abel)
         simpa only [dist_eq_norm,norm_zero] using hh.norm
    exact Glints.time ⟨_,hx,hx⟩ he
section bill
set_option quotPrecheck false
variable {u u':ℕ→ℕ}{Q:∀ n,Ops L (u n) p}{Q':∀ n,Ops L (u' n) p}
variable (h:Stationary.Artes.Cadre A.post A.B.kin)(hg:Next.Free.Amplify A.B.M)(ht:Jams.Wild R.shape A.delay)
    {M:∀ n,m < u n}{K':∀ n,m<u' n} {P:∀ n,wish (Q n) m (M n)} {T:∀ n,wish (Q' n) m (K' n)}
    (hp:∀ n, mild (A.B.a.clock.hatBeta (m+1)) (P n).1 ∧ ‖(P n).2‖ ≤ 1/8)(hk:∀ n,mild (A.B.a.clock.hatBeta (m+1)) (T n).1 ∧ ‖(T n).2‖ ≤ 1/8)
    (hu:Tendsto u atTop atTop)(hv:Tendsto u' atTop atTop)
    (hA:Glints atTop (fun i=>(P i).1) (fun i=>(T i).1))(hE:Glints atTop (fun i=> room (Q i) (P i).2) (fun i=> room (Q' i) (T i).2))
include h hg ht hp hk hu hv hA hE Y
local notation "c₀"=>fun i=> offer (Q i) (M i) (P i)
local notation "c₁"=>fun i=> offer (Q' i) (K' i) (T i)
local notation "K₀"=> fun i=>L.prim (u i) m p (M i)
local notation "K₁"=>fun i=>L.prim (u' i) m p (K' i)
local notation "X'"=> fun i=> (Pass.invitation (K₀ i) (P i)).val
local notation "Y'"=> fun i=> (Pass.invitation (K₁ i) (T i)).val
omit h hg ht hp hk hu hv hA hE Y in
private lemma passers {S:Type}[SeminormedAddCommGroup S]{f g:ℕ→ S}(h:Glints atTop (fun n=>((f n):Completion S)) (fun n=> ((g n):Completion S))): CauchySeq f∧ CauchySeq g∧Tendsto (fun n=> f n-g n) atTop (𝓝 0):=by
   obtain ⟨x,hx,hu⟩:=h; constructor
   · exact Metric.cauchySeq_iff.mpr (Metric.cauchySeq_iff.mp hx.cauchySeq|> fun h i hi=>by simpa only [Completion.dist_eq] using h i hi)
   constructor
   · exact Metric.cauchySeq_iff.mpr (Metric.cauchySeq_iff.mp hu.cauchySeq|> fun h i hi=>by simpa only [Completion.dist_eq] using h i hi)
   refine Metric.tendsto_nhds.mpr fun i hi=>?_ ; have hg:dist x x < i:= by rw [dist_self]; exact hi
   filter_upwards [(hx.dist hu).eventually (gt_mem_nhds hg)] with j hj; rw [dist_zero_right]; have he:dist (f j) (g j)< i:= ((Completion.dist_eq _ _).symm.trans_lt hj); simpa only [dist_eq_norm] using he
set_option maxHeartbeats 600000 in
lemma taxes : Tendsto (fun i=> room (Q i) (c₀ i)- room (Q' i) (c₁ i)) atTop (𝓝 0) ∧ Tendsto (fun i=>costP (Q i) (M i) (P i)-costP (Q' i) (K' i) (T i)) atTop (𝓝 0):=by
    have hx := fun i=> Window.filled Y (Q i) (P i) (hp i).1 (hp i).2; have he:=fun i=> Window.filled Y (Q' i) (T i) (hk i).1 (hk i).2
    let f:=fromLambda (Ω (m+1)); have hh:Continuous f:=by unfold f fromLambda; fun_prop
    have hP:Glints atTop (fun n=> (X' n).val.beta) (fun n=>(Y' n).val.beta):= (hA.bin (Q:=f) (fun _ _=> hh.continuousAt)).carve (Eventually.of_forall fun i=>(hx i).1.symm) (Eventually.of_forall fun i=>(he i).1.symm)
    obtain ⟨hr,hH,hκ⟩:= passers (f:=fun i=> (P i).2.val) (g:=fun i=> (T i).2.val) hE
    have hw n: (K₀ n|>.moment (X' n)).activities=(c₀ n).val.proper:= (chooseR (K₀ n) (Q n|>.walks m (M n)) (Pass.invitation (K₀ n) (P n))).property.symm
    have hw' n:(K₁ n|>.moment (Y' n)).activities=(c₁ n).val.proper:=(chooseR (K₁ n) (Q' n|>.walks m (K' n)) (Pass.invitation (K₁ n) (T n))).property.symm
    obtain ⟨ht,hZ⟩:=Pith.shall Y.SimpleR h hg hu hv K₀ K₁ X' Y' (fun i=>(P i).2.val) (fun i=>(T i).2.val) (fun i=>(c₀ i).val) (fun i=>(c₁ i).val) ht (fun i=>(hx i).2) (fun i=>(he i).2) hw hw' hP hr hH hκ
    constructor
    · refine Metric.tendsto_nhds.mpr fun i hi=>?_ ; filter_upwards [(Metric.tendsto_nhds.mp hZ i hi)] with n hn
      rw [dist_zero_right,←dist_eq_norm]; exact lt_of_eq_of_lt (Completion.dist_eq ((c₀ n).val: Show (stageP B m p)) ((c₁ n).val: Show (stageP B m p))) (by rw [dist_eq_norm]; exact lt_of_eq_of_lt (dist_zero_right _).symm hn)
    have hv := (ht.sub hP.shrank).sub ((landhold h hu hv (m:=m)).shrank); simp only [sub_zero] at hv; refine hv.congr' (Eventually.of_forall fun i=> ?_); dsimp only; unfold costP drum Pass.Delta; ring
lemma eternity : Glints atTop (fun i=>room (Q i) (c₀ i)) (fun i=>room (Q' i) (c₁ i)) ∧ Glints atTop (fun i=> costP (Q i) (M i) (P i)) (fun i=>costP (Q' i) (K' i) (T i)):=by
    have hh (f g:ℕ→ℕ)(hf:Tendsto f atTop atTop)(he:Tendsto g atTop atTop) := taxes Y h hg ht (u:=u∘f) (u':=u'∘g) (Q:=fun i=> Q (f i)) (Q':=fun i=> Q' (g i)) (M:=fun i=>M (f i)) (K':=fun i=>K' (g i)) (P:=fun i=>P (f i)) (T:=fun i=>T (g i)) (fun i=>hp _) (fun i=>hk _) (hu.comp hf) (hv.comp he) (glitters hA hf he) (glitters hE hf he)
    exact ⟨wait (fun _ _ hx hv=>(hh _ _ hx hv).1),wait (fun _ _ hx hv=> (hh _ _ hx hv).2)⟩
end bill
end Window
end YM.PhysicalNext.Repeat.Lark.Glide
