import YM.FullVolume.Fields.Pond
/-! Convergence and budget at a period (ANY local probes) for all labelling banks. Upper hull uniform even at changing mask.Geometry. Need not assume continuity. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Retreat
open Function Filter Set Finset MeasureTheory Metric Lattice Wilson RG Source Push Marker Extra.Histories Ac Bid Local
open Planned.GuardedAtom MergeProof MergeProof.Accent MergeProof.Menu Motion Extra.Multi
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {X Y Z : Type} [SeminormedAddCommGroup Y] [SeminormedAddCommGroup Z]
structure Confluence (f:ℕ→X→Y) : Prop where
   stretch : ∃ b:ℝ, ∀ᶠ i in atTop, ∀ x, ‖f i x‖≤ b
   trend (t:ℝ)(ht:0<t) :∃ N:ℕ,∀ n≥ N,∀ m≥N,∀ i, dist (f n i) (f m i)≤t
variable {f g:ℕ→ X→Y}{t:ℕ→X→Z}
lemma upperD (x y:Y): ‖x‖ ≤ ‖y‖+dist x y:=(dist_zero_right x).symm.trans_le ((dist_triangle x y 0).trans_eq (by rw [dist_zero_right,add_comm]))
lemma by_measure {s:X→Y}(hn:∃ x:ℝ,∀ i,‖s i‖ ≤ x)(h:∀ y>0,∀ᶠ n in atTop,∀ i,dist (s i) (f n i) ≤ y): Confluence f:=by
    obtain ⟨x,hx⟩:= hn; refine ⟨⟨x+1,(h _ zero_lt_one).mono (fun n hn i=> ?_)⟩,fun t ht=> ?_⟩
    · have hp:= hn i; rw [dist_comm] at hp; linarith only [upperD (f n i) (s i),hp,hx i]
    obtain ⟨N,hN⟩:= eventually_atTop.mp (h _ (half_pos ht)); refine ⟨N,fun n h m he i=>?_⟩; have hp:=hN n h i; rw [dist_comm] at hp; exact (dist_triangle ..).trans ((add_le_add hp (hN m he i)).trans_eq (add_halves _))
lemma constantP {s:X→Y}(b:ℝ)(hp:∀ x, ‖s x‖≤ b): Confluence fun _:ℕ=> s:= by apply by_measure (s:=s) ⟨b,hp⟩; intro c hc; exact Eventually.of_forall fun _ i=>(dist_self ..|>.trans_le hc.le)
namespace Confluence
lemma persist (h:Confluence f)(hx:f=ᶠ[atTop] g): Confluence g:=by
    obtain ⟨b,hB⟩:=h.stretch; obtain ⟨k,hk⟩:= eventually_atTop.mp hx
    refine ⟨⟨b,(hx.and hB).mono fun i hi=> hi.1 ▸ hi.2⟩,fun t ht=>?_⟩; obtain ⟨N,hN⟩:= h.trend t ht
    refine ⟨max k N,fun i hi j hj x=>?_⟩; obtain ⟨hp,hv⟩:= max_le_iff.mp hi; obtain ⟨he,hq⟩:=max_le_iff.mp hj; rw [← hk _ hp,← hk _ he]; exact hN i hv j hq x
lemma dual (h:Confluence f)(ha:Confluence t):Confluence (fun n x=> (f n x,t n x)):=by
    obtain ⟨b,hB⟩:=h.stretch; obtain ⟨c,hc⟩:=ha.stretch
    refine ⟨⟨max b c, (hB.and hc).mono fun n hn x=> max_le_max (hn.1 x) (hn.2 x)⟩,fun e he=>?_⟩; obtain ⟨v,hv⟩:=h.trend e he; obtain ⟨w,hw⟩:= ha.trend e he; refine ⟨max v w,fun i hi j hj x=>?_⟩; obtain ⟨hp,hq⟩:= max_le_iff.mp hi; obtain ⟨ht,hf⟩:=max_le_iff.mp hj; exact max_le (hv i hp j ht x) (hw i hq j hf x)
lemma front {s:ℕ→ Y}(hp:CauchySeq s):Confluence (fun i (_:X)=>s i):=by
    obtain ⟨b,hb⟩:= isBounded_iff_forall_norm_le.mp hp.isBounded_range; refine ⟨⟨b,Eventually.of_forall fun n x=> hb _ (Set.mem_range_self _)⟩,fun e he=>?_⟩; obtain ⟨K,hK⟩:= Metric.cauchySeq_iff.mp hp e he; exact ⟨K,fun n hn m hm _=>(hK n hn m hm).le⟩
lemma ahead (h:Confluence f)[ProperSpace Y](p:Y→Z)(hp:Continuous p): Confluence (fun n x=> p (f n x)):=by
    obtain ⟨b,hb⟩:=h.stretch; let S:= Metric.closedBall (0:Y) b; have hS:IsCompact S:= isCompact_closedBall 0 b
    obtain ⟨k,hk⟩:= eventually_atTop.mp hb; have hz(i)(hi:k ≤ i)(x): f i x∈ S:=by simpa [S,Metric.mem_closedBall] using hk _ hi x
    obtain ⟨a,ha⟩:= (hS.image (continuous_norm.comp hp)).bddAbove
    refine ⟨⟨a, (eventually_ge_atTop k).mono fun i hi x=> ha ⟨_,hz i hi x,rfl⟩⟩,fun e he=>?_⟩
    obtain ⟨c,hc,hC⟩:= Metric.uniformContinuousOn_iff.mp (hS.uniformContinuousOn_of_continuous hp.continuousOn) e he; obtain ⟨N,hN⟩:= h.trend _ (half_pos hc)
    refine ⟨max N k,fun i hi j hj x=>?_⟩; obtain ⟨he,h⟩:= max_le_iff.mp hi; obtain ⟨hf,hr⟩:=max_le_iff.mp hj; exact (hC _ (hz i h x) _ (hz j hr x) (lt_of_le_of_lt (hN i he j hf x) (half_lt_self hc))).le
lemma alongside (hp:Confluence f) {T:Type}(p:T→ X): Confluence fun n x=> f n (p x):=by obtain ⟨a,ha⟩:= hp.stretch; exact ⟨⟨a, ha.mono fun i hi x=> hi _⟩, fun t ht=> let ⟨N,hN⟩:= hp.trend t ht; ⟨N,fun n hn m hm i=>hN _ hn _ hm _⟩⟩
lemma ifs (h:Confluence f)(hg:Confluence g)(P:X→Prop): Confluence fun n x=> if P x then f n x else g n x:=by
    obtain ⟨b,hb⟩:=h.stretch; obtain ⟨c,hc⟩:=hg.stretch; refine ⟨⟨max b c,(hb.and hc).mono fun i hi x=>?_⟩,fun t ht=>?_⟩
    · split_ifs; exact (hi.1 _).trans (le_max_left ..); exact (hi.2 _).trans (le_max_right ..)
    obtain ⟨u,hu⟩:= h.trend _ ht; obtain ⟨v,hv⟩:= hg.trend _ ht; refine ⟨max u v,fun i hi j hj x=>?_⟩; obtain ⟨ha,h⟩:= max_le_iff.mp hi; obtain ⟨hr,hf⟩:= max_le_iff.mp hj; split_ifs; exact hu _ ha _ hr _; exact hv _ h _ hf _
lemma bats [ProperSpace Y](ha:Confluence f)(hb:Confluence g): Confluence (fun n x=> f n x+g n x):=ahead (dual ha hb) (uncurry (·+·)) (continuous_fst.add continuous_snd)
lemma fences [ProperSpace Y]{ι:Type}(T:Finset ι){p:ι→ℕ→X→Y}(he:∀ i, Confluence (p i)): Confluence fun n x=> ∑ i∈T,p i n x:=by
   induction T using Finset.induction_on with
   | empty=> simp_rw [Finset.sum_empty]; exact constantP (s:=fun _=>0) 0 (fun _=> (norm_zero : ‖(0:Y)‖=0).le)
   | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact bats (he i) ih
-- no combined normedRing assumptions
lemma metal (u:Y) : Confluence fun (_:ℕ)(_:X)=>u:= constantP ‖u‖ fun _=>le_rfl
section
variable [CommMonoid Y][ContinuousMul Y][ProperSpace Y]
lemma lit (h:Confluence f)(he:Confluence g):Confluence fun n x=> f n x*g n x:= ahead (dual h he) (uncurry (· * ·)) (continuous_fst.mul continuous_snd)
lemma wreaths {ι:Type}(T:Finset ι){p:ι→ℕ→X→Y}(h:∀ i,Confluence (p i)): Confluence fun n x=> ∏ i∈T,p i n x:=by
    induction T using Finset.induction_on with
    | empty=> simp_rw [Finset.prod_empty]; exact metal _
    | insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact lit (h i) ih
end
end Confluence
-- Linear images uniform on arbitrary X all coordinates x using op norm. any index.C. budgets.
section
variable {X Y Z:Type}[SeminormedAddCommGroup Y][SeminormedAddCommGroup Z]
lemma sheers (s:Y→ X→ Z) (B:ℝ)(f:ℕ→Y)(ht:∀ z:ℕ,∃ b:ℝ,∀ i, ‖s (f z) i‖≤ b)(hp:∀ v w:Y,∀ x, dist (s v x) (s w x) ≤ B* dist v w)(h:CauchySeq f): Confluence fun n x=>s (f n) x:=by
    have hb (e:ℝ)(he:0<e):∃ k:ℕ,∀ n ≥ k,∀ m≥k,∀ x,dist (s (f n) x) (s (f m) x)≤ e:=by
       let a:= |B|+1; have ha:0<a:=by unfold a; positivity
       obtain ⟨N,hN⟩:= Metric.cauchySeq_iff.mp h (e/a) (div_pos he ha); exact ⟨N,fun i hi j hj x=> (hp ..).trans ((mul_le_mul ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)) (hN i hi j hj|>.le) dist_nonneg ha.le).trans_eq (by change a*(e/a)=e; field_simp))⟩
    refine ⟨?_, hb⟩; obtain ⟨b,hb⟩:= hb _ zero_lt_one; obtain ⟨a,ha⟩:= ht b; exact ⟨a+1,(eventually_ge_atTop b).mono fun i hi x=> le_trans (upperD _ _) (add_le_add (ha x) (hb i hi b le_rfl x))⟩
end
section normed
variable {X Y:Type}[MeasurableSpace X][NormedAddCommGroup Y][NormedSpace ℝ Y] {f:ℕ→X→Y}
namespace Confluence
lemma account (μ:Measure X)[IsProbabilityMeasure μ](h:Confluence f)(he:∀ᶠ i in atTop, AEStronglyMeasurable (f i) μ):CauchySeq (fun i=> ∫ x,f i x ∂μ):=by
    obtain ⟨b,hb⟩:= h.stretch; obtain ⟨k,hk⟩:= eventually_atTop.mp (hb.and he); have ha m (h:k ≤ m):Integrable (f m) μ:= Integrable.of_bound (hk m h|>.2) _ (Eventually.of_forall (hk m h|>.1)); apply Metric.cauchySeq_iff.mpr; intro ε hε; obtain ⟨N,hN⟩:= h.trend (ε/2) (half_pos hε)
    refine ⟨max k N,fun i hi j hj=>?_⟩; obtain ⟨hp,hq⟩:= max_le_iff.mp hi; obtain ⟨h,hc⟩:= max_le_iff.mp hj; rw [dist_eq_norm,← integral_sub (ha _ hp) (ha _ h)]; apply lt_of_le_of_lt _ (half_lt_self hε)
    apply (norm_integral_le_integral_norm _).trans; rw [← show (∫ _ : X,ε/2∂μ)=ε/2 from by simp]; exact integral_mono ((ha _ hp|>.sub (ha _ h)).norm) (integrable_const _) (fun k=> (dist_eq_norm _ _).symm.trans_le (hN i hq j hc k))
end Confluence
end normed
end YM.FullVolume.Retreat
#print axioms YM.FullVolume.Retreat.Confluence.account
#print axioms YM.FullVolume.Retreat.Confluence.ahead
