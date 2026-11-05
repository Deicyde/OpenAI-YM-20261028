import YM.UVExtension.Wet.Rad
import YM.UVExtension.Wren.Singer
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
open Function Filter Finset Lattice Wilson MeasureTheory RG Push Push.AbsoluteSums
open Steady Wren Extra.Histories Concert Local MergeProof Planned.GuardedAtom Guard Rainfall Eyelet Source Next.Foundations
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{κ ι α :Type}{v: Filter ι}{u t a b c η w:ℝ}{p:BudgetPoint}{F:κ→ RegularAddress n}{A:Hol G}{d:ℕ}{U:Labels.Frame G d}{B:SectionData U}
-- Produce existential no false topology.Weak.Are.
variable {V:κ→Type} {E:κ→Type} [∀ i, NormedAddCommGroup (E i)][∀ i,NormedSpace ℂ (E i)][∀ i,CompleteSpace (E i)] [NeBot v]
lemma steadyL (P:ι→lp E 1)(H:∀ i,V i→ E i→L[ℂ] ℂ)(hv: Transit v (fun i j k=> H j k (P i j)))(hp:∀ i r:_,∀ w:E i,(0:ℝ) ≤ r → (∀ j, ‖H i j w‖ ≤ r)→ ‖w‖ ≤ r) :∃ p,Tendsto P v (𝓝 p):=by
    apply cauchy_map_iff_exists_tendsto.mp; rw [cauchy_map_iff', tendsto_uniformity_iff_dist_tendsto_zero,Metric.tendsto_nhds]
    intro ε he; filter_upwards [hv.drought _ (half_pos he)] with i hi; obtain ⟨r,hv,H'⟩:= hi; let a:= P i.1 -P i.2; have ha(j) : ‖a j‖ ≤ r j:=hp _ _ _ (hv.1 _) (fun k=>by rw [show a j=P i.1 j-P i.2 j from rfl,map_sub]; exact H' ..)
    rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg]; change dist (P i.1) (P i.2)< _; rw [dist_eq_norm]; exact (((castL a).tsum_eq.symm.trans_le ((castL a).summable.tsum_le_tsum ha hv.2.1)).trans hv.2.2).trans_lt (half_lt_self he)
lemma expand {q :ℕ↪κ}{U:κ→Type}{Q:ι→(i:κ)→U i→ℂ}(h:Transit v (fun n i u=> Q n (q i) u))(hz:∀ i n,i∉ Set.range q→Q n i=0):Transit v Q:=by
   obtain ⟨f,hf,hq⟩:=h.rain
   let g n:=Function.extend q (f n) 0; have hm n k:g n (q k)= f n k:=q.injective.extend_apply ..; have hs(n i)(h:i∉ Set.range q):g n i=0:=extend_apply' _ _ _ h
   have hp:Swift v g:=by
       obtain ⟨K,hK⟩:= hf.books; constructor
       · refine ⟨K,hK.mono fun n hn=>?_⟩; apply Local.sumBudget_pass q _ ?_ (hs n); simp_rw [hm]; exact hn
       intro ε he; obtain ⟨s,hs'⟩:= hf.drops ε he; refine ⟨s.map q,hs'.mono fun n hn=> ?_⟩; apply Local.sumBudget_pass q _ _ _
       · simp_rw [hm,Finset.mem_map]; simp only [EmbeddingLike.apply_eq_iff_eq,exists_eq_right]; convert! hn using 2 with i; split_ifs <;> rfl
       intro i hi; split; rfl; exact hs _ _ hi
   refine ⟨⟨g,hp,hq.mono (fun n hn i k=>?_)⟩,fun i=> ?_⟩
   · by_cases he:i∈Set.range q; obtain ⟨j,rfl⟩:=he; rw [hm]; exact hn j k
     rw [hs n i he,hz i n he,Pi.zero_apply,norm_zero]
   by_cases he:i∈Set.range q; obtain ⟨j,rfl⟩:=he; exact h.meters j
   simp_rw [fun n=>hz i n he,Pi.zero_apply]; exact Tune.nil
variable {R:ι→ Rep G n}(j:ι)(h:∀ i,(R i).Lawful a b c η t)(hz:∀ i,(R i).p=p)(hq:∀ i,(R i).activities.forced=(R j).activities.forced)(hw:0 <w)(hk: Transit v (fun i j x=> (R i).activities.K j x))
variable {X:ℕ→Support n}(he:Readable A B p n u)(M:ι→ Local.Raw U n)(hp:∀ i,Valid (M i) X (R i) t B A u w)(K:∀ i:ι, Keeper (R i).p (R i).activities)(hb:Cof (G:=G) (v:=v) p X (fun i=> (M i).bulk))(hF : Transit v (fun i s x=> (M i).forced s x))(ha:∀ i,(M i).seed=0)
-- Cast from (R i).p to p.Avoid HEq below by simp subst on isolated helper invocation.
section move
variable (Q:Rep G n)
def warp (Xq: Coefficient U n)(H:Hol G)(w:ℝ)(hz:Q.p=p): Bucket U p H n:= hz ▸ (Eye Xq H Q w)
include Q
lemma worthT (Xq:Coefficient U n) (h:Eligible Xq A Q w)(hz:Q.p=p): (warp Q Xq A w hz).1=Xq.x∧ (∀ (i:Eyelet.Slot n) k,gaze d A p i k (warp Q Xq A w hz).2.1= Eyelet.fee p i.1.val*(Concert.Tap.read k (graft Xq i))) ∧ (∀ (i:StockTag n) x,tire p i x (warp Q Xq A w hz).2.2= ((Eyelet.fee p i.val.1 / w:ℝ):ℂ)*profile Q.activities Xq.forced i.val x.tag):=by
   subst p; unfold warp; rw [h.vistas]; exact ⟨rfl,h.take,h.make⟩
end move

include j hF hp h hb hz hq hw he hk ha
-- all observations; aligned pointers
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
lemma steadfast: ∃ x,Tendsto (fun i=>warp (R i) (wallet (K i) X B (M i) A) A w (hz i)) v (𝓝 x):=by
   let P i:= warp (R i) (wallet (K i) X B (M i) A) A w (hz i); have hv i:=fits (hz i|>.symm ▸ he) (h i) hw (K i) (hp i) ; have hT i:=worthT _ _ (hv i) (hz i)
   obtain ⟨hq',hK,hM⟩:= receipt X hb he; let Y i:=(P i).1
   have hh: Tune v (fun i (_:Unit)=> Y i):=by
      have ht(i):Y i=∑' j, weighted A U 0 (X j) p.threshold ((M i).bulk j):=by
          unfold Y P; rw [(hT i).1]; change (M i).seed+∑' j,Raw.row _ _ _ _ _ j=_; rw [ha, zero_add]; change ∑' j,weighted _ _ _ _ (R i).p.threshold _=_; rw [hz i]
      simp_rw [ht]; exact hq'.includes (fun _ _=>())
   let Z n:= (P n).2.1; let k i:= joint B (0:Site n) (X i); -- fixed frameE
   have hW(x) : (0:Site n)∈ k x:= (hv j).form.origin _ -- hp.R
   let e : ℕ↪ Eyelet.Slot n:= ⟨fun x=> (⟨k x,hW x⟩,x),fun x y he=>congr_arg Prod.snd he⟩
   let g m (i:Eyelet.Slot n) u:= gaze d A p i u (Z m)
   have hx(i m)(u): g i (e m) u= (Eyelet.fee p (k m):ℂ)*u.read (Local.residual A B 0 (X m) p.threshold ((M i).bulk m)):=by
       unfold g Z P; rw [(hT i).2.1]; apply congr_arg
       refine congr_arg u.read ?_; rw [← hz i]; exact if_pos rfl
   have hu : Transit v g:=by
      refine expand (q:=e) ?_ ?_; swap
      · intro i n hi; funext v; have he: graft (wallet (K n) X B (M n) A) i = 0:= if_neg fun h=>hi ⟨i.2,Prod.ext (Subtype.ext h.symm) rfl⟩
        unfold g Z P; rw [(hT n).2.1 i v, he]; simp only [Tap.read]; rw [show (0:Config G (show Side from _ )→ℂ) = fun _=> 0 from rfl,Work.G07.left_const,ite_self,mul_zero]; rfl
      simp_rw [hx]; obtain ⟨f,hf,hA⟩:=hK.earns.rain; obtain ⟨u,hu,hu'⟩:= Verso.limits p (fun i=> k i) p.supportExponent -- function support finite lemma at prior.Script.Evidence
      obtain ⟨c,hc⟩:=hf.books; refine ⟨⟨_,hf.scales u hu.le,(hA.and hc).mono (fun n hp i x=>?_)⟩,fun i=> (hK.earns.meters i).cont (continuous_const.mul continuous_id)⟩
      rw [norm_mul]; exact mul_le_mul ((Complex.norm_real _).trans_le ((Real.norm_of_nonneg (Eyelet.toll_pos ..|>.le)).trans_le (hu' i))) (hp.1 i x) (norm_nonneg _) hu.le
   obtain ⟨E,hE⟩:= steadyL Z (flash A d p) (show Transit v (fun n i k=> flash A d p i k ((Z n) i)) from hu) (fun _ _ x hx hS=> (BoundedContinuousFunction.norm_le hx).2 hS) -- coercion
   have hpA(n): profile (R n).activities (wallet (K n) X B (M n) A).forced=profile (R n).activities (M n).forced + hook (R n).activities p.threshold (clipSum (fun i=> joint B 0 (X i)) (fun j=> rebate A B 0 (X j) p.threshold ((M n).bulk j))):=by
       rw [← show (R n).p=p from hz n] -- no dependent? wallet
       exact permitT (hz n|>.symm ▸ he) (h n) hw (K n) (hp n)
   let g n:=profile (R n).activities (wallet (K n) X B (M n) A).forced
   have Hg: Transit v (fun n i x=> g n i x):=by
        have hh:= clipsM (barcode (R j).activities) hF; have hv(n): barcode (R n).activities=barcode (R j).activities:= by unfold barcode; rw [hq]
        unfold g; simp_rw [hpA]; apply Transit.together _ _; exact (hh.fade (by filter_upwards with i u; funext x; unfold profile; rw [hv i])); exact hookM R j hq p.threshold hk (clipsM k hM)
   let T i:=(P i).2.2; have hvK: Transit v (fun i j v=> burn G p n j v (T i j)):=by
      have ht(m): Tune v (fun i x=> burn G p n m x (T i m)):=by
          refine ((Hg.meters m.val|>.cues Lab.tag).cont (F:=fun x=>((Eyelet.fee p m.val.1/w:ℝ):ℂ)* x) (continuous_const.mul continuous_id)).switch ?_
          filter_upwards with i; exact funext fun v=> ((hT i).2.2 m v).symm
      exact Transit.ready ht
   obtain ⟨X',hX⟩:=steadyL T (burn G p n) hvK (fun _ _ x hx hS=> (BoundedContinuousFunction.norm_le hx).2 hS)
   obtain ⟨Y',hY⟩:=leafy hh; exact ⟨(Y',E,X'),hY.prodMk_nhds (hE.prodMk_nhds hX)⟩
end YM.UVExtension.Wet
