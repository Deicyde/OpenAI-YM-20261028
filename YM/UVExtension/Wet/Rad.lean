import YM.UVExtension.Wet.Brook
import YM.UVExtension.Rainfall.Trail
/-! Millet series . Raw Nan.Assumulate accepted.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
open Function Filter Finset Lattice Wilson MeasureTheory RG Push Push.AbsoluteSums
open Steady Wren Extra.Histories
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{κ ι α :Type}{v: Filter ι}{t:ℝ}{p:BudgetPoint}
open Concert Rainfall Source Push.Local MergeProof Next.Foundations
variable {X:Support n}
lemma tapsK (d:Tap p G 0 X) (f g:Config G n→ℂ)(he:p.Regular X f)(hg:p.Regular X g) : d.read (f-g) = d.read f - d.read g :=by
    have hh:= regular_sub he hg; apply eq_sub_of_add_eq
    exact (Push.Local.left_add (f:=f-g) (g:=g) d.poll (hh.smooth _ d.live) (hg.smooth _ d.live) d.card).symm.trans (congr_arg d.read (sub_add_cancel ..))
structure Cof (p:BudgetPoint)(X:κ→Support n)(F:ι→κ→ Config G n→ℂ):Prop where
    works :∀ i j,p.Regular (X j) (F i j)
    earns : Transit v (fun i j (V:Tap p G 0 (X j))=> V.read (F i j))
variable {F:ι→κ→ Config G n→ℂ}{d:ℕ}{U:Labels.Frame G d}{H: Hol G} {B:SectionData U}
variable (X:κ→Support n)(h:Cof (G:=G) (v:=v) p X F)(he: Readable H B p n t)
local notation "Y"=> p.threshold
include h
lemma priceR : ∃ f:ι→ κ→ℝ,Swift v f ∧ ∀ᶠ n in v,∀ i,p.supBounds 0 (X i) (F n i) (f n i):=by
   obtain ⟨a,ha,hA⟩:= h.earns.rain; obtain ⟨c,hc⟩:= ha.books; exact ⟨_,ha, (hc.and hA).mono fun n hn j=>tap_bound.mpr ⟨hn.1.1 _,hn.2 j⟩⟩
lemma speedR (j:κ)(ε:ℝ)(hp:0<ε): ∀ᶠ n in v ×ˢ v, p.supBounds 0 (X j) (F n.1 j-F n.2 j) ε:=by
   filter_upwards [(h.earns.meters j).uv ε hp] with n hn; apply tap_bound.mpr; exact ⟨hp.le,fun i=> by rw [tapsK i _ _ (h.works n.1 j) (h.works n.2 j)]; exact hn i⟩
include he
lemma receipt : Transit v (fun i j (_:Unit)=> weighted H U 0 (X j) Y (F i j))∧ Cof (G:=G) (v:=v) p (joint B 0 ∘ X) (fun i j=> Local.residual H B 0 (X j) Y (F i j)) ∧ Transit v (fun i j V=> rebate H B 0 (X j) Y (F i j) V):=by
   obtain ⟨f,hf,hP⟩:=priceR X h; obtain ⟨r,hr⟩:= hf.books
   let b:= readPrice H U; let c:= atomPrice H U t; have hb : 0<b:= zero_lt_one.trans_le (readPrice_pos ..); have hc: 0 < c:= zero_lt_one.trans_le (atomPrice_ge_one _ _ he.nonneg) -- test
   have ht : Swift v (fun n j=> c*f n j):= hf.scales c hc.le
   have hr: Transit v (fun i j (_:Unit)=> weighted H U 0 (X j) Y (F i j)):=by
       have hx : ∀ᶠ i in v,∀ j, ‖weighted H U 0 (X j) Y (F i j)‖≤ b*f i j:= hP.mono (fun i hi j=> (Local.norm_le_size ..).trans (weighted_bound H U 0 (h.works ..) he.order he.power (hi j)))
       refine ⟨⟨_,hf.scales b hb.le,hx.mono fun i hi j _=> hi j⟩,fun j=> ⟨⟨b*r,(hr.and hx).mono fun i hi _=> (hi.2 _).trans (mul_le_mul_of_nonneg_left (budget_single hi.1 _) hb.le)⟩,?_⟩⟩
       intro ε hε; filter_upwards [speedR X h j (ε/b) (by positivity)] with n hn v
       exact (Local.norm_le_size ..).trans ((shiftsT he (h.works _ j) (h.works _ j) hn).1.trans_eq (by change b*_ = _; field_simp))
   refine ⟨hr,?_,?_⟩
   · have hp(n j): p.Regular (joint B 0 (X j)) (Local.residual H B 0 (X j) Y (F n j)):= (convert_atom _ he (h.works _ j)).1
     have h':∀ᶠ i in v,∀ j,p.supBounds 0 (joint B 0 (X j)) (Local.residual H B 0 (X j) Y (F i j)) (c*f i j):= hP.mono (fun i hi j=> (charge_atom _ he (h.works ..) (hi j)).1)
     obtain ⟨z,hz⟩:=ht.books; refine ⟨hp, ⟨_,ht,h'.mono fun i hi j=> ((tap_bound.mp (hi j)).2)⟩,fun j=> ⟨⟨z,(hz.and h').mono (fun i h k=> ((tap_bound.mp (h.2 j)).2 k).trans (budget_single h.1 _))⟩,?_⟩⟩ -- nested! fix
     intro ε hε; filter_upwards [speedR X h j (ε/c) (by positivity)] with n hn k; have hk:= (tap_bound.mp ((shiftsT he (h.works _ j) (h.works _ j) hn).2.1)).2 k; rw [tapsK _ _ _ (hp ..) (hp ..)] at hk; exact hk.trans_eq (by change c*_ = _; field_simp)
   have h':∀ᶠ i in v,∀ j V, ‖rebate H B 0 (X j) Y (F i j) V‖ ≤ c*f i j:= hP.mono (fun i hi j=> (charge_atom _ he (h.works ..) (hi j)).2)
   obtain ⟨z,hz⟩:=ht.books; refine ⟨⟨_,ht,h'⟩,fun j=> ⟨⟨z,(hz.and h').mono fun i h k=> (h.2 j k).trans (budget_single h.1 _)⟩,?_⟩⟩
   intro ε hε; filter_upwards [speedR X h j (ε/c) (by positivity)] with n hn k; exact ((shiftsT he (h.works _ j) (h.works _ j) hn).2.2 k).trans_eq (by change c*_ = _; field_simp)

omit he h
lemma leafy {Z:Type}[NormedAddCommGroup Z][CompleteSpace Z] [NeBot v] {f:ι→Z}(h:Tune v (fun i (_:Unit)=>f i)): ∃ a,Tendsto f v (𝓝 a):= by
  apply cauchy_map_iff_exists_tendsto.mp; rw [cauchy_map_iff', tendsto_uniformity_iff_dist_tendsto_zero]; exact (h.leaf (fun (x:ι×ι) b=>if b then x.1 else x.2) (fun b=> by cases b ; exact tendsto_snd; exact tendsto_fst) (fun _=>())).2
-- Reindex.Profile K. portion receipt only. all topology.
variable {R:ι→Rep G n}
lemma bowls (Q:ι→Rep G n) (i:ι) (h:∀ n,(Q n).activities.forced=(Q i).activities.forced)(t:ℝ) (hz:Transit v (fun n j u=> (Q n).activities.K j u)) (w:Support n) (u:Box n) : Tune v (fun n U=> MergeProof.portion (Q n).activities t w u U):=by
   obtain ⟨a,ha,hA⟩:=hz.rain; obtain ⟨B,hB⟩:=ha.books; let g n s x:= (∏ j∈s, (Q n).activities.K j x)
   have hg : Transit v g :=⟨⟨_,ha.powerList,(hA.and hB).mono (fun n hi s x=> by unfold g; rw [norm_prod]; exact Finset.prod_le_prod (fun _ _=> norm_nonneg _) fun _ _=> hi.1 _ x)⟩,fun i=> Sheets.tunes _ _ (fun i _=> hz.meters _)⟩
   have he : Transit v (fun n s U=> (g n s U:ℂ)):=by obtain ⟨a,ha,hA⟩:=hg.rain; exact ⟨⟨_,ha,hA.mono fun n hn i x=> by rw [Complex.norm_real]; exact hn i x⟩,fun i=>(hg.meters i).cont Complex.continuous_ofReal⟩
   let b(s:Finset ℕ)(U:Config G n):Prop:= Packs (Q i).activities w s ∧ fusionBox (Q i).activities w s=u ∧ u.1 ∩ flags t U=u.2
   apply ((he.masks b).includes (fun x _=>x)).switch; filter_upwards with j; funext Z; unfold portion; refine tsum_congr fun s=>?_
   have hp:Packs (Q i).activities w s = Packs (Q j).activities w s∧fusionBox (Q j).activities w s=fusionBox (Q i).activities w s:=by
       have H (X Ym:Activities G n)(h:X.forced=Ym.forced) : Local.Packs X w s= Local.Packs Ym w s ∧ fusionBox Ym w s=fusionBox X w s:=by
           rcases X with ⟨a,b,c,d⟩; rcases Ym with ⟨e,f,g,h'⟩; change b=f at h; subst f; exact ⟨propext ⟨fun ⟨hx,hy,hz⟩=> ⟨hx,hy,hz⟩,fun ⟨hx,hy,hz⟩=> ⟨hx,hy,hz⟩⟩,rfl⟩
       exact H _ _ (h _).symm
   unfold b grasp; simp_rw [hp.1,hp.2]; split_ifs; · simp [g];
   rfl
lemma hookM (Q:ι→Rep G n) (i:ι) (h:∀ n,(Q n).activities.forced=(Q i).activities.forced)(t:ℝ) (hz:Transit v (fun n j u=> (Q n).activities.K j u)) {f:ι→ Response G n}(hh:Transit v (fun i j v=> f i j v)) : Transit v (fun n p u => hook (Q n).activities t (f n) p u):=by
    apply Transit.ready; intro j; apply Tune.term; intro k _; exact ((hh.meters _).prod (bowls Q i h t hz _ j)).cont (F:=fun x=> x.1*x.2) (by fun_prop)
lemma clipsM (p:κ→α) [Finite α]{f:ι→ κ → Config G n→ℂ}(h:Transit v (fun i j x=>f i j x)): Transit v (fun n j v=> cram p (fun i=> f n i v) j):= by
    refine Transit.ready (fun i=>?_); exact (h.many (fun t:{t// p t=i}=> t.val) Subtype.val_injective (fun _ (x:Config G n)=> x)).includes (fun x _=> x)
end YM.UVExtension.Wet
