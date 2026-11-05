import YM.RG08.Creek.Drops
/-! # Single-slot extraction equivalence preserves ambient formal normalization through all combined lanes. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I:Type} [Fintype I][DecidableEq I]{G:Gauge}{R v A B:ℝ}{L:Side}{T: Finset I}{a b:I→ℕ}  -- del X
variable {τ D e r:ℕ}{F: Topaz I (Tale G)}{P: StripU G L}
lemma bulb_axis (i:I)(h:Stone τ (F {i}))(hp:F ∅=0) : Fabrics G F {i}=F {i}:= by
   let T:Finset I:= {i}; have he : Bulb (spine_one _) gust F (Fabrics G F):= bannerC _ _ _ gust_z hp
   have hx:= congr_fun he.2.2 T
   rw [festival,sum_eq_single_of_mem (T,∅) (by simp [norms_par,T])] at hx
   · rw [he.2.1] at hx; unfold sons T at hx; simp only [card_singleton,Nat.cast_one,one_smul] at hx; exact hx.trans (gust_coin (sails_from h))
   intro a ha ho
   have hh : a.1=∅:=by
     have hT:= par_count ha; rw [show T.card=1 from card_singleton i] at hT
     have hA:= mem_powerset.mp (mem_product.mp (mem_filter.mp ha).1).1; by_contra he
     have hp := card_ne_zero.mpr (nonempty_iff_ne_empty.mpr he); apply ho; exact Prod.ext (Finset.eq_of_subset_of_card_le hA (by change T.card ≤ _; simp only [T, card_singleton]; omega)) (card_eq_zero.mp (by omega))
   rw [hh, sons_empty, gust_z]
def Harmon (K:Layouts I G D R)(U:I→ BoardU D R G): Prop:= ∀ x (i:I), K x {i}=markZ U x {i}
-- one surgery at o=0 in canonical
variable {K:Layouts I G D R}{U:I→ BoardU D R G}
lemma civic_o (he:Climate P)(h:Sense a K)(hR:1/2≤ R)(hp:∀ i, Marvel (a i) (U i)) (hv:Harmon K U)(b:I→ℕ): Harmon (creekT P a (fun i=>rallyW L (b i)) K) (fun i=>Needle.push P (a i) (b i) (U i)) := by
   let V(i):= Needle.push P (a i) (b i) (U i); let d i:=rallyW L (b i); let S:= creekT P a d K; have hs:= creekS_w L he h hR d
   intro x i; have hx(v:I→Sight D R): access v (S x) {i}= access v (markZ V x) {i}:=by
     let T: Finset I:= {i}; have hq (b':Places I)(y: I→ Sight D R): SolarPaper K b' y T=access y (markZ U b') T:= by
       unfold SolarPaper; rw [bulb_axis i (h.stone b' y _) (access_nil y (h.void _))]; unfold access; rw [show K b' T=markZ U b' T from hv b' i]
     obtain ⟨f,hf⟩:= doors D R (v i)
     have hh: SolarPaper S x v T=access v (S x) T:= bulb_axis i (hs.stone ..) (access_nil v (hs.void _))
     change access v (S x) T=_; rw [←hh,show SolarPaper S x v T= _ from crest_p he hR h x v T, show vanes a T=a i from by simp [vanes,T], Finset.prod_singleton]
     let g(p: Site L):= Pages.roll (spinner p) (L.val:ℝ)⁻¹ f
     let Q (p:Site L):= d i • Town.season (stemA L (x i) p) (ringU (g p) (U i)); have hQ(p): Stone (a i) (Q p):=((Stone.graph (hp i) _).transport _).weight _
     let D : (T → Site L)→ Site L:= fun p=> enter T p i
     have hz: Bijective D:= by
        constructor
        · intro X Y h; funext j; obtain ⟨j,hp'⟩:=j
          obtain rfl: j=i:= mem_singleton.mp hp'
          exact (dif_pos hp':D X= X ⟨_,hp'⟩).symm.trans (h.trans (dif_pos hp'))
        intro x; exact ⟨fun _=>x,dif_pos (mem_singleton_self _)⟩
     rw [show (∑ p:subroll T (Site L),d i • SolarPaper K (footT L x (enter T p)) (spar (enter T p) he.odds hR v) T)=∑ p: Site L,Q p from ?_, inscript_list univ _ Q (fun i _=> hQ i) he.toFair, eye_sh x v i f hf.symm,show ringU f (V i)=_ from anthem _ hR he.toFair (hp _) (b i),Finset.smul_sum, season_group]; swap
     · refine Fintype.sum_bijective D hz _ Q ?_; intro p; rw [hq, eye_sh _ (spar (enter T p) he.odds hR v) i (g (D p)) (by unfold spar; rw [← hf, (Pages.scroll_leaf ..).2])]
     refine sum_congr rfl fun p _=>?_
     unfold Q; have hp:= Stone.graph (hp i) (g p); rw [inscription_sc _ _ (hp.transport _) he.toFair, order_moves (p:=p) hp he.toFair (by rw [nil_root,zero_add]; rfl)]; rfl
   funext j k; refine tapUni fun v=>congr_fun (congr_fun (hx v) j) k
lemma harmony_initial (U:I→BoardU D R G): Harmon (markZ U) U:= fun _ _=> rfl
end YM.RG08.Creek
