import YM.RG08.Bands.Gall
/-!
# Exact join discrepancy exposed at ONE root and any native center tag.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I α β : Type}[Fintype α][Fintype β]{L m:Side}{n k r:ℕ}{U V:Screed ℝ α}{F:I→Screed ℝ α}{K:Row α β}{u:List I}{a:I→ℕ}
section pay
def hears (K:Row α β)(U:Screed ℝ α)(i j:ℕ): Rooted ℝ β j:=spring (U i j) K
lemma hears_s (h:Whole K)(hp:Sails k U): Sails k (hears K U):= swung (fun i=> ⟨fun j=> spring_tidy (hp.tide i j|>.pens) h,fun j hj=> by rw [hears,(hp.thin i).budget _ hj,spring_zero h]⟩)
lemma hears_sub (hp:Sails k U)(he:Sails n V)(h:Whole K): hears K (U-V)=hears K U-hears K V:= funext fun i=>funext fun j=>spring_sub (hp.tide i j|>.pens) (he.tide i j|>.pens) h
lemma heirs_b (h:Whole K)(hp:Sails k U)(he:Sails n V): hears K (gust U V)= gust (hears K U) (hears K V):= by
  have hh o (p: PAC β o)(U:Screed ℝ α)(n)(hp:Sails n U)(j): large (0:Site o) (n+j) (hears K U j) p= large (0:Site o) (n+j) (U j) (K.acts o *ᵥ p):= by unfold large; rw [Finset.sum_apply, Finset.sum_apply]; exact sum_congr rfl fun i _=> spring_tell (U j i) (hp.tide j i|>.pens) h _ p
  refine unrolled (hears_s h (braid_s hp he)) (braid_s (hears_s h hp) (hears_s h he)) ?_; intro i m; funext x; rw [hh m _ (gust U V) _ (braid_s hp he), sing_k hp he,sing_k (hears_s h hp) (hears_s h he)]; unfold billow; rw [Finset.sum_apply,Finset.sum_apply]; exact sum_congr rfl fun b _=> (congr_arg₂ (·*·) (hh m x U k hp b.1) (hh m x V n he b.2)).symm
lemma spr0 (h:Whole K): hears K (spine_one α)=spine_one β:= by
   ext1 i; ext1 j; by_cases ht:i+j=0
   · obtain ⟨rfl,rfl⟩ : i=0∧ j=0:= by omega
     refine Tidy.uniquely (hears_s h sails_start|>.tide 0 0) (sails_start.tide 0 0) ?_; intro m; funext v; unfold hears; rw [spring_tell _ (sails_start.tide 0 0|>.pens) h]
     simp only [rootSong, Tensor.diagonal,stitch_apply (sails_start (α:=α)|>.tide 0 0|>.pens.of_norm),stitch_apply (sails_start (α:=β)|>.tide 0 0|>.pens.of_norm)]; simp [rosary,spine_one]
   unfold hears spine_one; rw [if_neg ht,if_neg ht,spring_zero h]
lemma heirs_c (h:∀ i∈u,Sails (a i) (F i))(hp:Whole K): hears K (castF F u)= castF (fun i=> hears K (F i)) u := by
    induction u with
    | nil=> exact spr0 hp
    | cons i u ih=>
      have he j hj:= h j (List.mem_cons_of_mem _ hj); change hears K (gust _ (castF F u))=gust _ (castF _ u); rw [heirs_b hp (h i List.mem_cons_self) (cast_s he),ih he]
lemma momentum_p {K:Row α α}{U:Screed ℝ α}(h:Sails k U)(hp:Whole K){H:Canticle α}(hv: Gets H): Sails k (washed k none K H U):= by rw [←end_w]; exact reels_sink (dressing h hp hv)
end pay
section relation
variable {G:Gauge}{P:StripU G L}{F:I→ Tale G}{p:Site L}
def hammers (P:StripU G L)(F:I→Tale G)(p:Site L)(u:List I):= birth none (veiled P.cv) P.song (fun i=>reachP p (F i)) u
def jamT (P: StripU G L)(F:I→Tale G)(p:Site L)(a:I→ℕ)(u:List I): Tale G:= inscribed (loadᵣ a u) P p (castF F u) - castF (fun i=> inscribed (a i) P p (F i)) u
lemma jam_period (h:Fair P)(hv:∀ i∈u,Sails (a i) (F i)) : jamT P F p a u= Tall.hill P.scale (hears (scan P.tree) (endP (loadᵣ a u) (hammers P F p u))) := by
   have hk:= veiled_whole h.cm; have hm: Gets P.song:=⟨h.lived,fun i j=>⟨h.tune i j,h.bought i j⟩⟩
   let U i:=reachP p (F i); let S:= veiled P.cv; let H:=scan P.tree; have hx i hi:= sails_k p (hv i hi)
   let V i:= washed (a i) none S P.song (U i); have hV i (hi:i∈u): Sails (a i) (V i):= momentum_p (hx i hi) hk hm; have hH:= scan_whole h.ct
   unfold jamT hammers; rw [cast_end hk hm hx] -- hx binder
   let v:=loadᵣ a u; change Tall.hill _ (hears H (washed v none S P.song (reachP p (castF F u))))-castF (fun i=>Tall.hill P.scale (hears H (V i))) u= Tall.hill _ (hears H (washed v none S P.song (castF U u)-castF V u)); rw [hears_sub (momentum_p (cast_s hx) hk hm) (cast_s hV) hH, reach_full p hv, hill_sub, heirs_c hV hH, spectra_cast (fun i hi=>hears_s hH (hV i hi))]
-- existence invariant of Jam whole not every product leg separately after births
lemma stone_start (G:Gauge): Stone 0 (spine_one (Loc G 1)):= by
    refine ⟨sails_start.tide,sails_start.budget,?_⟩
    intro m i a b ha hb hx k; dsimp only; refine Fit.supply (Eventually.of_forall fun t=>?_) _
    unfold arco year large; simp only [Finset.sum_apply]; refine sum_congr rfl fun j hj=> ?_; refine congr_arg (t^j * ·) (sum_congr rfl ?_); intro u hu; by_cases he:j+u=0; · rw [show u=0 by omega]; exact pews (sails_start.tide j 0) ..
    unfold spine_one; rw [if_neg he,root_zero]; rfl
lemma stone_cast (h: ∀ i∈u,Stone (a i) (F i)): Stone (loadᵣ a u) (castF F u):= by
    induction u with
    | nil=> exact stone_start G
    | cons i u ih=> exact wind (h _ List.mem_cons_self) (ih fun i hi=>h i (List.mem_cons_of_mem _ hi))
lemma jam_party (h:Fair P)(hp:∀ i∈u,Stone (a i) (F i)): Stone (loadᵣ a u) (jamT P F p a u):= Stone.less (inscribe_law p h (stone_cast hp)) (stone_cast (fun i hi=> inscribe_law p h (hp i hi)))
end relation
end YM.RG08.Bands
