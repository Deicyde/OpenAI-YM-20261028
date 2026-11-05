import YM.RG08.Creek.Supply
/-! # Linear conjunction of ring operations on ALL-origin auxiliary calculations. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I α β X: Type} [Fintype I][Fintype α][DecidableEq I][Fintype β]{G:Gauge}{a:I→ℕ}{F: Topaz I (Screed ℝ α)}{τ:ℕ}{r:ℝ}
lemma sm_k {U:Screed ℝ α}(h:Sails τ U)(r:ℝ):Sails τ (r • U):= swung fun i=>(h.thin i).sc _
lemma line_k (t:Finset X){F:X→ Screed ℝ α}(hp:∀ i∈t,Sails τ (F i)): Sails τ (∑ i∈t,F i):= swung fun i=>by rw [Finset.sum_apply]; exact Loomed.sum fun i h=> (hp i h).thin _
lemma festive_k (h:∀ t,Sails (vanes a t) (F t))(t:Finset I): Sails (vanes a t) (Wax.banner t F gust (spine_one _)):=by
   induction t using strongInductionOn with
   | _ t ih=>
     rw [Wax.banner]; split; next hp=> subst t; rw [vanes_empty]; exact sails_start
     apply sm_k; refine line_k _ (fun i _=>?_)
     rw [wind_cell a _ (mem_filter.mp i.property).1]; exact braid_s (sm_k (h _) _) (ih _ (part_lt i.property))

lemma mat_p (h:∀ t,Sails (vanes a t) (F t))(t:Finset I)(op:Screed ℝ α → Screed ℝ β)(h0:op (spine_one α)=spine_one β)(hp:∀ U V:Screed ℝ α,∀ i j,Sails i U→ Sails j V→ op (gust U V)= gust (op U) (op V))(hq:∀ V i,Sails i V→ ∀ k:ℝ,op (k • V)=k • op V)(hv:∀ W:Screed ℝ α,∀ V,∀ k,Sails k V→ Sails k W→ op (V+W)=op V+op W) :
  op (Wax.banner t F gust (spine_one _))=Wax.banner t (op∘ F) gust (spine_one _):=by
   induction t using strongInductionOn with
   | _ t ih=>
     rw [Wax.banner,Wax.banner]; split; next hz=> exact h0
     let U p:= Wax.banner p F gust (spine_one _); let M (i:directVote t):= gust (sons F i.val.1) (U i.val.2)
     have hM i:Sails (vanes a t) (M i):= by rw [wind_cell a _ (mem_filter.mp i.property).1]; exact braid_s (sm_k (h _) _) (festive_k h _)
     have hh: ∀ s: Finset (directVote t), op (∑ i∈s,M i)=∑ i∈s,op (M i):= by
        intro s; induction s using Finset.induction_on with
        | empty=> rw [sum_empty,sum_empty]; simpa only [zero_smul] using hq _ _ sails_start 0
        | insert i p hi ih=> rw [sum_insert hi,sum_insert hi,hv _ _ _ (hM i) (line_k _ (fun i _=>hM _)),ih]
     rw [hq (∑ p: directVote t,M p) _ (line_k _ (fun i _=>hM _)), hh]; congr 1; apply sum_congr rfl; intro i _
     unfold M U sons; rw [hp _ _ _ _ (sm_k (h _) _) (festive_k h _),ih _ (part_lt i.property),hq _ _ (h _)] ; rfl
lemma access_reach {G:Gauge}{F:Topaz I (Tale G)}(h:∀ t,Sails (vanes a t) (F t)){L:Side}(p:Site L)(t:Finset I):
   reachP p (Wax.banner t F gust (spine_one _))=Wax.banner t (reachP p ∘ F) gust (spine_one _):= mat_p h t (reachP p) (stem0 p) (fun _ _ i j hp hv=> gust_springs p hp hv) (fun V k hv r=> funext fun i=>funext fun j=>by unfold reachP lotS; simp only [Pi.smul_apply]; unfold shiftP; rw [tub_scale (hv.tide _ j|>.pens),spring_a ((hv.tide _ _|>.pens).pours _) _ skylight_ok]) (fun W V k hv h=> funext fun i=>funext fun j=>by unfold reachP lotS; simp only [Pi.add_apply]; unfold shiftP; rw [Pens.tub_plus _ (hv.tide _ _|>.pens) (h.tide _ _|>.pens)]; exact spring_plus ((hv.tide _ _|>.pens).pours _) ((h.tide _ _|>.pens).pours _) skylight_ok)
lemma access_back {K: Row α β}(hv:Whole K)(S: PowerSeries ℝ)(h:∀ t,Sails (vanes a t) (F t))(t:Finset I):
    Tall.hill S (hears K (Wax.banner t F gust (spine_one _)))=Wax.banner t ((Tall.hill S ∘ hears K) ∘ F) gust (spine_one _):= by
    refine mat_p (β:=β) h t (Tall.hill S ∘ hears K) ?_ ?_ ?_ ?_
    · simp only [comp_apply,spr0 hv,growth_unit]
    · intro V U i j h g; simp only [comp_apply,heirs_b hv h g,spectrum_b (hears_s hv h) (hears_s hv g)]
    · intro V i h k; have hp : hears K (k • V)= k • hears K V:= funext fun j=>funext fun t=> spring_a (h.tide _ _|>.pens) k hv
      simp only [comp_apply,hp,hill_weight]
    intro V U i h g; have he: hears K (U+V)=hears K U+hears K V:= funext fun j=>funext fun t=> spring_plus (h.tide _ _|>.pens) (g.tide _ _|>.pens) hv
    simp only [comp_apply,he,hill_add]
lemma isbn {L:Side}{P:StripU G L}(hp:Fair P)(hv:∀ m,(veiled P.cv|>.acts m)ᵀ=(veiled P.cv|>.acts m)) (o:Site L){A:Topaz I (Tale G)}(h:∀ t,Stone (vanes a t) (A t))(hx:A ∅=0):
   let Z:=pulse none (veiled P.cv) P.song (reachP o ∘ A)
   let V t:= Tall.hill P.scale (hears (scan P.tree) (endP (vanes a t) (Z t)))
   ∀ t, Fabrics G V t= inscribed (vanes a t) P o (Fabrics G A t):= by
   intro Z V t; have hk:= veiled_whole hp.cm; have hM: Gets P.song:=⟨hp.lived,fun i j=>⟨hp.tune i j,hp.bought i j⟩⟩
   let g(t:Finset I):= endP (vanes a t) (Z t); have he t:=sails_from (h t); have hz t:= sails_k o (he t); have hT t: Sails (vanes a t) (g t):= reels_sink (pulse_ok (reachP o∘ A) hk hM hz t)
   have hX:reachP o (A ∅)=0:= by rw [hx]; exact funext fun i=>funext fun j=>lot_zero _
   rw [show Fabrics G V t=_ from (access_back (scan_whole hp.ct) P.scale hT t).symm]
   change _=Tall.hill P.scale (hears (scan P.tree) (washed (vanes a t) none (veiled P.cv) P.song (reachP o (Fabrics G A t))))
   unfold Fabrics; rw [access_reach he o, ceremony (F:=reachP o ∘ A) hz hk hM hX hv]
end YM.RG08.Creek
