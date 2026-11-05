import YM.RG08.Harvest.Roots
/-!
# Qualitative all moments for membership/recovery
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Harvest
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands Pill Wings PowerSeries Taste Plot Plot.High
open scoped BigOperators Topology Real ContDiff Classical
variable {I α:Type}{L:Side}{z r s k j t h D i:ℕ}{R:ℝ}{G:Gauge}
variable {F:Shale α r}
section members
lemma lifelong : Vale.Polished F↔∀ i,∃ A, Run.cis i 1 F A:= by
   constructor
   · intro h i; obtain ⟨A,H⟩:=h i; exact ⟨A,H.shrink (zero_le_one.trans (tailp zero_le_one)) (fun z=> by simpa only [tailP,one_mul] using lower_bill (z:Beads α r) i)⟩
   intro h i; obtain ⟨A,H⟩:=h (i*r); exact ⟨A,H.shrink (mint_pos α r i) (fun z=> by simpa only [tailP,one_mul] using (greater_bill (z:Beads α r) i))⟩
lemma venez {W:Shale α s}(h:Vale.Polished F)(hp:Vale.Polished W): Vale.Polished (braidV F W):= lifelong.mpr (fun i=>by obtain ⟨a,hA⟩:= lifelong.mp h i; obtain ⟨b,hB⟩:= lifelong.mp hp i; exact ⟨_,braid_pol hA hB zero_le_one⟩)
lemma pinning {X:Tale G}(h:Lank X)(k:Cover) : Lank (Town.season k X) := fun i j=> lifelong.mpr (fun v=>by
   obtain ⟨A,H⟩:= lifelong.mp (h i j) v; exact ⟨_,roam_cis H zero_le_one k⟩)
lemma polish_chart {F V:Screed ℝ α}(h:Lank F)(he:Lank V): Lank (gust F V) := by
   intro i j; unfold gust; rw [Finset.sum_apply]; refine polished_sum (fun _ _=> polished_sum (fun p (_:p∈wheel j)=>?_)); unfold grant; split; next h'=> cases h'; exact venez (h _ _) (he _ _) -- .. implicit
   exact polished_zero ℝ α j
lemma inscription_L {Q:StripU G L}(h: Fair Q){V:Tale G}(p:Site L)(he:Lank V)(hp:Stone t V): Lank (inscribed t Q p V):= by
    have hx: Lank (reachP p V) := fun i j=> rung_price skylight_ok (lifelong.mpr (fun v=>by
      obtain ⟨A,H⟩:= lifelong.mp (he i j) v; exact ⟨_,plank_m p H zero_le_one le_rfl (one_div_le_one_div_of_le zero_lt_one (show 1 ≤ (L.val:ℝ) by exact_mod_cast L.property)|>.trans (by simp))⟩))
    have hw:Lank (originS t Q p V none):= fun i j=> rung_price (scan_whole h.ct) (polished_sum (fun z (_:z∈range (windows t i+1))=> (treble_shelf (veiled_whole h.cm) h.tune h.bought (reaches hp.cap hp.tidy p|>.2) hx (n:=z) i j : Vale.Polished (murmur none (veiled Q.cv) Q.song (reachP p V) z i j))))
    exact fun i j=> polished_sum (fun p (_:p∈range (i+1))=>polished_scale (hw p j) _)
end members

section scene
-- point-spectrum arc as FINITE combinations of exact invariant entire-order stencils
variable {W:Type}[TopologicalSpace W]
inductive Via (G:Gauge)(k:ℕ) : (W→Tale G)→Prop where
 | head (F:Tale G)(h:Stone k F)(p:Lank F) (g:W→ℝ)(he:Continuous g) : Via G k (fun i=>g i • F)
 | plus (F V:W→Tale G)(p:Via G k F)(q:Via G k V) : Via G k (F+V)
lemma stead {H:W→ Tale G}(he:Via G k H)(i:W) : Stone k (H i) ∧ Lank (H i) := by
    induction he with
    | head F h p g he=> exact ⟨h.weight _,lank_wt p _⟩
    | plus F V h hp h1 h2=>exact ⟨h1.1.more h2.1,lank_add h1.2 h2.2⟩
lemma Via.none : Via G k (0:W→Tale G):= by
    refine (show (fun _ : W=> (0:ℝ) • (0:Tale G)) =0 from funext fun _=>smul_zero _) ▸?_; exact Via.head _ Stone.zero lank_zero _ continuous_const
lemma Via.scale (a:ℝ){H:W→Tale G}(hp:Via G k H): Via G k (a • H) := by
    induction hp with
    | head H h p g he=> rw [show (a • (fun i:W=>g i • H))=(fun i=> (a*g i) • H) from funext fun i=> smul_smul a (g i) H]; exact Via.head _ h p _ (continuous_const.mul he)
    | plus P Q h hV ih ik=> rw [smul_add]; exact Via.plus _ _ ih ik
lemma Via.sum {F:I→W→Tale G}(s:Finset I)(hp:∀ i∈s, Via G k (F i)): Via G k (fun i=> ∑ j∈s,F j i) := by
   induction s using Finset.induction_on with
   | empty=> simp only [sum_empty]; exact Via.none
   | insert i s hi ih=> simp only [sum_insert hi]; exact Via.plus (F i) (fun i=>∑ j∈s,F j i) (hp _ (mem_insert_self ..)) (ih (fun j hj=>hp j (mem_insert_of_mem hj)))
lemma Via.moves {F:W→ Tale G}(hp:Via G k F)(z:Cover) : Via G k (fun i=> Town.season z (F i)):= by
   induction hp with
   | head F h p g he=> simp only [season_scale]; exact Via.head _ (h.transport _) (pinning p z) _ he
   | plus F V h hV ih ik=> exact Via.plus (fun i=> Town.season z (F i)) _ ih ik
lemma Via.inscription {F:W→Tale G}{P:StripU G L}(hp:Via G k F)(z:Site L)(he:Fair P): Via G k (fun i=>inscribed k P z (F i)):= by
   induction hp with
   | head F h p g hv=> simp only [fun v=> inscription_sc z (g v) h he]; exact Via.head _ (inscribe_law z he h) (inscription_L he z p h) _ hv
   | plus F V h hV ih ik=>
      rw [show (fun i=>inscribed k P z ((F+V) i))=(fun i=>inscribed k P z (F i))+(fun i=>inscribed k P z (V i)) from funext fun i=>inscription_add z (stead h i|>.1) (stead hV i|>.1) he]; exact Via.plus _ _ ih ik
lemma Via.product {F V:W→ Tale G}(hF:Via G k F)(hV:Via G j V): Via G (k+j) (fun i=> gust (F i) (V i)) := by
   induction hF with
   | head F h p g he=>
     induction hV with
     | head V hv hw f ha=>
         rw [show (fun i=> gust ((fun i=> g i • F) i) ((fun i=> f i • V) i))=(fun i=>(f i*g i) • gust F V) from ?_]; · exact Via.head _ (wind h hv) (polish_chart p hw) _ (ha.mul he)
         funext i; dsimp only; rw [gust_same (h.weight _) (hv.weight _), swell_w hv (h.weight _),gust_same hv (h.weight _),swell_w h hv,smul_smul]
     | plus V H hv hw ih ik=>
         refine cast (congr_arg (Via G (k+j)) ?_) (Via.plus _ _ ih ik); funext i; have hV:= stead hv i|>.1; have hW:= stead hw i|>.1; symm; change gust (g i • F) (V i+H i)=gust (g i • F) (V i) + gust (g i • F) (H i); rw [gust_same (h.weight _) (hV.more hW),swell_left hV hW (h.weight _),gust_same hV (h.weight _),gust_same hW (h.weight _)]
   | plus F P h hp ih ik=>
     refine cast (congr_arg (Via G (k+j)) ?_) (Via.plus _ _ ih ik); funext i; exact Eq.symm (swell_left (stead h i|>.1) (stead hp i|>.1) (stead hV i|>.1))
lemma coolU : Lank (spine_one α):= by
   intro i r; by_cases h: i+r=0
   ·
     rw [show r=0 by omega]; intro k; refine ⟨_, budget_finite ?_ le_rfl⟩; exact fun i=>mul_nonneg (mint_pos _ _ _ _) (norm_nonneg _)
   unfold spine_one; rw [if_neg h]; exact polished_zero ℝ α r
lemma Via.service {u:List I}{F:I→W→Tale G}{a:I→ℕ} (h:∀ i∈u, Via G (a i) (F i)): Via G (loadᵣ a u) (fun t=>castF (fun i=>F i t) u):= by
   induction u with
   | nil=>
     convert Via.head (spine_one (Loc G 1)) (stone_start G) coolU (fun _:W=>1) continuous_const using 1
     · rfl
     funext i; unfold castF; simp
   | cons i s ih=> exact (h _ List.mem_cons_self).product (ih fun j hj=>h j (List.mem_cons_of_mem _ hj))
end scene
end YM.RG08.Harvest
