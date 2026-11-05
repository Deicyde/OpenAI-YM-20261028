import YM.RG08.Bands.Pung
/-!
# Exact thermal birth branch with charge even on infinite cover
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
variable {I α:Type} [Fintype α]{r s:ℕ}{c:Side}{m:ℕ→Side}{K:Row α α}{p:Option Side}{A B C η:ℝ}
def Tips (F:ℕ→HeatS α)(G:HeatS α):Prop := ∀ i j r, Hurled (fun z=> F z i j r) (G i j r)
variable {F Q:ℕ→HeatS α}{U V:HeatS α}{u:List I}
section tips
lemma tips_more (h:Tips F U)(hp: Tips Q V): Tips (F+Q) (U+V):= fun i j r=>(h i j r).plus (hp i j r)
lemma tips_sub (h:Tips F U)(hp:Tips Q V):Tips (F-Q) (U-V):= by rw [sub_eq_add_neg,sub_eq_add_neg,← neg_one_smul ℝ V,←neg_one_smul ℝ Q]; exact tips_more h (fun i j r=>(hp i j r).scale _)
lemma tips_b (h:Tips F U)(hp: Tips Q V): Tips (fun i=>borne (F i) (Q i)) (borne U V) := by
   intro i j r; unfold borne; simp_rw [Finset.sum_apply]
   refine Hurled.additions (wheel i) (fun b hb=> ?_); unfold gust; simp_rw [Finset.sum_apply]; exact Hurled.additions (wheel j) fun a ha=> Hurled.additions (wheel r) fun v hv=> Hurled.granting (windB (h _ _ _) (hp _ _ _)) r
lemma tips_t (h:Tips F U)(hp:Tips Q V)(he:Whole K)(hm:Tendsto (fun i=>(m i).val) atTop atTop):Tips (fun i=>thunder (some (m i)) K (F i) (Q i)) (thunder none K U V):= by intro i j r; unfold thunder; simp_rw [Finset.sum_apply]; exact Hurled.additions (wheel i) fun p hp'=> Hurled.additions (wheel j) fun v hv=> Hurled.additions (wheel r) fun v hv=> Hurled.granting (legs_move (h _ _ _) (hp _ _ _) hm he) r
variable {f:I→ ℕ→ HeatS α}{v:I→ HeatS α}{S: Canticle α}
lemma tips_none (k:ℕ)(h:Reels k U) : Tips (fun _=>U) U:= fun i j r=> Hurled.fixed (h i|>.tide j r|>.pens)
lemma tips_z (h:∀ i∈u, Tips (f i) (v i)): Tips (fun j=> castM (fun i=> f i j) u) (castM v u):= by
    induction u with
    | nil=> exact tips_none 0 reels_start
    | cons b u ih=> exact tips_b (h b List.mem_cons_self) (ih fun j hj=> h j (List.mem_cons_of_mem _ hj))
lemma tips_j (h:∀ i∈u, Tips (f i) (v i))(hx: Tips F U)(he:Whole K)(hm:Tendsto (fun i=>(m i).val) atTop atTop): Tips (fun j=>junction (some (m j)) K (fun i=>f i j) (F j) u) (junction none K v U u) := by
    induction u with
    | nil=> simp_rw [junction]; exact tips_none 0 Reels.none
    | cons b u ih=>
      have hp i hi:= h i (List.mem_cons_of_mem (l:=u) b hi); have ht:=h b List.mem_cons_self
      simp_rw [junction]; exact tips_more (F:=fun i=>_) (Q:=fun i=>_) (tips_b (tips_t hx ht he hm) (tips_z hp)) (tips_b ht (ih hp))
lemma tips_p (h:∀ i∈u,Tips (f i) (v i))(he:Whole K)(hm:Tendsto (fun i=>(m i).val) atTop atTop): Tips (fun j=>pullG (some (m j)) K (fun i=>f i j) u) (pullG none K v u) := by
    induction u with
    | nil=> simp_rw [pullG]; exact tips_none 0 Reels.none
    | cons b u ih=>
      have hp i hi := h i (List.mem_cons_of_mem (l:=u) b hi); have ht:=h b List.mem_cons_self
      simp_rw [pullG]; exact tips_more (F:=fun i=>_) (Q:=fun i=>_) (tips_j hp ht he hm) (tips_b ht (ih hp))
lemma tips_peel (hp:Whole K)(ht:Gets S)(hm:Tendsto (fun i=>(m i).val) atTop atTop)(h:Tips F U): Tips (fun i=>pumpP (some (m i)) K S (F i)) (pumpP none K S U):= by
    refine tips_more (F:=fun i=> _) (Q:=fun i=> _) (fun i j r=> (h i j _).jib_l m hp hm) (fun i j r=>?_)
    unfold choirR; simp_rw [Finset.sum_apply]; refine Hurled.additions (wheel i) fun p hp'=> Hurled.additions (wheel j) fun v hv=> Hurled.additions (wheel r) fun u hu=> Hurled.granting ((h _ _ _).clasp_l (Mending.both (fun i j=> Mending.one (S i j) (ht.2 i j|>.2)) hp hm p.2 v.2 _) hp) r
end tips
section arrives
variable {F:ℕ→Shale α r}{f:Shale α r}
private lemma caps_u (c:Side)(v:Site c)(h:Quire.Lit f 0 A)(b:Fin r→ PAC α c): ‖stitch f c v b‖ ≤ A*∏ j, ‖b j‖:= by
   have hh:=h.pens (ling_one le_rfl); rw [stitch_apply hh.of_norm]; let f' j:=f j*rosary b v j; have ht : Summable f':= bead_summable f b hh.of_norm v
   apply (norm_tsum_le_tsum_norm ht.norm).trans
   apply (Summable.tsum_le_tsum (g:=fun i=> ‖f i‖*∏ j, ‖b j‖) ?_ ht.norm (hh.mul_right _)).trans
   · unfold Quire.Lit Quire.Ink at h; simp only [ling,zero_mul,Real.exp_zero,one_mul] at h; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h.2.2 (by positivity)
   intro i; unfold f'; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (rosary_bill ..) (norm_nonneg _)
-- May choose exact Classical.decEq
lemma unfurl (h: Hurled F f)(ht:Tidy f)(he:Tendsto (fun i=>(m i).val) atTop atTop) (b:Beads α r) : Tendsto (fun i=> stitch (F i) (m i) (0:Site (m i)) (fun j=> Pi.single (silks (0:Site (m i)) b j) 1)) atTop (𝓝 (f b)):= by
   let x (i:ℕ)(j:Fin r): PAC α (m i):= Pi.single (silks (0:Site (m i)) b j) 1; let u i:= stitch (F i-f) (m i) 0 (x i)
   have hp i j: ‖x i j‖≤1:= (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun k=> by simp only [x,Pi.single_apply]; split <;> simp)
   obtain ⟨p,hp',H⟩:=h.moment.thus
   have ha i : ‖u i‖≤p i:= by
      refine (caps_u _ _ (H i) (x i)).trans (mul_le_of_le_one_right (Ink.nonneg (H i)) ?_)
      calc
        _≤∏ _ :Fin r,(1:ℝ):= Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> hp i j)
        _=_:=by simp
   have hh : Tendsto u atTop (𝓝 0):= squeeze_zero_norm ha hp'
   convert (show Tendsto (u+fun i=>stitch f (m i) 0 (x i)) atTop (𝓝 _) from hh.add (ht.shale_limit m he b)) using 1
   · funext i; rw [Pi.add_apply]; unfold u; rw [st_sub (h.ever i|>.of_norm) h.old.of_norm,_root_.sub_apply,sub_add_cancel]
   rw [zero_add]
lemma relic {F W:ℕ→ HeatS α}{U V:HeatS α}(hF:Tips F U)(hU:Reels r U)(hW:Tips W V)(hp:Reels r V)(hx:∀ i,Reels r (F i))(ht:∀ i, Reels r (W i))(hm:Tendsto (fun i=>(m i).val) atTop atTop)(he:∀ i,glee r (0:Site (m i)) (F i)=glee r 0 (W i)): U=V:= by
   funext n e r b; apply tendsto_nhds_unique_of_eventuallyEq (unfurl (hF n e r) ((hU n).tide _ _) hm b) (unfurl (hW n e r) ((hp n).tide _ _) hm b) (Eventually.of_forall (fun i=>?_))
   exact DFunLike.congr_fun (Tensor.ext_diag _ _ (((hx i n).tide e r).sym _) (((ht i n).tide e r).sym _) (glee_stanza (hx i) (ht i) _ (he i) n e r)) _
end arrives
end YM.RG08.Bands
