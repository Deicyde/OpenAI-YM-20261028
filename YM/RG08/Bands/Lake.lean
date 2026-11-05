import YM.RG08.Bands.Mantle
/-!
# Thermal stocks. Invariants in graded/tested scalar channels.
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
open scoped BigOperators Topology Real ContDiff Matrix.Norms.Frobenius
variable {I α:Type}{m c f:Side}{p:Option Side}{K:Row α α}{τ ε k E r n s:ℕ}
abbrev HeatS (α:Type) := ℕ→Screed ℝ α
def borne (U V: HeatS α)(n k:ℕ): Spine ℝ α := ∑ p∈wheel n,gust (U p.1) (V p.2) k
def thunder (p:Option Side)(K:Row α α)(U V:HeatS α)(n e:ℕ): Spine ℝ α:= ∑ b∈wheel n,∑ a∈wheel e, grail p K (U b.1 a.1) (V b.2 a.2)
-- time+arity filtration
def Reels (τ:ℕ)(X:HeatS α) : Prop:= ∀ i, Sails τ (X i)
def Last (τ:ℕ)(X:HeatS α):Prop:=∀ i j,windows τ j < i → X i j=0
variable {F:Screed ℝ α}{U V:HeatS α}
section span
lemma Loomed.fresh {U:Screed ℝ α}{k:ℕ} (h:Sails k U)(v): Sails k ((v:ℝ) • U):= swung fun i=> Loomed.sc (h.thin i) _
lemma Reels.none : Reels τ (0:HeatS α) := fun i=> swung fun j=> Loomed.zero
lemma Reels.sm (h:Reels τ U)(b:ℝ) : Reels τ (b • U):= fun i=> Loomed.fresh (h i) _
lemma Reels.more (h:Reels τ U)(he:Reels τ V): Reels τ (U+V) := fun i=>swung fun j=> ((h i).thin j).more ((he i).thin j)
lemma Reels.less (h:Reels τ U)(he:Reels τ V): Reels τ (U-V) := fun i=>swung fun j=> ((h i).thin j).less ((he i).thin j)
lemma borne_r (h:Reels τ U)(he:Reels ε V): Reels (τ+ε) (borne U V):= fun i=>swung fun j=> Loomed.sum fun p (_:p∈wheel i)=> (braid_s (h _) (he _)).thin j
lemma thunder_r (h:Reels τ U)(he:Reels ε V)(hp:Whole K): Reels (τ+ε) (thunder p K U V):= fun n=>swung fun e=>Loomed.sum fun b (_:b∈wheel n)=>Loomed.sum fun a ha=> by
  have hh:= mem_antidiagonal.mp ha; exact (grail_story (((h b.1).thin a.1).rise (Nat.le_succ _)) (((he b.2).thin a.2).rise (Nat.le_succ _)) hp).rise (by omega)
lemma short_pro {V:Screed ℝ α}(h:∀ i j,i+j>0→V i j=0)(hV:Tidy (V 0 0)): Sails 0 V:= swung fun i=>by
   constructor
   · intro j; by_cases ht:i+j>0; rw [h i j ht]; exact Tidy.zero ..
     obtain ⟨rfl,rfl⟩ : i=0 ∧ j=0:=by omega
     exact hV
   intro j hh; exact h _ _ (by omega)
lemma hull_tiny (z:Screed ℝ α) : Sails 0 z → Reels 0 (fun i=> if i=0 then z else 0) := fun h i=> by dsimp only; split; exact h; apply swung; exact fun i=> Loomed.zero
def spine_one (α:Type)(i j:ℕ): Rooted ℝ α j := if i+j=0 then fun _=>1 else 0
def upstart (α:Type)(i:ℕ) : Screed ℝ α:=if i=0 then spine_one α else 0
lemma sails_start : Sails 0 (spine_one α):= short_pro (fun i j h=> if_neg (ne_of_gt h)) ⟨by unfold Pens; exact ((hasSum_fintype _).summable),fun _ _=>rfl⟩
lemma reels_start : Reels 0 (upstart α):= hull_tiny _ sails_start
lemma borne_z : borne U V 0=gust (U 0) (V 0) := by funext i; simp only [borne,wheel,Nat.antidiagonal_zero,sum_singleton]
end span
section trip
variable [Fintype α] [DecidableEq α]
def glee (τ:ℕ)(o:Site c)(U:HeatS α): Op (Co c α) := fun i j=> large o (τ+j) (U i j)
lemma glee_sum {u v:Spine ℝ α}(h:Loomed k u)(hp:Loomed k v)(p:Site c) : large p k (u-v)=large p k u-large p k v:= eq_sub_of_add_eq (by rw [← spool_more (h.less hp) hp,sub_add_cancel]) -- k undecl
lemma glee_m (h:Reels τ U)(hz:Reels τ V)(o:Site c): glee τ o (U+V)=glee τ o U+glee τ o V:= funext fun i=>funext fun j=> spool_more ((h i).thin j) ((hz i).thin j) o
lemma glee_sub (h:Reels τ U)(hz:Reels τ V)(o:Site c): glee τ o (U-V)=glee τ o U-glee τ o V:= funext fun i=>funext fun j=> glee_sum ((h i).thin j) ((hz i).thin j) o
lemma glee_sway (h:Reels τ U)(o:Site c): Fluid (glee τ o U):= fun _ _=> large_smooth ..
lemma tempo_b (h:Reels τ U)(he:Reels ε V)(o:Site c): glee (τ+ε) o (borne U V)=dancing (glee τ o U) (glee ε o V):= by funext i j; unfold borne glee; rw [spool_group (k:=τ+ε+j) (p:=o) (F:=fun (b:ℕ×ℕ)=>gust (U b.1) (V b.2) j) _ (fun i _=> (braid_s (h i.1) (he i.2)).thin j)]; exact sum_congr rfl fun b _=> sing_k (h _) (he _) _ _
lemma tempo_h (h:Reels τ U)(he:Reels ε V)(hp:Whole K)(o:Site c): glee (τ+ε) o (thunder (some c) K U V)=rim (K.acts c) (glee τ o U) (glee ε o V):= by
   funext i j
   let W (u v:ℕ×ℕ):= grail (some c) K (U u.1 v.1) (V u.2 v.2)
   have hx (u v:ℕ×ℕ):= grail_story (p:=some c) (((h u.1).thin v.1).rise (Nat.le_succ _)) (((he u.2).thin v.2).rise (Nat.le_succ _)) hp
   have hh(u v)(hv:v∈wheel j):Loomed (τ+ε+j) (W u v):=(hx u v).rise (by have hk:=mem_antidiagonal.mp hv; omega)
   unfold rim glee
   refine Eq.trans (spool_group _ (F:=fun u=>∑ v∈wheel j,W u v) (fun i _=> Loomed.sum (hh i)) o) (sum_congr rfl fun b hb=>?_)
   rw [spool_group _ (hh b)]; refine sum_congr rfl fun v hv=>?_ ; have hk:= mem_antidiagonal.mp hv
   unfold W; rw [show τ+ε+j=τ+v.1+(ε+v.2) by omega, chorus_frame (((h b.1).thin v.1).rise (Nat.le_succ _)) (((he b.2).thin v.2).rise (Nat.le_succ _)) hp,← larger_s ((h b.1).thin v.1) (Nat.le_succ _),←larger_s ((he b.2).thin v.2) (Nat.le_succ _)]
private lemma notes_unit (p:Site c)(n:ℕ): large p n (0:Spine ℝ α)=0:= sum_eq_zero fun i _=> root_zero p
private lemma glider_zero (p:Site c): large p 0 ((spine_one α) 0)=1 := by
   rw [large,sum_eq_single_of_mem 0 (by simp), spine_one, if_pos (by omega)]
   · have ht : Summable (fun (_:Beads α 0)=> (1:ℝ)):=((hasSum_fintype _).summable)
     funext x; unfold rootSong Tensor.diagonal; rw [stitch_apply ht]; simp [rosary]
   intro i hi hk; simp only [mem_range_succ_iff,mem_singleton] at hi; omega
-- `ingr n e`
lemma glee_empty (α:Type)[Fintype α][DecidableEq α](p:Site c): glee 0 p (upstart α)=fun n i=> if n+i=0 then 1 else 0 := by
   funext n i; unfold glee; unfold upstart; split; next hp=>
     subst n; split; next hi=> rw [show i=0 by omega]; exact glider_zero p
     unfold large; simp only [spine_one]; refine sum_eq_zero fun v _=> ?_; rw [if_neg ?_,root_zero]
     omega
   next ht=>rw [if_neg (by omega)]; exact notes_unit p _
lemma glee_stanza (h:Reels τ U)(he:Reels τ V)(z:Site c)(hp: glee τ z U=glee τ z V)(i j r:ℕ) : rootSong (U i j r) c z=rootSong (V i j r) c z:= by
   by_cases hx:r ≤ τ+j
   · let L:= large (α:=α) z (τ+j); have hs : L (U i j)=L (V i j):= congr_fun (congr_fun hp i) j
     exact congr_arg Tensor.diagonal (((large_jet z _ (h i|>.tide j) hx).symm.trans (congr_arg (fun f=> Tensor.coeff f r 0) hs)).trans (large_jet _ _ ((he i).tide j) hx))
   rw [(h i|>.thin j).budget r (by omega),((he i).thin j).budget r (by omega)]
end trip
end YM.RG08.Bands
