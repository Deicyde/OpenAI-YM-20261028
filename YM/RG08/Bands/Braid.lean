import YM.RG08.Town.Plaine
/-!
# Cover braid with all scalar and canonical companions
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
variable {I α:Type}{m c f:Side}{r s j n k E ε τ:ℕ}{η A B:ℝ}
section algebra
def aboardB (w:Beads α r× Beads α s): Beads α (r+s):= Fin.append w.1 w.2
def interU (F:Rooted ℝ α r)(V:Rooted ℝ α s)(w:Beads α r×Beads α s):=F w.1*V w.2
def braidV (F:Rooted ℝ α r)(V:Rooted ℝ α s):=sew (tub (interU F V) aboardB)
variable {U:Rooted ℝ α r}{V:Rooted ℝ α s}{u v : Spine ℝ α}{F Q: Screed ℝ α}
lemma inter_pens (h:Pens U)(e:Pens V): Pens (interU U V) := (summable_mul_of_summable_norm h e).norm
lemma braid_tid (h:Pens U)(he:Pens V): Tidy (braidV U V):= Tidy.sewn ((inter_pens h he).pours _)
lemma braid_none : braidV (0:Rooted ℝ α r) V=0 := by unfold braidV; rw [show interU (0:Rooted ℝ α r) V=0 from funext fun i=> zero_mul _, show tub (0:Beads α r×Beads α s→ℝ) aboardB=0 from funext fun _=>tsum_zero]; simpa using sew_sub (x:=(0:Rooted ℝ α (r+s))) (y:=0)
lemma braid_no : braidV U (0:Rooted ℝ α s)=0:= by unfold braidV; rw [show interU U (0:Rooted ℝ α s)=0 from funext fun i=>mul_zero _,show tub (0:Beads α r×Beads α s→ℝ) aboardB=0 from funext fun _=>tsum_zero]; simpa using sew_sub (x:=(0:Rooted ℝ α (r+s))) (y:=0)
lemma braid_pol (h:cis k η U A)(he:cis k η V B)(hp:0≤η): cis k η (braidV U V) (A*B):= by
  refine sew_cis (Ink.pour aboardB (p:=interU U V) ?_ (tailp hp)) hp
  apply budget_mono (f:=fun w:Beads α r ×Beads α s=> (tailP k η w.1*tailP k η w.2)*‖interU U V w‖) ?_ (fun i=> mul_nonneg (zero_le_one.trans (tailp hp _)) (norm_nonneg _)) (fun i=>mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)); rotate_left
  · dsimp only [Function.comp_apply,tailP]; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); rw [show girth (aboardB i)=girth i.1+girth i.2 from ?_,Nat.cast_add]; swap; · unfold girth aboardB; rw [Fin.sum_univ_add]; simp [Fin.append]
    nlinarith only [show 0≤η*(girth i.1:ℝ)*(η*(girth i.2:ℝ)) by positivity]
  have ht:= budget_prod h he; refine (budget_mono ht (fun i=>mul_nonneg (mul_nonneg (zero_le_one.trans (tailp hp _)) (zero_le_one.trans (tailp hp _))) (norm_nonneg _)) fun i=>le_of_eq ?_)
  unfold interU; rw [norm_mul]; exact mul_mul_mul_comm ..
-- Finite valence arity cost exact same centered norm.
def spoolB (u v : Spine ℝ α) (r:ℕ) : Rooted ℝ α r := ∑ p∈wheel r, grant r (braidV (u p.1) (v p.2))
structure Loomed (k:ℕ)(p:Spine ℝ α):Prop where
   tide : ∀ i,Tidy (p i)
   budget : ∀ i,k < i → p i=0
structure Sails (k:ℕ)(U:Screed ℝ α):Prop where
   tide : ∀ i j,Tidy (U i j)
   budget : Fits k U
lemma Loomed.rise (h:Loomed k v)(hp:k≤ E): Loomed E v:= ⟨h.tide,fun i hi=>h.budget _ (by omega)⟩
lemma Loomed.more (h:Loomed k u)(he:Loomed k v): Loomed k (u+v):= ⟨fun i=>(h.tide i).plus (he.tide i),fun i hi=>by rw [Pi.add_apply,h.budget i hi,he.budget i hi,add_zero]⟩
lemma Loomed.less (h:Loomed k u)(he:Loomed k v): Loomed k (u-v):= ⟨fun i=>(h.tide i).less (he.tide i),fun i hi=>by rw [Pi.sub_apply,h.budget i hi,he.budget i hi,sub_zero]⟩
lemma Loomed.sc (h:Loomed k u)(v:ℝ): Loomed k (v • u):=⟨fun i=>(h.tide i).scale _,fun i hi=>by rw [Pi.smul_apply,h.budget _ hi,smul_zero]⟩
lemma Loomed.zero : Loomed k (0:Spine ℝ α):= ⟨fun i=> Tidy.zero ..,fun _ _=>rfl⟩
lemma Loomed.sum {F:I→Spine ℝ α}{v:Finset I}(h:∀ i∈v,Loomed k (F i)): Loomed k (∑ i∈v,F i):= by
  induction v using Finset.induction_on with
  | empty=> rw [sum_empty]; exact Loomed.zero
  | insert i s hi ih=> rw [sum_insert hi]; exact (h i (mem_insert_self ..)).more (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma Sails.thin (h:Sails k F)(i): Loomed (k+i) (F i):=⟨h.tide i,fun j hi=> not_ne_iff.mp (mt (h.budget i j) (by omega))⟩
lemma swung (h:∀ i,Loomed (k+i) (F i)): Sails k F := ⟨fun i=>(h i).tide,fun i j hz=> le_of_not_gt (fun he=>hz ((h i).budget _ he))⟩
def gust (F Q : Screed ℝ α)(e :ℕ) : Spine ℝ α:= ∑ p∈wheel e,spoolB (F p.1) (Q p.2)
lemma braid_loom (h:Loomed n v)(he:Loomed k u): Loomed (n+k) (spoolB v u):= by
  refine ⟨fun i=> Tidy.additions (fun p (_:p∈wheel i)=> Tidied i (braid_tid ((h.tide p.1).pens) (he.tide p.2|>.pens))),fun i hi=>?_⟩
  refine sum_eq_zero (s:=wheel i) ?_; intro p hp; have hX:=mem_antidiagonal.mp hp; by_cases hk:n<p.1; · rw [h.budget p.1 hk,braid_none, grant_zero]
  rw [he.budget p.2 (by omega), braid_no, grant_zero]
lemma braid_s (h:Sails k F)(he:Sails n Q): Sails (k+n) (gust F Q):= swung fun i=> Loomed.sum fun p (hp:p∈wheel i)=> ((braid_loom (h.thin _) (he.thin _)).rise (E:=k+n+i) (by have ht:=mem_antidiagonal.mp hp; omega)) -- fix
variable [Fintype α] [DecidableEq α]
lemma join_song (h:Pens U)(hp:Pens V)(z:Site c): rootSong (braidV U V) c z=rootSong U c z*rootSong V c z:= by
   unfold braidV; rw [sew_diagonal ((inter_pens h hp).pours _)]
   funext x; simp_rw [Pi.mul_apply,rootSong,Tensor.diagonal]; rw [st_tub _ _ (inter_pens h hp), stitch_apply h.of_norm,stitch_apply hp.of_norm, tsum_mul_tsum_of_summable_norm (bead_summable _ _ h.of_norm _).norm (bead_summable _ _ hp.of_norm _).norm]; apply tsum_congr; intro b; unfold rosary aboardB interU; rw [Fin.prod_univ_add,mul_mul_mul_comm]; congr 2 <;> simp [silks]
lemma spire_s (h:Loomed n v)(he:Loomed k u)(o:Site c): large o (n+k) (spoolB v u)=large o n v*large o k u:= by
   unfold large; rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]; symm
   rw [triangle_sum (fun i j=> rootSong (v i) c o* rootSong (u j) c o) n k]; swap
   · intro i j hp; constructor
     · by_contra hh; exact hp (by rw [h.budget i (by omega),root_zero,zero_mul])
     by_contra hh; exact hp (by rw [he.budget j (by omega),root_zero,mul_zero])
   refine sum_congr rfl fun i hi=> ?_; rw [spoolB,root_sum o (h:=fun p _ => (Tidied i (braid_tid (h.tide _|>.pens) (he.tide _|>.pens))).pens)]
   refine sum_congr rfl fun p hp=> ?_; rw [← mem_antidiagonal.mp hp,grant_self,join_song (h.tide _|>.pens) (he.tide _|>.pens)]
lemma larger_s (h:Loomed j u)(hp:j ≤ k)(o:Site c): large o j u= large o k u:= sum_subset (range_mono (by omega : j+1 ≤ k+1)) fun i hi hx=> by unfold rootSong; rw [h.budget i (by have he:=mt mem_range_succ_iff.mpr hx; omega),st_zero]; rfl
lemma spool_group (w:Finset I){F:I→ Spine ℝ α}(h:∀ i∈w,Loomed k (F i))(p:Site c): large p k (∑ i∈w,F i)=∑ i∈w, large p k (F i):= by unfold large; simp_rw [Finset.sum_apply,root_sum p w (h:=fun i hi=> ((h i hi).tide _).pens)]; rw [sum_comm]
lemma spool_more (h:Loomed k u)(hp:Loomed k v)(o:Site c): large o k (u+v)= large o k u+large o k v:= by unfold large; simp_rw [Pi.add_apply,fun i=>root_plus o ((h.tide i).pens) (hp.tide i|>.pens)]; rw [sum_add_distrib] -- use explicit
lemma sing_k (h:Sails k F)(hp:Sails n Q)(o:Site c)(i:ℕ): large o (k+n+i) (gust F Q i)= billow (fun i=>large o (k+i) (F i)) (fun i=>large o (n+i) (Q i)) i:= by
   have hx (p)(hp:p∈wheel i): k+n+i= k+p.1 + (n+p.2):= by have he:= mem_antidiagonal.mp hp; omega
   unfold gust billow; refine (spool_group (k:=k+n+i) (F:=fun (p:ℕ×ℕ)=>spoolB (F p.1) (Q p.2)) _ (fun i hi=> (braid_loom (h.thin i.1) (hp.thin i.2)).rise ((hx i hi).ge)) o).trans (sum_congr rfl fun p hp'=>?_); rw [hx p hp', spire_s (h.thin p.1) (hp.thin p.2)]
end algebra
section ward
variable {G:Gauge}{F V:Tale G}
lemma sails_from (h: Stone k F): Sails k F:= ⟨h.tidy,h.cap⟩
lemma wind (h: Stone k F)(hp:Stone j V) : Stone (k+j) (gust F V):= by
  have ht:=sails_from h; have hT:= sails_from hp; have hh:=braid_s ht hT
  refine ⟨hh.tide,hh.budget,fun c o a b ha hb hv n=> ?_⟩
  let P (v:ℝ→Link G c) i:= large o (k+i) (F i)∘v; let Q (v:ℝ→Link G c) i:= large o (j+i) (V i)∘v
  have hx (h : ℝ→ Link G c):arco c (fun e=> large o (k+j+e) (gust F V e)) h n=year (Zone.mul (P h) (Q h)) n:= by
    unfold arco; simp_rw [sing_k ht hT]; congr 1; funext i t; unfold Zone.mul billow; simp_rw [Finset.sum_apply]; rfl
  let U' v := year (P v) n; let V' v:= year (Q v) n
  have he(v: ℝ→Link G c)(he:ContinuousAt v 0)(u: Spine ℝ (Loc G 1))(j): Bill 0 (large o j u∘v):= life_price (((large_smooth _ _).continuous.continuousAt.comp he).mono_left nhdsWithin_le_nhds)
  have hy v (ht:ContinuousAt v 0) : Fit (n+1) (U' v* V' v) (year (Zone.mul (P v) (Q v)) n):= year_mult (fun i=> he v ht _ _) (fun i=> he v ht _ _) n
  let A := h.shore c o a b ha hb hv n; let B:=hp.shore c o a b ha hb hv n
  have hL : Fit (n+1) (U' a*V' a) (U' b*V' b):= (show Fit _ (U' a) (U' b) from A).groups B (year_bills (fun i=> he b hb.continuousAt _ _) n) (year_bills (fun i=> he b hb.continuousAt _ _) n)
  dsimp only; rw [hx,hx]; exact (hy _ ha.continuousAt|>.turn).join (hL.join (hy _ hb.continuousAt))
end ward
end YM.RG08.Bands
