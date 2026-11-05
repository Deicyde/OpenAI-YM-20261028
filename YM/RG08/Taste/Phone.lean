import YM.RG08.Run.Eclog
/-!
# Tape counted fronts; projection fees and returned vectors. True positions
- vectors always used at coordinates declared with actual frame witness.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Taste
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J:Type} {u:I→Windows}{w:J→ShoreP u} {n k m l:ℕ}
-- match higher wing, and original. formulas invariant in actual supports.
structure Offer (w:J→ShoreP u) where
  N : J→ℕ
  M : J→ℕ
  bigger a : (w a).next.i ≤ N a
  past : N ≤ M
variable (b:Offer w)
def Offer.part (i:Wall w n): Wings u n:= ⟨i.world.toLaunch,b.N i.a,b.M i.a,i.last.trans (b.bigger i.a),b.past _⟩
variable (w)
def offerD : Offer w := ⟨fun i=> (w i).next.N,fun i=>(w i).next.M,fun i=>(w i).next.cut, fun i=>(w i).next.side⟩
def offerF : Offer w:= ⟨fun i=>(w i).next.M,fun i=>(w i).next.M, fun i=>(w i).next.cut.trans ((w i).next.side),le_rfl⟩
variable {w}
example (t:Wall w n): (offerD w).part t=t.world:=rfl
example : (offerF w).part=wallR:=rfl
-- `Pages` indices relative to low on current tape.
section
variable (t:Wall w 0)
def foothold : Wall w 0:=⟨t.a,(w t.a).low,le_rfl,(w t.a).init⟩
def raceL : ℕ:= t.i-(w t.a).low
lemma raceH : (w t.a).low+raceL t=t.i := by unfold raceL; have he:=t.first; omega
lemma raceUp (i:Wall w 1): raceL i.roof=raceL i.low + 1:= by unfold raceL; change i.i+1 - (w i.a).low = i.i-(w i.a).low+1; have ht:=i.first; omega
-- copy/order not pruning horizon. debt bases at coarse are always relative to $w t$ master.
def spawn (n:ℕ)(h:n<raceL t): Wall w 1:= ⟨t.a,(w t.a).low+n,Nat.le_add_right .., le_trans (by have he:=raceH t; omega : _+1≤t.i) t.last⟩
lemma spawned (n:ℕ)(h:n<raceL t) : raceL (spawn t n h).low=n:= by unfold spawn Wall.low raceL; simp
lemma spawn_same (z:Wall w 1) (h: k < raceL z.low) : spawn z.low k h=spawn z.roof k (lt_trans h (by rw [raceUp]; omega)):= rfl
lemma spawn_tip (t:Wall w 1) : spawn t.roof (raceL t.low) (by rw [raceUp]; omega)=t:= by
   obtain ⟨a,i,h,hp⟩:=t; unfold spawn Wall.roof Wall.low; dsimp only; congr 1; exact raceH (w:=w) ⟨a,i,h,le_trans (Nat.le_succ _) hp⟩
-- budgets indexed by all roots/residue relationships
abbrev Stem (w:J→ShoreP u) := DeckSeat (raceL (w:=w)) 1
abbrev inside (i: Stem w): Wall w 1:= spawn i.i i.k i.hw
def fragment (i:Stem w): ShoreP u:=
  ⟨⟨i.i.world,(w i.i.a).next.fromK,(w i.i.a).next.ends⟩,(inside i).i,
     show (w i.i.a).low+i.k≤ i.i.i by have he:= raceH i.i; have ht:=i.hw; omega,(inside i).world.geC⟩
lemma tiprace (i:Stem w): i.i.i-(inside i).i=(fragment i).city:=rfl
variable (X:Chain)
lemma along_roof (i:Stem w): (inside i).low.i ≤ i.i.i := (fragment i).init
lemma race_a (i :Stem w): (fragment i).y X ≤ wallY X i.i:= by
    unfold Pill.ShoreP.y; unfold wallY
    refine max_le ?_ ?_
    · exact src_cost _ X _ rfl (inside i).first ((along_roof i).trans i.i.last)
    exact src_cost _ X _ rfl i.i.first i.i.last
lemma race_b (i:Stem w): (fragment i).rate X ≤ tiltP X i.i:= by
   let x:=i.i; unfold tiltP Pill.ShoreP.rate; apply Real.exp_monotone
   have hm:(fragment i).next.i ≤ (w i.i.a).next.i:=x.last
   have ht:(fragment i).next.main=(w i.i.a).next.main:= rfl
   have he:= age_scale_mono X.S (max_le_max hm ht.le); have hv:(fragment i).next.N=(w i.i.a).next.N:=rfl; rw [hv]; linarith
lemma race_c : Weighed (wallY X (b:=w) (n:=0)) (fun i:Wall w 0=> (raceL i:ℝ)):= by
    have hv:Weighed (wallY X (n:=0)) (fun i: Wall w 0=> ((w i.a).city:ℝ)):= (subsegment X).transfer (fun i:Wall w 0=> w i.a)
    exact hv.mono (fun _=>Nat.cast_nonneg _) (fun i=> Nat.cast_le.mpr (Nat.sub_le_sub_right i.last _))
end
section
variable {G:Gauge}{R:ℝ}{t d D e r:ℕ}{P:Side}{F:Labels.Frame G d}
lemma edge_crew (V:ReadsU F D R)(p:Native (Letter F))(h:Boards V)(he:d≤t): Marvel t (edgeBook V p) ∧ Lank (edgeBook V p):= by
    constructor
    · exact across_b (fun i=>⟨_,edge_marks V _ i,choir_array _ fun a _ => choir_array (τ:=t) _ fun j _=> choir_weight (stemmed (h.rank a) ((slot_le a).trans (he.trans (Nat.le_add_right ..)))) _⟩)
    intro e k; rw [edge_marks V p e e le_rfl]; exact (lank_tbl (fun i _=>lank_tbl (X:=fun j=>PowerSeries.coeff j (p i) • fem j (V i)) (fun _ _=> lank_wt (lank_fee (h.paid i) _) _))) e k
lemma edge_more (V:ReadsU F D R)(p q:Native (Letter F)): edgeBook V (p-q)=edgeBook V p-edgeBook V q:= by
    ext1 i; ext1 j; rw [Pi.sub_apply,Pi.sub_apply]; simp_rw [accounting, Pi.sub_apply,map_sub]; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro k _; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun n _=> _root_.sub_smul (coeff n (p k)) (coeff n (q k)) (V k (i-n) j)
lemma edge_none (V:ReadsU F D R): edgeBook V 0=0:= by have he:=edge_more V 0 0; rw [sub_zero,sub_self] at he; exact he
lemma edge_plus (V:ReadsU F D R)(p q:Native (Letter F)): edgeBook V (p+q)=edgeBook V p+edgeBook V q:= by
    apply sub_eq_iff_eq_add.mp; rw [← edge_more, add_sub_cancel_right] -- lemma name?
lemma lemma_fewer {P : Side}{Q:StripU G P}(h:Fair Q)(hR:1/2≤R){U V:BoardU D R G}(he:Marvel t U)(hp:Marvel t V): Needle.push Q t d (U-V)=Needle.push Q t d U-Needle.push Q t d V:= by
   have hx: Marvel t (U - V):= by rw [sub_eq_add_neg,← neg_one_smul ℝ]; exact choir_plus he (choir_weight hp _)
   have hP:= filop_plus (τ:=t) h.cm h.ct hx.cap hp.cap h.odds hx.hem hp.hem h.lived h.tune hR d
   unfold Needle.push; rw [sub_add_cancel] at hP; rw [show filop Q.cv Q.tree _ none t d (U-V)=_ from (eq_sub_of_add_eq hP.symm)]
   ext1 i; ext1 j; unfold Tall.hill; rw [Pi.sub_apply, Pi.sub_apply]; simp_rw [Pi.sub_apply,smul_sub, Finset.sum_sub_distrib]
lemma epoch_f (Q:StripU G P)(h:Fair Q)(hR:1/2≤R){U:BoardU D R G}(hp:Marvel t U)(d)(he:t≤n): Needle.push Q n d U=Needle.push Q t d U := by unfold Needle.push; rw [filop_epoch h.cm hp.cap h.odds hp.hem h.tune h.lived hR he]
end
end YM.RG08.Taste
