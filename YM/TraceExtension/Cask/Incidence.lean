import YM.MergeProof.Vale

/-!
# The tagged-Haar change. Incidence of connected movements.

Overlap via a shifted marker is charged once even for powers of the
*same* long E label. A movement meeting unmodified flags is attached,
with full footprint, to **all** overlapping forced labels; movements with
no flags not so attached. (Hard core is not imposed on the latter.)
A forced vertex with movement permission has two supports,
for quote and for ORIGINAL hard core. All overlap rules here use BOTH.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker
open scoped Classical
variable {I V:Type*}[DecidableEq I][DecidableEq V]{n:Side}
-- strokes negative sign are ornaments. Sign of the Mobius coefficient lives in the ornaments, not in reconnection.
structure Staff (V I:Type*) (n:Side) where
 seat : V ↪ Site n
 cast : I→Finset V
 shop : I→ Prop
 foot : I → Support n
 pole : I → Support n -- empty for ornament and invitation
 flag : I → Support n
 books i x : x ∈ cast i→ seat x ∈ foot i
 purse i : pole i ⊆ foot i
 miss i : flag i ⊆ pole i
 needs i : (pole i).Nonempty → (flag i).Nonempty
 root i : (pole i).Nonempty ∨ (cast i).Nonempty
variable (P:Staff V I n)
abbrev sector : I→Support n:=fun i=> (P.cast i).image P.seat
abbrev cohorts := Ac.Parts (sector P)
abbrev hill (q:Finset I):= q.biUnion P.foot
abbrev crew (q:Finset I):= q.biUnion P.cast
abbrev gem (q:Finset I):= q.biUnion P.flag
lemma net (q:Finset I): q.biUnion (sector P)= (crew P q).image P.seat:=by ext; simp; grind
lemma fare (i:I) : sector P i⊆ P.foot i:=by intro x h; obtain ⟨k,hk,rfl⟩:= mem_image.mp h;exact P.books i k hk
lemma starred (q:Finset I) : (crew P q).image P.seat⊆hill P q:= by
    rw[← net]; intro x h; obtain ⟨k,hk,hu⟩:= mem_biUnion.mp h; exact mem_biUnion.mpr ⟨k,hk,fare P k hu⟩
lemma owns (q:Finset I) : gem P q⊆hill P q:=by
    intro x h; obtain ⟨k,hk,hu⟩:= mem_biUnion.mp h; exact mem_biUnion.mpr ⟨k,hk,P.purse k (P.miss k hu)⟩
lemma fest (i:I): (P.foot i).Nonempty:= (P.root i).elim (fun h=>h.mono (P.purse _)) (fun h=>(h.image _).mono (fare P i))
variable {q r s:Finset I}
structure Woven (q:Finset I) : Prop where
 actor (v): v∈crew P q→ (∃! i, i∈q ∧ v∈P.cast i∧P.shop i) -- at least one carrier
 host (v): v∈crew P q→ ∃ i, i∈q ∧ v∈P.cast i ∧ ¬ P.shop i
 pole : (q:Set I).PairwiseDisjoint P.pole
structure Ice (q:Finset I): Prop where
 sound : Woven P q
 force : Spark (sector P) q
 dry : gem P q=∅
structure Boat (q:Finset I): Prop where
 sound : Woven P q
 force : Spark P.foot q
 wet : (gem P q).Nonempty
abbrev Piece := Finset (Finset I)
def Glut (T:Support n) (q:Finset I):Prop:= ∀ i∈cohorts P q,¬ Disjoint (hill P i) T
structure Basic (T:Support n)(q:Finset I):Prop where
 formed : Woven P q
 complete : gem P q=T
 location i : i∈q→ P.pole i∩T=P.flag i
-- (ice,boat)
structure Haven (T:Support n)(i b:Finset (Finset I)):Prop where
 ice s : s∈i→ Ice P s ∧ Disjoint (hill P s) T
 boat s:s∈b→ Boat P s∧Glut P T s ∧ hill P s∩T=gem P s
 apart : ((i∪b:Finset _):Set (Finset I)).PairwiseDisjoint (crew P)
 spatial : (b:Set _).PairwiseDisjoint (hill P)
 flags : b.biUnion (gem P)=T
 lemma Ice.rises (h:Ice P q): (crew P q).Nonempty:=by
    obtain ⟨k,hk⟩:=h.force.1
    rcases P.root k with h'|⟨a,ha⟩
    · have hp:=P.needs k h'; obtain ⟨x,hx⟩:= hp; exact False.elim ((Nonempty.ne_empty ⟨x,(show x∈gem P q from mem_biUnion.mpr ⟨k,hk,hx⟩)⟩) h.dry)
    exact ⟨a,mem_biUnion.mpr ⟨k,hk,ha⟩⟩
lemma Ice.moving (h:Ice P q): Spark P.foot q:=by
   refine ⟨h.force.1,fun i hi j hj=> Relation.ReflTransGen.mono (r:=bonds (sector P) q) (p:=bonds P.foot q) ?_ i j (h.force.2 i hi j hj)⟩
   rintro a b ⟨h₀,h',x,hx,hy⟩; exact ⟨h₀,h',x,fare P a hx,fare P b hy⟩
variable {P}
lemma Woven.parts (H:Woven P q) {S:I→Support n}(hs: sector P≤ S)(h:r∈ Ac.Parts S q): Woven P r:=by
    have ht:= Ac.lives S q h
    have he v (hv:v∈crew P r) i (hi:i∈q)(hm:v∈P.cast i): i∈ r:=by
       obtain ⟨c,hc,hq⟩:=mem_biUnion.mp hv; rw[← Ac.contains S h c hc]; exact (Ac.bright S c i).mpr ⟨hi,.single ⟨ht.1 hc,hi,P.seat v,hs c (mem_image_of_mem _ hq),hs i (mem_image_of_mem _ hm)⟩⟩
    have hp : crew P r⊆ crew P q:=by intro x hx; obtain ⟨i,hi,x'⟩:= mem_biUnion.mp hx; exact mem_biUnion.mpr ⟨i,ht.1 hi,x'⟩
    refine ⟨fun v hv=>?_, fun v hv=>?_, H.pole.subset (coe_subset.mpr ht.1)⟩
    · obtain ⟨i,⟨hi,hi',hm⟩,hI⟩:=H.actor v (hp hv); exact ⟨i,⟨he v hv i hi hi',hi',hm⟩,fun j h=> hI j ⟨ht.1 h.1,h.2⟩⟩
    obtain ⟨i,hi,hi',hm⟩:=H.host v (hp hv); exact ⟨i,he v hv i hi hi',hi',hm⟩
private lemma live_le (h:q⊆r): hill P q ⊆ hill P r:=by intro x hx; obtain ⟨i,hi,h'⟩:=mem_biUnion.mp hx; exact mem_biUnion.mpr ⟨i,h hi,h'⟩
lemma Woven.union {i b:Finset (Finset I)} (hi:∀ s∈i,Ice P s) (hb:∀ s∈b, Boat P s)
    (hz:((i∪b:Finset _):Set (Finset I)).PairwiseDisjoint (crew P))(hl:(b:Set _).PairwiseDisjoint (hill P)): Woven P ((i∪b).biUnion id):=by
    let c:=i∪b; let A:=c.biUnion id
    have hw(s)(hs:s∈c): Woven P s:= (mem_union.mp hs).elim (fun h=>(hi s h).sound) (fun h=>(hb s h).sound)
    have hh (s) (hs:s∈c): s⊆A:=fun _ h=>mem_biUnion.mpr ⟨s,hs,h⟩
    have hy(v)(hv:v∈crew P A):∃ s∈c, v∈crew P s:=by
       obtain ⟨x,hx,hv'⟩:= mem_biUnion.mp hv; obtain ⟨s,hs,hx'⟩:=mem_biUnion.mp hx; exact ⟨s,hs,mem_biUnion.mpr ⟨x,hx',hv'⟩⟩
    refine ⟨fun v hv=> ?_,fun v hv=> ?_,fun x hx y hy hxy=> ?_⟩
    · obtain ⟨s,hs,hv'⟩:=hy v hv; obtain ⟨x,⟨hx,hx',hr⟩,hI⟩:=(hw s hs).actor v hv'
      refine ⟨x,⟨hh s hs hx,hx',hr⟩,fun j h=>?_⟩; obtain ⟨hj,hj',hz'⟩:=h; obtain ⟨m,hm,hj⟩:= mem_biUnion.mp hj; obtain rfl : m=s:= of_not_not fun ht=> disjoint_left.mp (hz hm hs ht) (mem_biUnion.mpr ⟨j,hj,hj'⟩) hv'; exact hI j ⟨hj,hj',hz'⟩
    · obtain ⟨s,hs,hv'⟩:=hy v hv; obtain ⟨x,hx,hx',hr⟩:=(hw s hs).host v hv'; exact ⟨x,hh s hs hx,hx',hr⟩
    change x∈A at hx; change y∈A at hy; obtain ⟨s,hs,hx⟩:= mem_biUnion.mp hx; obtain ⟨t,ht,hy⟩:= mem_biUnion.mp hy
    by_cases he:s=t
    · subst t; exact (hw s hs).pole hx hy hxy
    refine disjoint_left.mpr fun p hp h=> ?_
    have hm(s)(a)(hs:s∈c)(hx:a∈id s)(hp:p∈P.pole a): s∈ b:=(mem_union.mp hs).resolve_left (fun h'=> by
       obtain ⟨r,hr⟩:= P.needs a ⟨p,hp⟩; exact Nonempty.ne_empty ⟨r,mem_biUnion.mpr ⟨a,hx,hr⟩⟩ (hi s h').dry)
    exact disjoint_left.mp (hl (hm _ _ hs hx hp) (hm _ _ ht hy h) he) (mem_biUnion.mpr ⟨x,hx,P.purse x hp⟩) (mem_biUnion.mpr ⟨y,hy,P.purse y h⟩)
end YM.Trace.Cask
