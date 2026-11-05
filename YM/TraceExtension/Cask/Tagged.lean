import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra
import YM.TraceExtension.Cask.Holds
import YM.Overlay.Terminal
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker Extra.Trajectories Function
open scoped Classical
variable {I V:Type*}[DecidableEq I][DecidableEq V]{n:Side}[Fintype V]
abbrev Duel (V:Type*) := V×Bool
abbrev Twin (V:Type*)[DecidableEq V][Fintype V]:= Stock.census (Duel V)
def spanZ (v:Finset V): (Twin V).Mode:= ⟨v×ˢuniv,mem_univ _⟩
def shipP (v:Finset V)(a:ℂ):= Poly.send (spanZ v) a
lemma fitsZ {T:Finset I}{a:I→Finset V}: Extra.Trajectories.Fits (spanZ ∘ a) T↔(T:Set I).PairwiseDisjoint a:=by
    constructor
    · intro ⟨h,_⟩ j hj k hk hm; exact disjoint_left.mpr fun i hp hv=> disjoint_left.mp (h hj hk hm) (show (i,true)∈_ from mem_product.mpr ⟨hp,mem_univ true⟩) (mem_product.mpr ⟨hv,mem_univ true⟩)
    intro h; exact ⟨fun j hj k hk hm=> disjoint_left.mpr fun i hp hv=> disjoint_left.mp (h hj hk hm) (mem_product.mp hp).1 (mem_product.mp hv).1,mem_univ _⟩
lemma ship_sum (S:Finset I)(a:I→Finset V)(v:I→ℂ)(hp:(S:Set I).PairwiseDisjoint a): (∏ i∈S,shipP (a i) (v i))=shipP (S.biUnion a) (∏ i∈S,v i):=by
  unfold shipP; refine (tagged_prod (spanZ ∘ a) S (fitsZ.2 hp) v).trans ?_
  refine congr_arg (fun p => Poly.send p _) (Subtype.ext ?_); ext k; simp only[unionTag,comp_apply,spanZ,mem_biUnion,mem_product,mem_univ,true_and,and_true]
lemma ship_fits (S:Finset I)(a:I→Finset V)(v:I→ℂ)(hp:∏ i∈S,shipP (a i) (v i)≠0): (S:Set I).PairwiseDisjoint a:= fitsZ.mp (fits_of_tagged_prod (spanZ ∘ a) hp)
variable (P:Staff V I n)
abbrev Stiff := {s:Finset I// Ice P s}
abbrev Arch := {s:Finset I// Boat P s}
abbrev Pier (s:Arch P):Box n:= (hill P s.val,gem P s.val)
def blue (F:Finset I→ℂ) (T:Support n)(q:Finset I):= if Disjoint (hill P q) T then F q else 0
def red (F:Finset I→ℂ) (T:Support n)(q:Finset I):= if Glut P T q∧hill P q∩T=gem P q then F q else 0
def booth (F:Finset I→ℂ)(T:Support n)(a:Finset (Stiff P))(b:Finset (Arch P)):= (∏ i∈a,shipP (crew P i.val) (blue P F T i.val))*Packets.value (Pier P) (Pattern T) (fun i=> shipP (crew P i.val) (red P F T i.val)) b
variable {P}
def beadsP {D:Finset I→Prop}(p:Finset {s:Finset I// D s}):= p.image Subtype.val
variable (P)
lemma glass (a:Finset (Stiff P))(b: Finset (Arch P)): Disjoint (beadsP a) (beadsP b):=by
  refine disjoint_left.mpr fun s hs hx=>?_ ; obtain ⟨t,_,rfl⟩:= mem_image.mp hs; obtain ⟨p,_,hp⟩:= mem_image.mp hx; exact p.property.wet.ne_empty (hp.symm ▸ t.property.dry)
lemma pier_m (T:Support n)(b:Finset (Arch P)): Packets.selected (Pier P) (Pattern T) b ↔ (((beadsP b):Set _).PairwiseDisjoint (hill P) ∧ (beadsP b).biUnion (gem P)=T):= by
   rw [marked_pattern ..]; swap; exact fun i _=> i.property.wet.mono (owns ..)
   unfold beadsP; rw [image_biUnion]; refine and_congr ?_ Iff.rfl
   constructor
   · intro h i hi j hj hD; obtain ⟨v,hv,rfl⟩:=mem_image.mp hi; obtain ⟨w,hw,rfl⟩:=mem_image.mp hj; exact h hv hw fun hm=>hD (congr_arg _ hm)
   intro h i hi j hj hm; exact h (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) (fun H=>hm (Subtype.ext H))
variable {P}
variable {F:Finset I→ℂ}{T:Support n}{a:Finset (Stiff P)}{b:Finset (Arch P)}
abbrev dispel (a:Finset (Stiff P))(b:Finset (Arch P)):= (beadsP a)∪beadsP b
abbrev grab (a:Finset (Stiff P))(b:Finset (Arch P)):= bulk (beadsP a) (beadsP b)
def pink (F: Finset I→ℂ)(P:Staff V I n)(T:Support n)(q:Finset I):= if gem P q=∅ then blue P F T q else red P F T q
private lemma glass_val (hp:Packets.selected (Pier P) (Pattern T) b): booth P F T a b=∏ i∈dispel a b,shipP (crew P i) (pink F P T i):=by
   rw[booth,Packets.value,if_pos hp,dispel,prod_union (glass ..),beadsP,beadsP,prod_image Subtype.val_injective.injOn,prod_image Subtype.val_injective.injOn]; apply congr_arg₂ (·*·)
   · apply prod_congr rfl; intro i _; rw [pink,if_pos i.property.dry]
   apply prod_congr rfl;intro i _;rw [pink,if_neg i.property.wet.ne_empty]
lemma booth_up (H:booth P F T a b ≠0): Haven P T (beadsP a) (beadsP b):=by
   have hp:Packets.selected (Pier P) (Pattern T) b:= Classical.byContradiction fun h=> H (by simp [booth,Packets.value,h])
   obtain ⟨hq,hM⟩:= (pier_m ..).1 hp; rw [glass_val hp] at H; have hx(v)(hv:v∈dispel a b): pink F P T v ≠0:=fun h'=> H (prod_eq_zero hv (by simp [shipP,h']))
   refine ⟨fun s hs=> ?_,fun s hs=> ?_,ship_fits _ _ _ H,hq,hM⟩
   · obtain ⟨t,ht,rfl⟩:=mem_image.mp hs; have hb:= t.property; exact ⟨hb, Classical.byContradiction (fun h=> hx _ (mem_union_left _ (mem_image_of_mem _ ht)) (by simp [pink,hb.dry,blue,h]))⟩
   obtain ⟨t,ht,rfl⟩:= mem_image.mp hs; have hb:= t.property; exact ⟨hb,Classical.byContradiction (fun h=> hx _ (mem_union_right _ (mem_image_of_mem _ ht)) (by rw [pink,if_neg hb.wet.ne_empty,red,if_neg h]))⟩
lemma booth_shares (h:Haven P T (beadsP a) (beadsP b)): booth P F T a b=shipP (crew P (grab a b)) (∏ i∈dispel a b,F i):=by
   rw [glass_val ((pier_m ..).2 ⟨h.spatial,h.flags⟩),ship_sum _ _ _ h.apart]
   refine congr_arg₂ _ ?_ (prod_congr rfl (fun i hi=> ?_))
   · unfold grab crew bulk; rw [biUnion_biUnion]; rfl
   unfold pink; rcases mem_union.mp hi with H|H
   · rw [if_pos (h.ice i H).1.dry,blue,if_pos (h.ice i H).2]
   rw [if_neg (h.boat i H).1.wet.ne_empty,red,if_pos (h.boat i H).2]
end YM.Trace.Cask
