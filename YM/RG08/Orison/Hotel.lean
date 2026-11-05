import YM.RG08.Orison.Falcon

/-! # Vault limit exactly after aggregate; frames commits transfer Ward & FPS
 to first unmatched. All diagrams rooted before limits. -/
noncomputable section
namespace YM.RG08.Orison
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen Rows
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {I J:Type}{k:ℕ}{n q r e:ℕ}{F:ℕ→Flake n (Market I)}{V:Flake n (Market I)}
/-- Commits a usable width per material. choose any common smaller for finite
 purchases below. -/
def Studio (F:ℕ→Flake n (Market I))(V:Flake n (Market I)):Prop:=∃ σ,0<σ∧ Tone F V σ
lemma Studio.sum (s:Finset J)(f:J→ℕ→Flake n (Market I))(g:J→Flake n (Market I))(he:∀ i∈s,Studio (f i) (g i)):Studio (fun i=>∑ j∈s,f j i) (∑ j∈s,g j):=by
 induction s using Finset.induction_on with
 | empty=>simp only [sum_empty];exact ⟨1,zero_lt_one,nil⟩
 | insert x s h hs=>
   obtain ⟨p,hp,H⟩:=hs fun i hi=>he i (mem_insert_of_mem hi)
   obtain ⟨v,hv,T⟩:=he x (mem_insert_self ..)
   simp only [sum_insert h];exact ⟨min v p,lt_min hv hp,(T.narrow (min_le_left ..)).add (H.narrow (min_le_right ..))⟩
lemma Studio.neg (h:Studio F V):Studio (fun i=> -F i) (-V):=by obtain ⟨p,hp,H⟩:=h; exact ⟨_,hp,H.neg⟩
lemma Studio.add {G:ℕ→Flake n (Market I)}{D:Flake n (Market I)}(h:Studio F V)(hp:Studio G D):Studio (fun i=>F i+G i) (V+D):=by obtain ⟨p,ht,H⟩:=h;obtain ⟨x,hx,h⟩:=hp;exact ⟨min p x,lt_min ht hx,(H.narrow (min_le_left ..)).add (h.narrow (min_le_right ..))⟩
variable {G:Gauge}{X:ℕ→Castle G}{Y:Castle G}{E:ℕ}{P:Patch}{K:KernelChoices}{Z:ChartRatio G} {h:P.Branches K G}
lemma Studio.castles (h:Shade E X Y){e k:ℕ}(he:e≤E)(hk:0<k):Studio (fun i=>demand (X i) e k) (demand Y e k):=by
 unfold demand; apply Studio.sum _ _ _ _;intro i hi;apply Studio.sum _ _ _ _;intro j _
 unfold RG08.Mount.flight
 split_ifs
 · obtain ⟨s,hs,d,hd,hT⟩:=h.cost i j (by simp only [mem_range] at hi;omega)
   have hx:=Ducat.composed (O:=ℕ) (w:=fun _=>s) (fun _=>hs) (tiny _ hd) hT (hush.steady _ (Ducat.poem_pos G j k s)) hk
   refine ⟨_,?_ ,d,hd,hx⟩;change 0 < trail j (fun _:ℕ=>s) 0;unfold Ducat.trail _root_.YM.RG08.Mount.rank;positivity
 exact ⟨1,zero_lt_one,nil⟩
lemma elevation {F:ℕ→Flake k (Market (Loc G 1))}{Y:Flake k (Market (Loc G 1))}(h:Studio F Y): Studio (fun i=>Cairn.box P (F i)) (Cairn.box P Y):=by
 obtain ⟨s,hs,d,hd,H⟩:=h; let t:=min 1 s;have ht:0<t:=lt_min zero_lt_one hs
 refine ⟨t,ht,d,hd,Ducat.box (O:=ℕ) (v:=fun _=>t) (fun _=>ht) (tiny _ hd) (fun _=>P) H (fun _=> (show t ≤ s from min_le_right ..).trans ?_) (fun _=>min_le_left ..)⟩
 exact le_mul_of_one_le_left hs.le (by exact_mod_cast P.L.property)
lemma Studio.ghosted (hT:Shade E X Y)(he:e≤E)(hk:0<k): Studio (fun i=> inlet h (X i) Z e k) (inlet h Y Z e k):=by
 unfold inlet; split_ifs;swap;exact ⟨1,zero_lt_one,nil⟩
 have hh:= elevation (P:=P) (Studio.castles (G:=G) hT he hk)
 let b:=bell h e k; let c:=dusk P Z e k
 have hb:Studio (fun _=>b) b:=by obtain ⟨p,q,hp,hq,H⟩:= bell_room h e k;exact ⟨_,hp,_,hush.zero,(Bound.join (I:=fun _=>Tack.Head P G) (O:=ℕ) (D:=hush) (w:=fun _=>_) ⟨fun _=>q,hush.steady _ hq,fun _=>H⟩)⟩
 have hc:Studio (fun _=>c) c:=by obtain ⟨p,q,hp,hq,H⟩:=dusk_room P Z e k;exact ⟨_,hp,_,hush.zero,(Bound.join (I:=fun _=>Tack.Head P G) (O:=ℕ) (D:=hush) (w:=fun _=>_) ⟨fun _=>q,hush.steady _ hq,fun _=>H⟩)⟩
 exact ((hh.add hb).neg).add hc
end YM.RG08.Orison
