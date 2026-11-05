import YM.RG08.Redo.Keys
/-! # Unmarked -> Mark occurrence provider directly in regulator independent bulk. -/
noncomputable section
namespace YM.RG08.Redo
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Camera Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Function Jetty Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {O X:Type}{G:Gauge}(hg:G.Simple){K:KernelChoices}{Z:ChartRatio G}{P:O→Patch}{H:O→Yard G}(hp:∀ i,(P i).Branches K G)
local notation "C0"=>Ducat.SliceSide

def porter (C:C0 P H K Z)(i:O):Necks.Crew G (P i) K:= ⟨C.fine i,C.coarse i,hp i,C.letters i,Z,Nacre.torque (C.ample hp i) hg,Classical.choice (C.leaders i).1⟩
variable {W:Rate.Stair X}
variable {J:Mason.Charter W K Z} (C R:Pros J){e n k E:ℕ}{Δ:Mason.Run W→ℝ}
local notation "T0"=>Mason.Run W
local notation "D0"=>turnstile W
-- Uniform family of coupons at all k occurrences in mark, post at v=coarser unmarked E width or wider pay individual.
theorem groceries (hh:W.Admits)(he:Mason.Pair hg E C R)(hE:0<E)(he':Even E)(hz:e<E):
 let v:=needs J.warp E 0
 let Q i:=porter hg J.branch C.side i; let S i:=porter hg J.branch R.side i
 ;∃ d:Mason.Run W→ℝ,(D0).cheap d∧ (FairT (Γ:=J.patch) (K:=K) (G:=G) (D:=D0) C.side.fine R.side.fine v d)
 ∧ (∀ i k,taps 0 e 0 i k→ Lance (I:=fun i:Mason.Run W=>Tack.Head (J.patch i) G) D0 v d (fun j=> (Q j).move i k) (fun j=> (S j).move i k))
 ∧ ∀ i≤e,∀ j < i,∀ r:ℕ,Weigh D0 d (fun x=> Nacre.dues (Q x).wake j r i) (fun x=> Nacre.dues (S x).wake j r i):=by
 intro v Q S
 have ht:Live 0 E:=⟨Nat.zero_le _,by simpa⟩
 let hC:=he.one.tuition E 0 le_rfl ht hE
 obtain ⟨f,hf,H⟩:= he.armies E 0 le_rfl ht hE
 obtain ⟨p,hq,h⟩:=upkeep (E:=E) J.learn C.side.letters R.side.letters (fun i j hi hj=>⟨up hh (Mason.delivers hg C hh he.one hi hj).1,up hh (Mason.delivers hg R hh he.two hi hj).1, waved C R hh (pellets hg C R hh he hi hj).1⟩)
 obtain ⟨q,hu,h'⟩:=upkeep (E:=E) (coats J.warp) (C.side.ample J.branch) (R.side.ample J.branch) (fun i j hi hj=>⟨(Mason.delivers hg C hh he.one hi hj).2,(Mason.delivers hg R hh he.two hi hj).2,(pellets hg C R hh he hi hj).2⟩)
 let d(i:T0):=f i+p i+q i
 have hD:(D0).cheap d:=(D0).lasts _ _ ((D0).lasts _ _ hf hq) hu
 have hx(i):f i ≤ d i:=by unfold d;linarith only [tiny _ hq i,tiny _ hu i]
 have hs(i):p i ≤ d i:=by unfold d;linarith only [tiny _ hf i,tiny _ hu i]
 have hd(i):q i ≤ d i:=by unfold d;linarith only [tiny _ hf i,tiny _ hq i]
 have hp(i):0 ≤ d i:=tiny _ hD _
 refine ⟨d,hD,⟨downCost H.1 (fun _=>le_rfl) hx,downCost H.2 (fun _=>le_rfl) hx⟩,fun i k hV=>?_,fun i hi j hj r=>?_⟩
 · have hv:Book D0 C.side.letters R.side.letters J.learn d E 0:= fun i p hx=> Lance.vow (I:=Gear T0 G) (h i p (by have h:=hx.2;omega) hx.1) hs (fun _=>le_rfl)
   apply eligible_lane _ _ hC.loan.toQuarrying hv (fun i=>(C.side.bulbs i).ethos) (fun i=>(R.side.bulbs i).ethos) (fun i=>hp i)
   unfold Residual taps RG08.Mount.rank;unfold taps at hV;omega
 apply sizes (D:=D0) hp
 intro x hx hX
 let Q':=C.side.ample J.branch;let S':=R.side.ample J.branch
 have Hv:Ducat.Mount (r:=0) D0 (coats J.warp x 0) d (fun i=>Q' i 0 x) (fun i=>S' i 0 x):=by
    by_cases hv:Live 0 x
    · exact Lance.vow (I:=Gear T0 G) (h' x 0 (by omega) hv) hd (fun _=>le_rfl)
    have h1 (t:T0):Q' t 0 x=0:= (C.side.price hg J.branch x t).1.rests _ _ hv
    have h2 (t:T0):S' t 0 x=0:= (R.side.price hg J.branch x t).1.rests _ _ hv
    simp_rw [h1,h2];exact Ducat.zero D0 _ _
 apply metered hg (fun i=>show 0 < coats J.warp x 0 i from ((J.warp i).tag x 0).1) hp Hv

-- self-version with no nested larger construction when pair partner not supplied.
def identical (h:Mason.Vow hg E C):Mason.Pair hg E C C where
 one := h
 two := h
 harm e r he hr hq:=(h.tuition e r he hr hq).sure
 armies e r he hr hq:=⟨_,(D0).zero,(h.tuition e r he hr hq).fence⟩
 base:=⟨_,(kiosk W).zero,fun i=>by rw [sub_self];exact zero_held⟩
 baseC:=⟨_,(D0).zero,fun i=>by rw [sub_self];exact zero_held⟩
end YM.RG08.Redo

namespace YM.RG08.Redo
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Camera Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Function Jetty Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {O X:Type}{G:Gauge}(hg:G.Simple){K:KernelChoices}{Z:ChartRatio G}
variable {W:Rate.Stair X}{J:Mason.Charter W K Z} (C R:Pros J){e n k E:ℕ}
local notation "T0"=>Mason.Run W
local notation "D0"=>turnstile W
lemma lengths (hh:W.Admits):(D0).Good fun i:T0=>W.length i.x i.m:=by
 apply hh.mono; intro x i hj;rw [wide,stepOnly]; split_ifs with h hp hp -- active vs i<top? see
 · exact ⟨le_trans (by norm_num) (W.length_large x i),le_rfl⟩
 · have he:=h.2; contradiction
 all_goals constructor; exact le_rfl
 · linarith only [W.length_large x i]
 exact le_rfl
lemma positiveCheap:∃ g,(D0).cheap g∧∀ i:T0,0<g i:=by
 let a(x:T0):=(W.weight 1 x.x x.m)⁻¹
 refine ⟨a,⟨1,zero_lt_one,?_⟩,fun i=>inv_pos.mpr (W.weight_pos ..)⟩
 apply (Rate.Stair.Poly.constant W zero_le_one).mono
 intro x i _hi; change 0 ≤ wide a x i*W.weight 1 x i ∧ wide a x i*W.weight 1 x i ≤ _; rw [wide];split;next h=>simp [a,ne_of_gt (W.weight_pos 1 x i)]
 simp
lemma liftHeat {η δ p:ℝ}{Γ:Patch}{A B:Necks.Crew G Γ K}{d:ℕ}(h:Warmth η δ p e n d A B){q μ:ℝ}(hp:p ≤ q)(hz:δ ≤ μ): Warmth η μ q e n d A B:=by
 obtain ⟨he,hm,hk,hs⟩:=h;obtain ⟨hv,H,hK,hT,hY,hP,hS⟩:=hm
 have ht:p*δ ≤ q*μ:=mul_le_mul hp hz H (zero_le_one.trans (hv.trans hp))
 refine ⟨he,⟨hv.trans hp,H.trans hz,hK,hT,⟨wireBag hY.near hp,wireBag hY.far hp,wireBag hY.compare ht⟩,fun i=>alleyWiden (hP i) hp ht,fun i n hh=>?_⟩,hk.trans hp,fun i j r hi hh h'=>?_⟩
 · obtain ⟨h1,h2,h3,h4⟩:=hS _ _ hh;exact ⟨h1.trans hp,h2.mono le_rfl hp (fun _=>le_rfl),h3.mono le_rfl hp (fun _=>le_rfl),h4.mono le_rfl ht (fun _=>le_rfl)⟩
 obtain ⟨h1,h2,h3⟩:=hs i j r hi hh h';exact ⟨h1.trans hp,h2.trans hp,h3.trans ht⟩

lemma warmth (d r:ℕ)(hh:W.Admits)(he:Mason.Pair hg E C R)(hp:0<E)(hE:Even E)(hz:e<E){η:Mason.Run W→ℝ}(h:∀ i, 0<η i)(hη:∀ i, η i ≤ needs J.warp E 0 i):
 ∃ w δ,(D0).Good w∧(D0).cheap δ∧ ∀ i, 0 < δ i ∧ Warmth (η i) (δ i) (w i) e r d (porter hg J.branch C.side i) (porter hg J.branch R.side i):=by
 obtain ⟨v,hv,ht,hP,hC⟩:= groceries hg C R hh he hp hE hz
 obtain ⟨a,hA,K⟩:=positiveCheap (W:=W)
 obtain ⟨f,hf,hU⟩:=Ducat.counts (downCost ht.2 hη (fun _=>le_rfl)) h
 obtain ⟨g,hg0,hW⟩:=censorPlus (downCost ht.1 hη (fun _=>le_rfl)) h
 let u:Finset (ℕ×ℕ):=(square e ×ˢ square (e+2)).filter (fun x=>taps 0 e 0 x.1 x.2)
 choose p h0 H using fun s:↥u=>hP s.val.1 s.val.2 (Finset.mem_filter.mp s.property).2
 let u':Finset (ℕ×ℕ×ℕ):=(square e ×ˢ square e ×ˢ square r).filter (fun y=>y.2.1<y.1)
 choose q h1 H' using fun t:↥u'=> hC t.val.1 (by simpa only [in_square] using ((Finset.mem_product.mp ((Finset.mem_filter.mp t.property).1)).1)) t.val.2.1 (Finset.mem_filter.mp t.property).2 t.val.2.2
 let b(i:T0):=W.length i.x i.m^d
 let w(i:T0):=1+f i+g i+b i+(∑ j:↥u,p j i)+(∑ j:↥u',q j i)
 let δ(i:T0):=v i+a i
 have hY:(D0).Good w:=(D0).hear _ _ ((D0).hear _ _ ((D0).hear _ _ ((D0).hear _ _ ((D0).hear _ _ ((D0).steady _ zero_le_one) hf) hg0) (Ducat.stairs _ (lengths hh) _)) (Ducat.crowd _ univ p (fun i _=>h0 i))) (Ducat.crowd _ univ q (fun i _=>h1 i))
 refine ⟨w,δ,hY,(D0).lasts _ _ hv hA,fun i=>?_⟩
 have hb:0 ≤ b i:= by unfold b; exact pow_nonneg (le_trans (by norm_num) (W.length_large ..)) _
 have hp0:=fun j=>(D0).safe _ (h0 j) i;have hp1:=fun j=>(D0).safe _ (h1 j) i
 have hs:0 ≤ ∑ j:↥u,p j i:=sum_nonneg (fun _ _=>hp0 _); have hs':0 ≤ ∑ j:↥u',q j i:=sum_nonneg (fun _ _=>hp1 _)
 have hL:1 ≤ w i∧ f i ≤ w i∧ g i ≤ w i∧ b i ≤ w i∧ (∑ j:↥u,p j i) ≤ w i ∧ (∑ j:↥u',q j i) ≤ w i:=by
    have hx:0 ≤ f i:=(D0).safe _ hf i;have hy:0 ≤ g i:=(D0).safe _ hg0 i;unfold w;constructor; linarith
    constructor; linarith
    constructor;linarith
    constructor;linarith
    constructor<;>linarith
 have hz0:v i<δ i:=lt_add_of_pos_right _ (K i);have hz1:=tiny _ hv i;have hδ:=lt_of_le_of_lt hz1 hz0
 have brighten{a:ℝ}(h:a ≤ w i):a*v i ≤ w i*δ i:=mul_le_mul h hz0.le hz1 (zero_le_one.trans hL.1)
 have hZ:=hL.2.1
 refine ⟨hδ,rfl,⟨hL.1,hδ.le,inlet_eligible (J.branch i) Z ((porter hg J.branch C.side i).agree.stash),inlet_eligible (J.branch i) Z ((porter hg J.branch R.side i).agree.stash),⟨wireBag (hU i).near hZ,wireBag (hU i).far hZ,wireBag (hU i).compare (brighten hZ)⟩,fun k=> alleyWiden (hW i k) hL.2.2.1 (brighten hL.2.2.1),fun j n hJ=>?_⟩,?_,fun s t k hE' ht' hr=>?_⟩
 · let z:↥u:= ⟨(j,n),by simp only [u,mem_filter,mem_product,in_square]; refine ⟨?_,hJ⟩; unfold taps at hJ;omega⟩
   have hy:p z i≤w i:=(single_le_sum (s:=univ) (f:=fun x:↥u=>p x i) (fun _ _=>hp0 _) (mem_univ z)).trans hL.2.2.2.2.1
   obtain ⟨h1,h2,h3,h4⟩:= H z i
   exact ⟨zero_le_one.trans hL.1,h2.mono (hη i) hy (fun _=>le_rfl),h3.mono (hη i) hy (fun _=>le_rfl),h4.mono (hη i) (brighten hy) (fun _=>le_rfl)⟩
 · rw [J.same];exact hL.2.2.2.1
 let z:↥u':=⟨(s,t,k),by simp only [u',mem_filter,mem_product,in_square];exact ⟨⟨hE',ht'.le.trans hE',hr⟩,ht'⟩⟩
 obtain ⟨h1,h2,h3⟩:=H' z i;have hh:q z i ≤ w i:=(single_le_sum (s:=univ) (f:=fun x:↥u'=>q x i) (fun _ _=>hp1 _) (mem_univ z)).trans hL.2.2.2.2.2
 exact ⟨h1.trans hh,h2.trans hh,h3.trans (brighten hh)⟩
end YM.RG08.Redo
