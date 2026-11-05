import YM.RG08.Necks.Circus
import YM.RG08.Mason.Edge

/-! # Suppliers I - strong widths and all passage variations in \bar A ordinary bulk. -/
noncomputable section
namespace YM.RG08.Redo
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Camera Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Function Jetty Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {O:Type}{G:Gauge}(hg:G.Simple)
variable {I J:O→Type}{w d z v:O→ℝ}{D:Ducat.Exchange O}
lemma metered {X Y:O→ Sedan.Wheel G}(hv:∀ i,0<v i)(hd:∀ i,0 ≤ d i)(h:Ducat.Mount (r:=0) D v d X Y): Weigh D d (fun i=>Loop.measure (X i) hg/(1/2)) (fun i=> Loop.measure (Y i) hg/(1/2)):=by
 obtain ⟨p,hp,h⟩:=h
 refine ⟨_,D.moreover _ _ hp (D.steady 2 zero_le_two),?_⟩
 intro i;obtain ⟨hx,hy,hk,hS⟩:=h i
 have he:0≤v i:=(hv i).le
 change |Loop.measure (X i) hg / _| ≤ p i * _ ∧ _;rw [←sub_div,abs_div,abs_div,abs_div];norm_num
 obtain ⟨t,u⟩:|Loop.measure (X i) hg| ≤ p i ∧ |Loop.measure (Y i) hg| ≤ p i:=⟨Loop.bill_meter hg hx he hy,Loop.bill_meter hg hx he hk⟩
 rw [←Loop.var_meter hg hx hx he hy hk];have hT:=Loop.bill_meter hg (mul_nonneg hx (hd i)) he hS
 refine ⟨by linarith,by linarith,by rw [abs_div];norm_num;nlinarith⟩

variable [∀ i,Fintype (I i)][∀ i,Fintype (J i)]{f g:∀ i:O,Kernel (I i) (J i)}
lemma downCost (hf:Counter (D:=D) I J w d f g)(hc:∀ i,v i ≤ w i)(hp:∀ i,d i ≤ z i):Counter (D:=D) I J v z f g:=by
 obtain ⟨⟨p,hp0,h⟩,hs⟩:=hf
 exact ⟨⟨p,hp0,fun i=>⟨(h i).1.mono (hc i) le_rfl,(h i).2.1.mono (hc i) le_rfl,(h i).2.2.mono (hc i) (mul_le_mul_of_nonneg_left (hp i) (D.safe _ hp0 i))⟩⟩,hs⟩
-- widen wire etc profits
variable {N N':Type}
lemma wireBag {x C C':ℝ}{K:Forms.Line N}{L:Ground N}(hw:Wire L x C K)(h:C ≤ C'):Wire L x C' K:=by obtain ⟨hs,hJ,hV,hF⟩:=hw;exact ⟨hs,hJ.trans h,fun j=>(hV j).trans (by gcongr),fun j=>(hF j).trans (by gcongr)⟩
lemma alleyWiden {C C' t u σ τ:ℝ}{l:Ground N}{l':Ground N'}{n:ℕ}{a f g:Cables n N N'}(hs:Alley l l' σ τ t C a f g)(h:C ≤ C')(hT:C*t≤C'*u): Alley l l' σ τ u C' a f g:=by
 have hx (V:Cables n N N'){p p':ℝ}(hh:Forms.street a V (fun _=>p))(hp:p ≤ p'):Forms.street a V (fun _=>p'):= by
    intro j;obtain ⟨hm,hV,hY⟩:=hh j;exact ⟨hm.trans hp,fun x=>(hV x).trans (by gcongr), fun x=>(hY x).trans (by gcongr)⟩
 obtain ⟨h1,h2,h3,h4,h5⟩:=hs
 exact ⟨h1.trans h,hx _ h2 h,hx _ h3 h,hx _ h4 hT,h5⟩
-- C63 censorship is uniform any arity. derive by projecting one rank along fibers.
lemma censorPlus (h:Counter (D:=D) I J w d f g)(he:∀ i,0<w i):∃ a,D.Good a ∧ ∀ (i:O)(n:ℕ), Alley (carpet _) (carpet _) (w i) (w i) (d i) (a i) (flare _ _ (w i)) (repeatLine (f i) n) (repeatLine (g i) n):=by
 obtain ⟨a,ha,H⟩:=Ducat.censorship h he 1
 refine ⟨a,ha,fun i n=>?_⟩
 have hJ:=H i;obtain ⟨h1,h2,h3,h4,-⟩:=hJ
 -- for lights reuse h @ censorship n or explicit
 obtain ⟨_,_,K⟩:=Ducat.censorship h he n;exact ⟨h1,fun _=>h2 0,fun _=>h3 0,fun _=>h4 0,(K i).lights⟩

-- join previously solved tickets, neighboring queries. all through E.
variable {E n:ℕ}
lemma upkeep (w:ℕ→ℕ→O→ℝ)(F T:O→Castle G)(h:∀ i j,i ≤ E → Live j i → Lapel D (w i j) (fun x=>F x j i) ∧ Lapel D (w i j) (fun x=>T x j i) ∧ Wave D (w i j) (fun x=> F x j i) (fun x=> T x j i)):
 ∃ d,D.cheap d∧∀ i j,i ≤ E → Live j i → Ducat.Mount D (w i j) d (fun x=>F x j i) (fun x=>T x j i):=by
 let s:Finset (ℕ×ℕ):=(square E ×ˢ square E).filter (fun x=>Live x.2 x.1)
 let K (t:ℕ×ℕ)(d):= Ducat.Mount D (w t.1 t.2) d (fun x=> F x t.2 t.1) (fun x=> T x t.2 t.1)
 obtain ⟨a,ha,H⟩:=gathering (D:=D) s K (fun ⟨i,j⟩ hx=>by
    simp only [s,mem_filter,mem_product,in_square] at hx; obtain ⟨hA,hB,hv⟩:=h i j hx.1.1 hx.2;exact grazing (I:=Gear O G) hA hB hv) (fun i _ a b he hb=> Lance.vow (I:=Gear O G) hb he (fun _=>le_rfl))
 exact ⟨a,ha,fun i j hi hj=>H (i,j) (by simp only [s,mem_filter,mem_product,in_square];exact ⟨⟨hi,hj.1.trans hi⟩,hj⟩)⟩
end YM.RG08.Redo
