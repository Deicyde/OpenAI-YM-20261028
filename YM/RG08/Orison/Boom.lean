import YM.RG08.Orison.Brass
/-! # Realized tone through fixed thresholds and coarsen-to-lower-level. !-/
noncomputable section
namespace YM.RG08.Orison
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{a:Levels G}{F:Horizon a}{P X:MapPrices}(hg:G.Simple){Z:ChartRatio G}{U:ℕ→Kernel Flat.Links Flat.Links}{A B c:ℝ}{d k:ℕ}{E e r:ℕ}
variable (L: Yamen.Supplies F P Z) (hM:Bill G P X a)(hh:Payment G P X Z a) (hA:Flat.Quorum (Flat.curve X) U 0 F A B d k c)
include L hM hh hA
omit L hM hh hA in
private lemma clock0 (i u):2≤Flat.clock a.S (Flat.Lambda' a) u i:=by unfold Flat.clock Flat.Lambda' Flat.Lambda; have he:=Real.log_pos (a.fits.delayed u);have h:=abs_nonneg (a.S.scale i-a.S.scale u);linarith -- auto included variables causes error

lemma star (he:e ≤ E)(hr:Live r e)(m n)(hm:m ≤ n)(hn:E ≤ a.clock.J m):
 Tone (fun i=>fed F P X hg Z (i+n) m r e) (retreat F P X hg Z m r e) ((lamp P X a m).coats e r):=by
 obtain ⟨b,x,p,v,y,hb,hx,hy,H⟩:=vanishing hg L hM hh hA he hr
 obtain ⟨B,i,hV,hG⟩:=levels hg L hM hh he hr
 let t:=Flat.clock a.S (Flat.Lambda' a) m m;have ht:t≥0:=le_trans (by norm_num) (clock0 (a:=a) m m)
 -- p and B from different choices combine by mono
 have hp:0 ≤ b*t^p+B*t^i:=add_nonneg (mul_nonneg hb (pow_nonneg ht _)) (mul_nonneg hV (pow_nonneg ht _))
 obtain ⟨hH,h0,hW⟩:=H m m hn
 apply sounds _ _ (b*t^p+B*t^i) (fun n=>x*t^v*((a.S.a n/a.S.a m)^y)) _ n hm ⟨hH,h0.mono le_rfl (by apply le_add_of_nonneg_right (mul_nonneg hV (pow_nonneg ht _))) (fun _=>le_rfl),hW⟩ (rate0 hy _ _) hp _ _
 · intro j _; have ha:=a.S.a_pos j;have hb':=a.S.a_pos m;positivity
 intro j hj;exact (hG _ _ m hj hn).mono le_rfl (le_add_of_nonneg_left (by positivity)) (fun _=>le_rfl)

lemma admiral (he:e ≤ E)(hr:Live r e)(m n)(hm:m < n)(hn:E ≤ a.clock.J m):
 Tone (fun i=>wings F P X hg Z (i+n) m r e) (Orison.anchor F P X hg Z m r e) ((lamp P X a m).coats e r):=by
 obtain ⟨b,x,p,v,y,hb,hx,hy,H⟩:=fresh hg L hM hh hA he hr
 obtain ⟨B,B',i,j,y',hV,hV',hy',hG⟩:=scores hg L hM hh hA he hr
 let t:=Flat.clock a.S (Flat.Lambda' a) m m;have ht:t≥0:=le_trans (by norm_num) (clock0 (a:=a) m m)
 have hp:0 ≤ b*t^p+B*t^i:=add_nonneg (mul_nonneg hb (pow_nonneg ht _)) (mul_nonneg hV (pow_nonneg ht _))
 obtain ⟨hH,h0,hW⟩:=H m m hn
 apply sounds _ _ (b*t^p+B*t^i) (fun n=>x*t^v*((a.S.a n/a.S.a m)^y)) _ n hm ⟨hH,h0.mono le_rfl (by apply le_add_of_nonneg_right (mul_nonneg hV (pow_nonneg ht _))) (fun _=>le_rfl),hW⟩ (rate0 hy _ _) hp _ _
 · intro j _; have ha:=a.S.a_pos j;have hb':=a.S.a_pos m;positivity
 intro j hj;exact ((hG m j j m hn hj le_rfl).1).mono le_rfl (le_add_of_nonneg_left (by positivity)) (fun _=>le_rfl)

-- work only e≤E. limit capsules at every active live, and all smaller seats via cutting. constructor no hypotheses.
variable {Q:Castle G}
def erase (E:ℕ)(A:Castle G):Castle G:=fun i p=>if p≤E∧ Live i p then A i p else 0
omit L hM hh hA in
lemma certainly (A:Castle G)(E:ℕ)(p r:ℕ)(h:p ≤ E)(he:Live r p):erase E A r p=A r p:=if_pos ⟨h,he⟩ -- omit globals
omit L hM hh hA in
lemma clear_h (A:Castle G)(E:ℕ)(h:Fair A): Fair (Orison.erase E A):=by
 constructor <;>intro r e
 · intro he; unfold Orison.erase;rw [if_neg (fun H=>he H.2)]
 unfold Orison.erase;split;exact h.honor ..;exact Honor.nil

structure Shade (E:ℕ)(A:ℕ→Castle G)(B:Castle G):Prop where
 valid : Fair B
 paid i:Fair (A i)
 cost e r:e ≤ E→ ∃ σ,0<σ∧ Tone (fun i=>A i r e) (B r e) σ
-- supply from emissions (B always cut, A full ok).
omit L hM hh hA in
lemma parse {E:ℕ}{F:ℕ→Castle G}{V:Castle G}(hF:∀ i,Fair (F i))(h:∀ e r,e ≤ E → Live r e→∃ σ,0<σ∧Tone (fun i=>F i r e) (V r e) σ): Shade E F (Orison.erase E V):=by
 let Z:=Orison.erase E V
 refine ⟨?_,hF,?_⟩
 · constructor <;> intro i e <;> unfold Orison.erase <;> split
   next he=> intro h;exact (h he.2).elim
   next _=> exact fun _=>rfl
   next he=>
      obtain ⟨σ,hp,hZ⟩:=h e i he.1 he.2
      have ht:=hZ.field (Nat.zero_lt_succ _) hp.le
      obtain ⟨d,_,p,ha,H⟩:=hZ
      exact ⟨guard ht (Eventually.of_forall fun j=>((hF j).honor i e).1),σ,p 0,hp,hush.safe _ ha 0,(H 0).far⟩
   next=>exact Honor.nil
 intro e r hE;by_cases he:Live r e;swap
 · unfold Orison.erase;rw [if_neg (fun h=>he h.2)];simp_rw [fun i=>(hF i).rests r e he];exact ⟨1,zero_lt_one,nil⟩
 rw [certainly _ _ _ _ hE he];exact h _ _ hE he
lemma fidelity (i n)(hi:i ≤ n)(he:E ≤ a.clock.J i):Shade E (fun k=>fed F P X hg Z (k+n) i) (Orison.erase E (retreat F P X hg Z i)):=parse (fun j=>(ship X hg L (i:=i) (show i ≤ j+n by omega)).ethos) (fun e r h hr=> ⟨_,((lamp P X a i).tag e r).1,star hg L hM hh hA h hr _ _ hi he⟩)
lemma honesty (i n)(hi:i<n)(he:E ≤ a.clock.J i) : Shade E (fun k=>wings F P X hg Z (k+n) i) (Orison.erase E (Orison.anchor F P X hg Z i)):=by
 apply parse
 · intro j;let C:=fed F P X hg Z (j+n) (i+1)
   have hh:Tires _ C:=ship X hg L (show i+1 ≤ j+n by omega)
   exact (Ducat.baseT (h:=Yamen.branches (a:=a) i) hg 0 (studio L.housed _ _ hg (show i<j+n by omega) (fun _=>L.herald _ _ _ (show i ≤ j+n by omega)) L.lodged C hh)).1
 exact fun e r h hr=> ⟨_,((lamp P X a i).tag e r).1,admiral hg L hM hh hA h hr _ _ hi he⟩
end YM.RG08.Orison
