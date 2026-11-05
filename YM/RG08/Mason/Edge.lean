import YM.RG08.Mason.Walls

/-! # Solved deviation steps. both histories in same schedule problem. -/
noncomputable section
namespace YM.RG08.Mason
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {X:Type}{W:Rate.Stair X}{G:Gauge}(hg:G.Simple){K:KernelChoices}{Z:ChartRatio G}{T:Charter W K Z}{E e r:ℕ}
private lemma increases {O:Type}{D:Exchange O}{K:KernelChoices}(G:Gauge){w d p :O→ℝ}{Γ:O→Patch}{A B:O→Bed}(hM:FairT (D:=D) (Γ:=Γ) (K:=K) (G:=G) A B w d)(h:∀ i,d i ≤ p i):FairT (D:=D) (Γ:=Γ) (K:=K) (G:=G) A B w p:=by
 have he {I J:O→Type}[∀ i,Fintype (I i)][∀ i,Fintype (J i)]{a b:∀ i,Kernel (I i) (J i)}(hk:Counter (D:=D) I J w d a b):Counter (D:=D) I J w p a b:=by
    obtain ⟨⟨z,hz,hh⟩,hx⟩:=hk;exact ⟨⟨_,hz,fun i=>⟨(hh i).1,(hh i).2.1, (hh i).2.2.mono le_rfl (mul_le_mul_of_nonneg_left (h i) (D.safe _ hz i))⟩⟩,hx⟩
 exact ⟨he hM.1,he hM.2⟩

structure Pair (E:ℕ)(R P:Pros T) where
 one:Vow hg E R
 two:Vow hg E P
 harm e r (he:e ≤ E)(hr:Live r e)(h:0<e):∀ i,Held (carpet _) (coats T.warp e r i) ((one.tuition e r he hr h).ζ i) (P.side.top i)
 armies e r: e ≤ E→Live r e→0 < e →
    ∃ d,(turnstile W).cheap d ∧ FairT  (D:=turnstile W) (G:=G) (Γ:=T.patch) (K:=K) R.side.fine P.side.fine (needs T.warp e r) d
 base : Wave (r:=0) (kiosk W) (fun i=>apron T.yard 0 0 i.x i.m) (fun i=>R.current i.x i.m 0 0) (fun i=>P.current i.x i.m 0 0)
 baseC : Wave (r:=0) (turnstile W) (coats T.warp 0 0) R.side.top P.side.top

private lemma alloy {O:Type}(D:Exchange O)(w:ℕ→ℕ→O→ℝ)(F A:O→Castle G)(h:∀ i j,Earlier e r i j → Lapel D (w i j) (fun x=>F x j i) ∧ Lapel D (w i j) (fun x=>A x j i) ∧ Wave D (w i j) (fun x=> F x j i) (fun x=> A x j i)):
 ∃ d,D.cheap d ∧ Book D F A w d e r:=by
 let s:Finset (ℕ×ℕ):=(square e ×ˢ square e).filter (fun x=>Earlier e r x.1 x.2)
 let L (i:ℕ×ℕ) d:= Ducat.Mount D (w i.1 i.2) d (fun x=>F x i.2 i.1) (fun x=>A x i.2 i.1)
 obtain ⟨a,ha,hQ⟩:= gathering (D:=D) s L (fun x hx=>by obtain ⟨h,hh,hT⟩:=h _ _ (Finset.mem_filter.mp hx).2;exact grazing (I:=Gear O G) h hh hT) (fun i _ a b he ha=> Lance.vow (I:=Gear O G) ha he (fun _=>le_rfl))
 exact ⟨a,ha,fun i j hj=>hQ (i,j) (by simp only [s,mem_filter,mem_product,in_square]; refine ⟨?_,hj⟩;have ht:=hj.1.1;have hv:=hj.2;omega)⟩
private lemma book_bump {O:Type}(D:Exchange O){w:ℕ→ℕ→O→ℝ}{d d':O→ℝ}{F A:O→Castle G}(h:Book D F A w d e r)(he:∀ i,d i ≤ d' i):Book D F A w d' e r:=fun i j hi=> Lance.vow (I:=Gear O G) (h i j hi) he fun _=>le_rfl

variable (R P:Pros T)
def Cost (e r:ℕ):Prop:= Wave (kiosk W) (fun i=>apron T.yard e r i.x i.m) (fun i=> R.current i.x i.m r e) fun i=> P.current i.x i.m r e
def Woken (e r:ℕ):Prop:= Wave (turnstile W) (coats T.warp e r) (fun i=> R.side.ample T.branch i r e) fun i=> P.side.ample T.branch i r e
lemma waved (h:W.Admits)(hk:Cost R P e r):Wave (turnstile W) (T.learn e r) (fun i=> R.side.letters i r e) fun i=>P.side.letters i r e:=by simp_rw [R.receipt,P.receipt]; exact (highString h).wave hk

theorem pellets (h:W.Admits) (he:Pair hg E R P)(hC:e ≤ E)(hR:Live r e): Cost R P e r ∧ Woken R P e r:=by
 let D:=turnstile W
 have ah (i j :ℕ)(hi: Earlier e r i j):=hi -- erase
 generalize hp:merit E e r=n
 clear ah
 induction n using Nat.strong_induction_on generalizing e r with
 | h n ih=>
   rcases eq_or_lt_of_le (Nat.zero_le e) with h0|hz
   · subst e; have hx:r=0:=(Nat.eq_zero_of_le_zero hR.1); subst r;exact ⟨he.base,he.baseC⟩
   have hf0(i j)(hh:Earlier e r i j):i ≤ E:=by have ht:=hh.2;omega
   have old (i j)(hh:Earlier e r i j): Cost R P i j∧ Woken R P i j:=ih _ (hp ▸ precedes hC hR hh) (hf0 i j hh) hh.1 rfl
   obtain ⟨u,hu,H⟩:= he.armies e r hC hR hz
   have ha(i j)(hi:i ≤ E)(hk:Live j i):= delivers hg R h he.one hi hk; have hb(i j)(hi:i ≤ E)(hk:Live j i):=delivers hg P h he.two hi hk
   obtain ⟨v,hv,hQ⟩:=alloy (e:=e) (r:=r) D (T.learn) R.side.letters P.side.letters (fun i j hi=> ⟨up h (ha i j (hf0 i j hi) hi.1).1, up h (hb i j (hf0 i j hi) hi.1).1,waved R P h (old i j hi).1⟩)
   obtain ⟨z,ht,hT⟩:=alloy (e:=e) (r:=r) D (coats T.warp) (R.side.ample T.branch) (P.side.ample T.branch) (fun i j hi=>⟨(ha i j (hf0 i j hi) hi.1).2,(hb i j (hf0 i j hi) hi.1).2,(old i j hi).2⟩)
   let g(i:Run W):=u i+v i+z i
   have hg':D.cheap g:=D.lasts _ _ (D.lasts _ _ hu hv) ht
   let F:= he.one.tuition e r hC hR hz; let F':=he.two.tuition e r hC hR hz
   have hv0(i):0≤u i:=tiny D hu i;have hv1(i):0≤v i:=tiny D hv i;have hv2(i):0≤z i:=tiny D ht i
   have H0: Wave (r:=0) D (coats T.warp e r) R.side.top P.side.top:=by
      obtain ⟨a,H',h'⟩:=he.baseC;refine ⟨_,H',fun i=> (h' i).mono ?_ le_rfl (fun _=>le_rfl)⟩
      -- scant gives need(e,r) ≤ coats previous/(rank*32)
      refine ((T.warp i).tag e r).2.1.trans ((F.loan.scant 0 0 hz le_rfl i).trans ?_)
      unfold trail; have hx:= ((T.warp i).tag 0 0).1
      unfold RG08.Mount.rank;unfold coats; push_cast;nlinarith
   obtain ⟨p,q,s,hp,hq,hs,H'⟩:= ends hg R.side P.side F F' hR hz hg' (increases G H fun i=>by unfold g;linarith [hv1 i,hv2 i]) (book_bump D hQ (fun i=>by unfold g;linarith [hv0 i,hv2 i])) (book_bump D hT (fun i=>by unfold g;linarith [hv0 i,hv1 i])) (up h (ha e r hC hR).1) (up h (hb e r hC hR).1) (he.harm e r hC hR hz) H0
   have hr1:= (ha e r hC hR).1;have hr2:=(hb e r hC hR).1
   let V:=apron T.yard e r
   have hf: Cost R P e r:=by
      obtain ⟨a,hA,H⟩:=hr1; obtain ⟨b,hB,h'⟩:=hr2
      apply cruises (w:=V) (F:=fun x k=>R.current x k r e) (A:=fun x k=>P.current x k r e) (V:=fun i=>a i+b i) (U:=p) ((kiosk W).hear _ _ hA hB) hp
      · intro i _;exact (H i).sub (h' i) ((kiosk W).safe _ hA i) ((kiosk W).safe _ hB i)
      intro i b hb h0;rw [← T.same i,he.one.agreement i,he.two.agreement i];
      apply (H' i b hb _).1; rw [R.receipt,P.receipt];exact h0
   obtain ⟨a,hA,hb⟩:= waved R P h hf
   exact ⟨hf,_,D.lasts _ _ (D.awe _ _ hq hA) hs,fun i=>(H' i (a i) (tiny D hA i) (hb i)).2⟩
-- explicit kbulk cap; Held exponential widths as strong as proposed. E fixed.
theorem subsidy (h:W.Admits)(he:Pair hg E R P)(hC:e ≤ E)(hR:Live r e) : ∃ (A:ℝ)(d:ℕ)(c:ℝ),0 ≤ A∧ 0 < c∧∀ (x:X)(m:ℕ),W.Here x m→ Held (carpet (Tone G.ColorIndex)) (apron T.yard e r x m) (A*W.age x m^d*(((W.sched x).a (W.top x)/(W.sched x).a m)^c)) (R.current x m r e-P.current x m r e):=by
 obtain ⟨p,hp,hP⟩:= (pellets hg R P h he hC hR).1
 obtain ⟨a,d,c,ha,hc,H⟩:= (show W.Fade (wide p) from hp).cap
 exact ⟨a,d,c,ha,hc,fun x m hm=>(hP (⟨x,m,hm⟩:Haven W)).mono le_rfl (by simpa only [wide,dif_pos hm] using (H x m hm).2) (fun _=>le_rfl)⟩
end YM.RG08.Mason
