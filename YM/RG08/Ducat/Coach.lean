import YM.RG08.Ducat.Palms

/-! # Harvest polynomials for the step charges. Active grades only. One variant supplied with
 native hypothesis for the UNKNOWN record at self; suffices for vertical recursion. Y summaries
 for post-comparison before and after reset.
-/
noncomputable section
namespace YM.RG08.Ducat
open Filter Function Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets
open scoped Classical BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}(hg:G.Simple){O:Type}{D:Exchange O}{d:O→ℝ}{r e:ℕ}

-- align output page and harvest states. abstraction for use with independent choices per step.

def plotter {P:Patch}{K:RG.KernelChoices}(h:P.Branches K G)(Z:ChartRatio G)(A B:Bed)(C:Castle G): Scroll G:=-(vault G P K h C Z A B)
def hedge {P:Patch}{K:RG.KernelChoices}(h:P.Branches K G)(Z:ChartRatio G)(A B:Bed)(C:Castle G)(T:Wheel G)(H:Yard G)(e:ℕ):Castle G:=Sedan.carriage H (plotter h Z A B C) T (e-1)
variable {P:Patch}{K:RG.KernelChoices}{Z:ChartRatio G}{A B:Bed}{C:Castle G}{T:Wheel G}{H:Yard G}
def wild (H:Yard G)(T:Wheel G)(C:Castle G)(Z:ChartRatio G)(h:P.Branches K G)(A B:Bed):Castle G:=sorted H (plotter h Z A B C) T
abbrev wage (H:Yard G)(T:Wheel G)(C:Castle G)(Z:ChartRatio G)(h:P.Branches K G)(A B:Bed):Castle G:=Nacre.send (wild H T C Z h A B) hg
variable {h:P.Branches K G}
def Reach (P:Patch)(Z:ChartRatio G)(A B:Bed)(C:Castle G)(T:Wheel G):Prop:= Nonempty (Foyer P K A B C Z) ∧ Sedan.Seed B T
lemma wm(k:ℕ)(hr:RG08.Mount.Live r (k+1)): wild H T C Z h A B r (k+1)=grant H (k+1) (page h A B C (hedge h Z A B C T H (k+1)) Z (k+1) r):=by unfold wild sorted carriage patcher;rw [if_pos rfl,if_pos hr];unfold carry hedge;rw [show k+1-1=k by omega];rfl

include hg
lemma roof {p : ℝ}(ht:p≥0)(hH:Reach (K:=K) P Z A B C T)(he:RG08.Mount.Live r e)(hE:0<e)
    (hF:Held (carpet _) (H.need e r) p (page h A B C (hedge h Z A B C T H e) Z e r)):Ready (n:=r+1) (Symmetry.dressed G (RG08.Mount.rank r)) (H.need e r) p (page h A B C (hedge h Z A B C T H e) Z e r):=by
 let V:= plotter h Z A B C
 let L:=hedge h Z A B C T H e
 let i:=e-1
 obtain ⟨⟨hK⟩,hP⟩:=hH
 obtain ⟨hx,hM,H'⟩:= consulate h hP hK -- arguments?
 have hj:i+1=e:=by unfold i;omega
 obtain ⟨hf,hU,hq⟩:=toward H V T hg hx hM hP.honor H' i
 let W:=V-demand L;have he0:=hx.sub (Grimoire.demand L hU.rails)
 obtain ⟨w,q,hw,hQ,hJ⟩:=he0.billed e (RG08.Mount.rank r)
 obtain ⟨hN,hV,_⟩:=Roost.frontier W e (hM.sub (masters hU.rails)) (fun k hk n hn=>hf k (by omega) n (Nat.pos_of_ne_zero hn)) (k:=RG08.Mount.rank r) (by have := he.1;unfold RG08.Mount.rank;omega) (he0.solvent _ _).2 (he0.solvent _ _).1 hJ
 exact ⟨hN,hV,ht,hF⟩
lemma baseT (k:ℕ)(hH: Reach (K:=K) P Z A B C T): Fair (wild H T C Z h A B) ∧ Fair (hedge h Z A B C T H k):=by
 obtain ⟨⟨hK⟩,hP⟩:=hH; obtain ⟨hx,hM,H'⟩:=consulate h hP hK
 let V:=plotter h Z A B C
 exact ⟨(well_sorted H V T hg hx hM hP.honor H').1,(toward H V T hg hx hM hP.honor H' (k-1)).2.1⟩
lemma overT (hH: Reach (K:=K) P Z A B C T)(he:0<e):overlooks (hedge h Z A B C T H e) e:=by
 obtain ⟨⟨hK⟩,hP⟩:=hH; obtain ⟨hx,hM,H'⟩:=consulate h hP hK
 let V:=plotter h Z A B C
 have heq:e-1+1=e:=by omega
 exact fun i s h↦(toward H V T hg hx hM hP.honor H' (e-1)).2.2 i s (by omega)

-- hedges for pins earlier SAME degree higher r: hedge is zero there.
variable (Γ:O→Patch)(κ:RG.KernelChoices)(hΓ:∀ x,(Γ x).Branches κ G)(Z:ChartRatio G)(H:O→Yard G)
abbrev needs (e r:ℕ):O→ℝ:=fun i=>(H i).need e r
abbrev coats (e r:ℕ):O→ℝ:=fun i=>(H i).coats e r
abbrev cashes (e r:ℕ):O→ℝ:=fun i=>(H i).cash e r
structure Palace (D:Exchange O)(M:O→Kernel (TypeFace 2) (TypeFace 2))(X z ω:O→ℝ)(v:O→ℝ)(e r:ℕ):Prop where
 royalty: ∀ x,Royal G (H x) (X x) (v x) (z x) (ω x) r e ((Γ x).L)
 atlas x : Atlas (ω x) (Γ x).L 2 (M x) (X x)
 mark x : Packets.city ((Γ x).L) (M x)
 score : D.Good z
 congestion: D.Good (cashes H e r)
 token: D.Good fun x=>coin G r (X x) (needs H e r x) (v x)

variable {Γ κ hΓ Z H}
lemma earns {A B:O→Bed}{C:O→Castle G}{T:O→Wheel G}{w:O→ℝ}{M:O→Kernel (TypeFace 2) (TypeFace 2)}{X z ω:O→ℝ}
    (hS:Palace Γ H D M X z ω w e r)(hT:∀ i,Duo G (Γ i) κ (A i) (M i))(ht:∀ i,Reach (K:=κ) (Γ i) Z (A i) (B i) (C i) (T i))
    (hZ:∀ i,Tires (A i) (C i))(hq:∀ i,Held (carpet _) (coats H e r i) (z i) (T i))(hw:∀ i,0<w i)
    (he:RG08.Mount.Live r e)(h0:0<e)
    {R:O→Castle G}(hc:∀ i,R i=hedge (hΓ i) Z (A i) (B i) (C i) (T i) (H i) e)
    (hF:∀ i, ∃ σ p:ℝ,0<σ ∧ Priced σ p (Prism.rains (Γ i) κ (A i) (G:=G)))
    (hX:Bound (I:=Gear O G) D (needs H e r) (fun i=>Ducat.sweep (hΓ i) (A i) (C i) (R i) Z e r)):
 ∃ p s:O→ℝ,D.Good p∧ D.Good s∧ ∀ (i:O) (b:ℝ),0 ≤ b → Held (carpet _) (w i) b (C i r e) →
 let F:=page (hΓ i) (A i) (B i) (C i) (R i) Z e r; let V:=wild (H i) (T i) (C i) Z (hΓ i) (A i) (B i) r e; let H0:=√((Γ i).L.val:ℝ)
 ; Held (carpet _) (needs H e r i) (s i*b+s i) F ∧ Held (carpet _) (coats H e r i) (s i*b+s i) V ∧
   Held (carpet _) (coats H e r i) (b/H0+p i) (vac hg (T i) V):=by
 obtain ⟨y,hy,hY⟩:=hX
 let g(i):=1+cashes H e r i
 let u(i):=1+2*z i
 let τ(i:O):= coin G r (X i) (needs H e r i) (w i)
 have hf:D.Good g:=D.hear _ _ (D.steady 1 zero_le_one) hS.congestion
 have hu:D.Good u:=D.hear _ _ (D.steady _ zero_le_one) (D.moreover _ _ (D.steady _ zero_le_two) hS.score)
 let subtotal (i):=g i*(τ i+y i)
 refine ⟨fun i=>u i*cashes H e r i*y i,subtotal,D.moreover _ _ (D.moreover _ _ hu hS.congestion) hy,D.moreover _ _ hf (D.hear _ _ hS.token hy),?_⟩
 intro i b hb hF0 F V H0
 have hp:=hS.royalty i;have hU:= hS.atlas i; let L:= (Γ i).L
 have heq:F=voucher (M i) (C i r e)+Ducat.sweep (hΓ i) (A i) (C i) (R i) Z e r:=by obtain ⟨_,_,hh,H⟩:= hF i; exact absorbs (M i) (hT i) H hh (hZ i).ethos h0 he.1
 let j:= needs H e r i
 let Θ:= Symmetry.dressed G (RG08.Mount.rank r)
 let B0:=τ i*b/L.val+y i
 have hv0:= D.safe _ hS.token i; have hy0:=D.safe _ hy i
 have hl:1≤ (L.val:ℝ):= Nat.one_le_cast.mpr L.pos
 have hτ:0≤τ i*b/(L.val:ℝ):=by change 0 ≤ τ _ at hv0;positivity
 have hB:0≤B0:=add_nonneg hτ hy0
 have hx: Native G (C i r e) (w i) b:=by
    obtain ⟨hT,-⟩:=(hZ i).ethos.honor r e
    refine ⟨hF0,hT.beam,hT.path,?_⟩
    split
    next H=>subst r;exact (hZ i).cure _ h0.ne'
    next=>trivial
 have hQ:= roof hg (h:=hΓ i) (H:=(H i)) hB (ht i) he h0 ?w
 case w=> rw [←hc];change Held _ _ _ F;rw [heq];exact (currency hU (hS.mark _) hx (hw _) hp.cargo hb).add (hY i) hτ hy0
 rw [←hc] at hQ
 have hv:V=grant (H i) e F:=by
    unfold V F;rw [hc i]; revert he; cases e <;> intro he -- h0 already in context; shape H? eliminates massive context but ok?
    · omega
    exact wm _ he -- hc binder appears in F only; unfold
 have hh:= (H i).tag e r
 have heT:= (hh.2.2.2 _ B0 hQ)
 have hR:Ready (n:=r+1) Θ j 0 0:=⟨⟨fun _ _=>rfl, graded_iff.mpr (fun _ _ _=> rfl),Forms.Sym.zero,fun _=>map_zero _,fun _=> Θ.zero_mem⟩,by intro x y; change AnalyticNext.QuarticMatch.BoxChain.lower y (hum 0 x)=0;exact map_zero _,le_rfl,zero_held⟩
 have hA:= waxed (H:=H i) (S:=T i) (S':=T i) (c:=0) hg hp hU (hS.mark _) (hw _) hQ hR (by change F-0 = _;rw [sub_zero,heq]) (hY i) hy0 hx hb le_rfl (fun _=>⟨hq i,hq i,by rw [sub_self];exact zero_held⟩)
 have hJ: grant (H i) e (0:Gird G r)=0:=by
    rw [grant_open _ _ _ hR.held]
    have ht:=(hh.2.2.2 (0:Gird G r) 0 hR).2.1
    rw [mul_zero] at ht; ext x; have hy:=ht.plain  le_rfl hh.1.le (Nat.zero_lt_succ _) x
    simpa using hy
 have h0':B0 ≤ subtotal i*b+subtotal i:=by
   have hy:τ i*b/L.val ≤ τ i*b:=div_le_self (mul_nonneg hv0 hb) hl
   have hp:=D.safe _ hS.congestion i;dsimp only [subtotal, g, B0]
   nlinarith only [hy,hp,hy0,hv0,hb,mul_nonneg hp (mul_nonneg hv0 hb),mul_nonneg hy0 hb,mul_nonneg hp hy0,mul_nonneg hp (mul_nonneg hy0 hb),mul_nonneg hp hv0]
 have he2:cashes H e r i*B0 ≤ subtotal i*b+subtotal i:=by
   have hy:τ i*b/L.val ≤ τ i*b:=div_le_self (mul_nonneg hv0 hb) hl
   have hp:=D.safe _ hS.congestion i;dsimp only [subtotal, g, B0]
   nlinarith only [mul_le_mul_of_nonneg_left hy hp,hp,hv0,hy0,hb,mul_nonneg hp (mul_nonneg hy0 hb),mul_nonneg hp hv0,mul_nonneg hy0 hb,mul_nonneg hv0 hb]
 rw [hv]
 refine ⟨hQ.held.mono le_rfl h0' (fun _=>le_rfl),?_,?_⟩
 · rw [grant_open _ _ _ hQ.held];exact (heT.2.1).mono le_rfl he2 (fun _=>le_rfl)
 convert (hA.1) using 1
 · dsimp [B0,u,g,subtotal,cashes,H0];ring
 rw [hJ,show vac hg (T i) (0:Gird G r)=0 from ?_,sub_zero]
 -- meter zero
 unfold vac;split
 next h=> subst h; change 0-Loop.reading 0 hg (1/2) • T i=_
          have h:= Loop.meter_scale (F:=(0:Wheel G)) hg 0; simp only [zero_mul,zero_smul] at h
          rw [Loop.reading,h, _root_.zero_div,zero_smul,sub_zero]
 next=>rw [sub_zero]

private lemma native_change {C C':Castle G}{B B':Bed}(h:Tires B C)(h':Tires B' C'){p u:ℝ}(hN:Held (carpet _) u p (C r e-C' r e))(hu:0<e): Native G (C r e-C' r e) u p:=by
 have hh:= ((h.ethos.honor r e).minus (h'.ethos.honor r e))
 refine ⟨hN,hh.1.beam,hh.1.path,?_⟩; split <;> first|trivial|skip
 rename_i hr; subst r;change Loop.Core (C 0 e-C' 0 e) 0
 obtain ⟨hF,s,p,hs,hP,hQ⟩:=hh
 obtain ⟨-,m,q,hm,hT,hU⟩:=h.ethos.honor 0 e
 obtain ⟨-,M,Q,hM,hk,hJ⟩:=h'.ethos.honor 0 e
 convert Loop.plays hg hs.le hP hF hQ using 1
 rw [Loop.var_meter hg hT hk (lt_min hm hM).le (hU.mono (min_le_left ..) le_rfl (fun _=> le_rfl)) (hJ.mono (min_le_right ..) le_rfl (fun _=>le_rfl)),Loop.measured _ hg (h.cure e (by omega)),Loop.measured _ hg (h'.cure e (by omega)),sub_self]

-- reusable overlap wrapper: supplies ONLY require Bound page (which obtained by earns), Lance warm geometry and earlier stuff assemble amber β/c. hg scope.
lemma double {A B A' B':O→Bed}{C C':O→Castle G}{T T':O→Wheel G}{w:O→ℝ}{M:O→Kernel (TypeFace 2) (TypeFace 2)}{X z ω:O→ℝ}
 (hS:Palace Γ H D M X z ω w e r)(hw:∀ i,0<w i)
 (ht:∀ i,Reach (K:=κ) (Γ i) Z (A i) (B i) (C i) (T i))(ht':∀ i, Reach (K:=κ) (Γ i) Z (A' i) (B' i) (C' i) (T' i))
 (hZ:∀ i,Tires (A i) (C i))(hZ':∀ i,Tires (A' i) (C' i))
 (he:Live r e)(h0:0<e)
 {F F':O→Gird G r}{R R':O→Castle G}
 (hR:∀ i,R i=hedge (hΓ i) Z (A i) (B i) (C i) (T i) (H i) e)(hR':∀ i,R' i=hedge (hΓ i) Z (A' i) (B' i) (C' i) (T' i) (H i) e)
 (hA:∀ i,F i=page (hΓ i) (A i) (B i) (C i) (R i) Z e r)(hA':∀ i,F' i=page (hΓ i) (A' i) (B' i) (C' i) (R' i) Z e r)
 (hs:Lapel D (needs H e r) F)(hs':Lapel D (needs H e r) F') (hY:∃ p,D.cheap p ∧∀ i,Held (carpet _) (needs H e r i) (p i) (F i-F' i-voucher (M i) (C i r e-C' i r e)))
 (hq:∀ i,Held (carpet _) (coats H e r i) (z i) (T i)∧Held (carpet _) (coats H e r i) (z i) (T' i))
 (hD:Change (I:=Gear O G) D (coats H e r) T T'):
 ∃ p q s:O→ℝ, D.cheap p∧ D.Good q ∧ D.cheap s∧ ∀ i (c:ℝ),0 ≤ c→Held (carpet (Tone G.ColorIndex)) (w i) c (C i r e-C' i r e)→
 let V:=wild (H i) (T i) (C i) Z (hΓ i) (A i) (B i) r e; let V':=wild (H i) (T' i) (C' i) Z (hΓ i) (A' i) (B' i) r e; let H0:=Real.sqrt ((Γ i).L.val:ℝ)
 ; Held (carpet (Tone G.ColorIndex)) (coats H e r i) (c/H0 + p i) (vac hg (T i) V-vac hg (T' i) V') ∧ Held (carpet (Tone G.ColorIndex)) (coats H e r i) (q i*c+s i) (V-V'):=by
 obtain ⟨p,hp,hF⟩:=hs; obtain ⟨q,hQ,hf'⟩:=hs'; obtain ⟨d,hd,hD⟩:=hD; obtain ⟨y,hy,hY⟩:=hY
 let k:= cashes H e r; let m (i:O):= coin G r (X i) (needs H e r i) (w i)
 let u (i:O):=1+2*z i; have hu:D.Good u:=D.hear _ _ (D.steady _ zero_le_one) (D.moreover _ _ (D.steady _ zero_le_two) hS.score)
 let g(i:O):=u i*k i*y i+k i*p i*2*d i
 refine ⟨g,fun i=> k i*m i,fun i=>k i*y i,D.lasts _ _ (D.awe _ _ (D.moreover _ _ hu hS.congestion) hy) (D.awe _ _ (D.moreover _ _ (D.moreover _ _ hS.congestion hp) (D.steady _ zero_le_two)) hd),D.moreover _ _ hS.congestion hS.token,D.awe _ _ hS.congestion hy,?_⟩
 intro i c hc hb V V' H0
 have hh:∀ P X B C T R (_h':Reach (K:=κ) (Γ i) Z X B C T),P=page (hΓ i) X B C R Z e r→ R=hedge (hΓ i) Z X B C T (H i) e→ ∀ b,0 ≤ b→Held (carpet _) (needs H e r i) b P → Ready (n:=r+1) (Symmetry.dressed G (RG08.Mount.rank r)) (needs H e r i) b P ∧ wild (H i) T C Z (hΓ i) X B r e=grant (H i) e P:=by
    rintro P a b x t u (hp:Reach (K:=κ) (Γ i) Z a b x t) H hu b hb hB
    subst P u; refine ⟨roof hg hb hp he h0 hB,?_⟩;revert he;cases e <;>intro he;omega
    exact wm _ he
 obtain ⟨hU,hW⟩:=hh _ _ _ _ _ _ (ht i) (hA i) (hR i) _ (D.safe _ hp i) (hF i)
 obtain ⟨hU',hW'⟩:=hh _ _ _ _ _ _ (ht' i) (hA' i) (hR' i) _ (D.safe _ hQ i) (hf' i)
 have hv:= native_change hg (hZ i) (hZ' i) hb h0
 have hz:= D.safe _ hS.token i
 have hk:=D.safe _ hS.congestion i
 have ht:=waxed hg (H:=H i) (S:=T i) (S':=T' i) (s:=p i) (hS.royalty i) (hS.atlas i) (hS.mark _) (hw i) hU hU' (Y:=F i-F' i-voucher (M i) (C i r e-C' i r e)) (add_sub_cancel _ _).symm (hY i) (tiny D hy i) hv hc (tiny D hd i) (fun _=>⟨(hq i).1,(hq i).2,hD i⟩)
 unfold V V';rw [hW,hW']
 refine ⟨ht.1.mono le_rfl (by change c/H0+_+_ ≤ c/H0+_;unfold g u k cashes; exact le_of_eq (by ring)) (fun _=>le_rfl), ht.2.mono le_rfl ?_ (fun _=>le_rfl)⟩
 change k i*(m i*c/(↑(Γ i).L.val:ℝ)+y i) ≤ k i*m i*c + k i*y i; rw [mul_add,←mul_div_assoc,←mul_assoc]
 exact add_le_add_left (by exact div_le_self (mul_nonneg (mul_nonneg hk hz) hc) (Nat.one_le_cast.mpr (Γ i).L.pos)) _ -- add_le... orientation
end YM.RG08.Ducat
