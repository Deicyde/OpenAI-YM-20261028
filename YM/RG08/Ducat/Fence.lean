import YM.RG08.Ducat.Coach

/-! # Absolute post-step receipts, register handoff. Avoid any annularity prerequisites.
-/
noncomputable section
namespace YM.RG08.Ducat
open Filter Function Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}(hg:G.Simple){O:Type}{r e:ℕ}{K:RG.KernelChoices}{Z:ChartRatio G}{Γ:O→Patch}{hΓ:∀ i,(Γ i).Branches K G}{H:O→Yard G}{D:Exchange O}

-- β one or two incarnations
structure SliceSide (Γ:O→Patch) (H:O→Yard G) (K:RG.KernelChoices) (Z:ChartRatio G) where
 fine : O→Bed
 coarse: O→Bed
 letters: O→ Castle G
 top:O→Wheel G
 response:O→Kernel (TypeFace 2) (TypeFace 2)
 bulbs: ∀ i,Tires (fine i) (letters i)
 leaders: ∀ i,Reach (K:=K) (Γ i) Z (fine i) (coarse i) (letters i) (top i)
 aligned:∀ i,Duo G (Γ i) K (fine i) (response i)

namespace SliceSide
variable (S:SliceSide Γ H K Z)(hΓ:∀ i,(Γ i).Branches K G)
abbrev ample (i:O):Castle G:=Ducat.wild (H i) (S.top i) (S.letters i) Z (hΓ i) (S.fine i) (S.coarse i)
abbrev links(e)(i:O) := Ducat.hedge (hΓ i) Z (S.fine i) (S.coarse i) (S.letters i) (S.top i) (H i) e
abbrev hub (e r)(i:O) :=page (hΓ i) (S.fine i) (S.coarse i) (S.letters i) (S.links hΓ e i) Z e r
abbrev car (i:O):Castle G:=Nacre.send (S.ample hΓ i) hg
include hg
lemma price (e:ℕ)(i:O): Fair (S.ample hΓ i)∧Fair (S.links hΓ e i):=baseT hg _ (S.leaders i)
lemma overlook (he:0<e)(i:O):overlooks (S.links hΓ e i) e:=overT hg (S.leaders _) he
omit hg in
lemma front (i:O):(S.ample hΓ i) 0 0=S.top i:=rfl
variable {d:O→ℝ}
lemma lowers (S':SliceSide Γ H K Z)(h:Book D (S.ample hΓ) (S'.ample hΓ) (coats H) d e r)(he:0<e): Book D (S.links hΓ e) (S'.links hΓ e) (coats H) d e r:=by
 intro i q hi
 rcases hi.2 with he'|⟨he',hp⟩
 · have hh: i ≤ e-1:=by omega
   exact (show Lance _ _ _ (fun x=>_) (fun x=>_) from by
      have hl (S:SliceSide Γ H K Z)(x):S.links hΓ e x q i=S.ample hΓ x q i:= Sedan.matching _ _ _ _ hh
      simp_rw [hl];exact h i q hi)
 subst he'
 have he0 (S:SliceSide Γ H K Z)(j:O):S.links hΓ i j q i=0:=S.overlook hg hΓ he j i q le_rfl;
 simp_rw [he0]
 exact Ducat.zero D _ _
end SliceSide

-- paid at lane e,r. Normalization base bill at each lane (need only r=0); inserted explicitly before block.
structure Pay (S : SliceSide Γ H K Z) (hΓ:∀ i,(Γ i).Branches K G) (D:Exchange O) (w:ℕ→ℕ→O→ℝ)(e r:ℕ) where
 τ : O→ℝ
 ζ : O→ℝ
 x : O→ℝ
 heroes: Palace Γ H D S.response x ζ τ (w e r) e r
 loan:Reckons D Γ w (coats H) (needs H e r) e r hΓ Z
 sure:∀ i,Held (carpet _) (coats H e r i) (ζ i) (S.top i)
 fence: FairT (G:=G) (D:=D) (K:=K) (Γ:=Γ) S.fine S.fine (needs H e r) (fun _=>0)
 variable {w:ℕ→ℕ→O→ℝ}
lemma priceRain (S:SliceSide Γ H K Z)(h:Pay S hΓ D w e r)(i:O): ∃ σ p:ℝ,0<σ∧Priced σ p (Prism.rains (Γ i) K (S.fine i) (G:=G)):=by obtain ⟨x,_,hp⟩:=h.fence.1.1; exact ⟨_,_,(h.loan.roof i).1,(hp i).1⟩
include hg

lemma hires (S:SliceSide Γ H K Z){w:ℕ→ℕ→O→ℝ}(h:Pay S hΓ D w e r)(he:Live r e)(h0:0<e)
    (ht:∀ i q,Earlier e r i q→Lapel D (w i q) (fun x=> S.letters x q i))
    (hP:∀ i q,Earlier e r i q→ Lapel D (coats H i q) (fun x=>S.ample hΓ x q i)):
 ∃ p s : O→ℝ, D.Good p ∧ D.Good s ∧ ∀ (i:O)(b:ℝ), 0 ≤ b → Held (carpet _) (w e r i) b (S.letters i r e) →
    Held (carpet _) (coats H e r i) (b/Real.sqrt ((Γ i).L.val:ℝ)+p i) (S.car hg hΓ i r e) ∧ Held (carpet _) (coats H e r i) (s i*b+s i) (S.ample hΓ i r e) ∧ Held (carpet _) (needs H e r i) (s i*b+s i) (S.hub hΓ e r i):=by
 let q:=coats H
 let wL:=S.ample hΓ
 let d:O→ℝ:=fun _=>0;have hd(x:O):0≤ d x:=le_rfl
 have hR:Book D wL wL q d e r:=fun i j hh=> Bound.join (hP i j hh)
 have hL:= S.lowers (D:=D) hg hΓ S hR h0 -- order hg
 -- snap uses monotonicity of θ vs predecessor COARSE. Pay needs not explicit: scant states need v <=trail prior widths e<. tag θ ≤ need. trail positive ≤prior.
 have hv(x):0<q e r x:=((H x).tag e r).1
 have hb:= offer hg hR (fun x=> (S.price hg hΓ e x).1) (fun x=> (S.price hg hΓ e x).1) (fun a b x=> ((H x).tag a b).1) hd (fun a n hh hj i=> ?_)
 case refine_1 => -- width
   have hs:=h.loan.scant _ _ hh hj i
   apply ((H i).tag e r).2.1.trans (hs.trans _)
   unfold trail; apply (div_le_self (by have he:= ((H i).tag a n).1; unfold coats; positivity) (by norm_num)).trans
   exact div_le_self ((H i).tag a n).1.le (by norm_cast;unfold RG08.Mount.rank;omega)
 obtain ⟨A,hA,HA⟩:Lapel D (coats H e r) (fun x=>snap hg (wL x) e r):=Lance.fore (I:=Gear O G) hb
 have hX:=sweeping h.loan hd h.fence (fun i j hi=>Bound.join (ht i j hi)) hL (fun x=>(S.bulbs x).ethos) (fun x=>(S.bulbs x).ethos) (fun x=>(S.price hg hΓ e x).2) (fun x=> (S.price hg hΓ e x).2) (fun i=>S.overlook hg hΓ h0 i) (fun i=> S.overlook hg hΓ h0 i) he.1
 obtain ⟨p,s,hp,hs,Hs⟩:= earns hg (hΓ:=hΓ) (R:=S.links hΓ e) h.heroes S.aligned S.leaders S.bulbs h.sure (h.loan.fresh e r) he h0 (fun _=>rfl) (priceRain S h) (Lance.fore (I:=Gear O G) hX)
 refine ⟨fun i=>p i + A i,s,D.hear _ _ hp hA,hs,?_⟩
 intro i b hB hh; obtain ⟨h1,h2,h3⟩:=Hs i b hB hh;refine ⟨?_,h2,h1⟩
 unfold SliceSide.car;rw [ident hg _ ((S.leaders i).2.main) (S.price hg hΓ e i|>.1) h0,victim_r, S.front]
 exact (h3.add (HA i) (by have he:=D.safe _ hp i; positivity) (D.safe _ hA i)).mono le_rfl (le_of_eq (add_assoc ..)) (fun _=>le_rfl)

theorem ends (S S':SliceSide Γ H K Z){w:ℕ→ℕ→O→ℝ}(h:Pay S hΓ D w e r)(h':Pay S' hΓ D w e r)
    (he: Live r e)(h0:0<e){d:O→ℝ}(hd:D.cheap d)(hF:FairT (D:=D) (K:=K) (Γ:=Γ) (G:=G) S.fine S'.fine (needs H e r) d)
    (ht:Book D S.letters S'.letters w d e r)(hv:Book D (S.ample hΓ) (S'.ample hΓ) (coats H) d e r)
    (ha:Lapel D (w e r) (fun x=>S.letters x r e))(hb:Lapel D (w e r) (fun x=>S'.letters x r e))
    (hQ:∀ i,Held (carpet _) (coats H e r i) (h.ζ i) (S'.top i))(hn:Change (I:=Gear O G) D (coats H e r) S.top S'.top):
 ∃ p q s:O→ℝ,D.cheap p∧D.Good q∧D.cheap s∧∀ (i:O)(b:ℝ), 0≤ b → Held (carpet _) (w e r i) b (S.letters i r e-S'.letters i r e)→
    Held (carpet _) (coats H e r i) (b/Real.sqrt ((Γ i).L.val:ℝ)+p i) (S.car hg hΓ i r e-S'.car hg hΓ i r e) ∧ Held (carpet _) (coats H e r i) (q i*b+s i) (S.ample hΓ i r e - S'.ample hΓ i r e):=by
 have hhub (S:SliceSide Γ H K Z)(h:Pay S hΓ D w e r)(ha:Lapel D (w e r) (fun x=> S.letters x r e))(ht:∀ i q,Earlier e r i q→Lapel D (w i q) (fun x=> S.letters x q i))(hv:∀ i q,Earlier e r i q→Lapel D (coats H i q) (fun x=>S.ample hΓ x q i)):
    Lapel D (needs H e r) (S.hub hΓ e r):=by
    obtain ⟨p,s,hp,hs,H⟩:=hires hg S h he h0 ht hv
    obtain ⟨b,hb,h⟩:=ha; exact ⟨_,D.hear _ _ (D.moreover _ _ hs hb) hs,fun i=>(H i (b i) (D.safe _ hb i) (h i)).2.2⟩
 have hh:= hhub S h ha (fun i j he=> Lance.fore (I:=Gear O G) (ht _ _ he)) (fun i j he=> Lance.fore (I:=Gear O G) (hv _ _ he)); have hh':= hhub S' h' hb (fun i j he=> Lance.until (I:=Gear O G) (ht _ _ he)) (fun i j he=> Lance.until (I:=Gear O G) (hv _ _ he))
 obtain ⟨c,hc,hC⟩:= Ducat.amber (A:=S.coarse) (A':=S'.coarse) h.loan (fun x=>tiny D hd x) hF ht (S.lowers hg hΓ S' hv h0) (fun i=>(S.bulbs i).ethos) (fun i=>(S'.bulbs i).ethos) (fun i=>(S.price hg hΓ e i).2) (fun i=>(S'.price hg hΓ e i).2) (fun i=> S.overlook hg hΓ h0 i) (fun i=> S'.overlook hg hΓ h0 i) hb S.aligned S'.aligned h0 he.1
 obtain ⟨p,q,s,hp,hq,hs,ht⟩:= double (hΓ:=hΓ) (R:=S.links hΓ e) (R':=S'.links hΓ e) (F:=S.hub hΓ e r) (F':=S'.hub hΓ e r) hg h.heroes (h.loan.fresh _ _) S.leaders S'.leaders S.bulbs S'.bulbs he h0 (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) hh hh' ⟨_,D.awe _ _ hc hd,hC⟩ (fun i=>⟨h.sure i,hQ i⟩) hn
 have hry:=offer hg hv (fun x=> (S.price hg hΓ e x).1) (fun x=> (S'.price hg hΓ e x).1) (fun a b x=> ((H x).tag a b).1) (fun x=>tiny D hd x) (fun a n hh hj i=> ?_) -- H renamed palette
 case refine_1=> -- copy
   have hW:=h.loan.scant _ _ hh hj i
   apply ((H i).tag e r).2.1.trans (hW.trans _);unfold trail;apply (div_le_self (by have he:= ((H i).tag a n).1; unfold coats; positivity) (by norm_num)).trans;exact div_le_self ((H i).tag a n).1.le (by norm_cast;unfold RG08.Mount.rank;omega)
 obtain ⟨b,hb,Hb⟩:= Lance.berry (I:=Gear O G) hry hd
 refine ⟨fun i=>p i+b i,q,s,D.lasts _ _ hp hb,hq,hs,?_⟩
 intro i B hB hT; obtain ⟨h1,h2⟩:= ht i B hB hT;refine ⟨?_,h2⟩
 unfold SliceSide.car;rw [ident hg _ (S.leaders i).2.main (S.price hg hΓ e i).1 h0,ident hg _ (S'.leaders i).2.main (S'.price hg hΓ e i).1 h0,add_sub_add_comm,←add_assoc,victim_r,victim_r,S.front,S'.front]
 exact h1.add (Hb i) (by have he:=tiny D hp i; positivity) (tiny D hb i)
end YM.RG08.Ducat
