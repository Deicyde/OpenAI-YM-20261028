import YM.RG08.Ducat.Gallery

/-! # Cutoff variance in unchanged packet. Don't request cutoff comparisons of the parallel
 lifted all-curvature map (could be costed post-only if available).
 -/
noncomputable section
namespace YM.RG08.Ducat
open Filter Function Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior
open scoped Classical BigOperators PowerSeries Topology
set_option autoImplicit false
variable {O:Type} {G:Gauge} {P:Patch}{K:RG.KernelChoices}{A A':Bed}{Z:ChartRatio G}
variable {e r:ℕ}
abbrev Lancer {G:Gauge}(P:Patch)(K:RG.KernelChoices)(A:Bed)(F:Gird G r):Gird G r:=
 Anchor.extend 1 (Forms.raft (repeatLine (Prism.rains P K A) (RG08.Mount.rank r)) (Cairn.box _ (Carrel.completed F (stick r) (RG08.Mount.rank r))))
lemma billed {M:Kernel (TypeFace 2) (TypeFace 2)}{F:Gird G r}(hK:Duo G P K A M)(h:Honor G (RG08.Mount.rank r) F):voucher M F=Lancer P K A F:=by
 obtain ⟨hc,s,p,hs,hp,H⟩:=h; unfold Lancer;rw [surf,complete_top _ _ hc H hp hs,hK r F s p hs hp hc.path hc.beam H]
private lemma param{M:Kernel (TypeFace 2) (TypeFace 2)}{X Y:Gird G r}(hK:Duo G P K A M)(hX:Honor G (RG08.Mount.rank r) X)(hY:Honor G (RG08.Mount.rank r) Y){v p:ℝ}(hp:0<v)(hg:Priced v p (Prism.rains (G:=G) P K A)):
 voucher M X-voucher M Y=voucher M (X-Y):=by
 rw [billed hK hX,billed hK hY,billed hK (hX.minus hY)]
 obtain ⟨h,s,t,hs,ht,hR⟩:=hX; obtain ⟨hF,u,c,hu,hc,hT⟩:=hY
 let n:= RG08.Mount.rank r
 have he: ∀ (Φ:Gird G r)(v b:ℝ),Held (carpet _) v b Φ → 0 ≤ b → 0 < v → ∃ v' b':ℝ,0<v'∧0≤b'∧Held (carpet _) v' b' (Cairn.box P (completed Φ (stick r) n)):=by
   intro F w b h hb hw
   have ht : 0<w/(n:ℝ)/32:=by unfold n;unfold RG08.Mount.rank;positivity
   exact ⟨_,_,ht,mul_nonneg (Real.exp_nonneg _) (mul_nonneg (poem_pos ..) hb),Cairn.box_cost (poem_held h hb hw) ht.le P⟩
 unfold Lancer;rw [Carrel.cracks (σ:=min s u) X Y (stick r) (0:Fin n) (p:=max t c) (ht.trans (le_max_left ..)) (lt_min hs hu) (hR.mono (min_le_left ..) (le_max_left ..) (fun _=>le_rfl)) (hT.mono (min_le_right ..) (le_max_right ..) (fun _=>le_rfl)),Cairn.box_sub,linear_sub hg hp (Nat.zero_lt_succ _) (he _ s t hR ht hs) (he _ u c hT hc hu), hinged]

variable (h:P.Branches K G){C T C' T':Castle G}
def oyster (B B':Bed)(C C':Castle G)(T T':Castle G)(Z:ChartRatio G)(A A':Bed)(e r:ℕ):=page h B A C T Z e r-page h B' A' C' T' Z e r -- order fine B coarse A
lemma swing' {M M':Kernel (TypeFace 2) (TypeFace 2)}(hK:Duo G P K A M)(hKK:Duo G P K A' M')(hC:Fair C)(hT:Fair C'){v p:ℝ}(hp:0<v)(hg:Priced v p (Prism.rains (G:=G) P K A))(h0:Priced v p (Prism.rains (G:=G) P K A'))(B B':Bed)(he:0<e)(hr:r ≤ e):
 oyster h A A' C C' T T' Z B B' e r=voucher M (C r e - C' r e) + ((sweep h A C T Z e r - sweep h A' C' T' Z e r) + (Lancer P K A (C' r e)-Lancer P K A' (C' r e))):=by
 rw [oyster,absorbs M hK hg hp hC he hr, absorbs M' hKK h0 hp hT he hr,←param hK (hC.honor r e) (hT.honor r e) hp hg,billed hKK (hT.honor r e),billed hK (hT.honor r e)];abel

variable {Γ:O→Patch}{D:Exchange O}{d v:O→ℝ}{w:ℕ→ℕ→O→ℝ}
variable {X Y:O→Gird G r}{B B':O→Bed}{hq:∀ i,(Γ i).Branches K G}
lemma lancer (hF:Quarrying D Γ w v e hq Z)(hd:∀ i,0≤d i)(ht:FairT (D:=D) (K:=K) (Γ:=Γ) (G:=G) B B' v d)(h:Ducat.Mount D (w e r) d X Y)(he:r ≤ e): Ducat.Mount D v d (fun i=> Lancer (Γ i) K (B i) (X i)) fun i=> Lancer (Γ i) K (B' i) (Y i):=
 extension <| Lance.reserve (fun i=>(hF.roof i).1) hd (Ducat.box (fun i=>(hF.roof i).1) hd _ (composed (hF.fresh _ _) hd h (hF.duty (RG08.Mount.rank r) (by unfold RG08.Mount.rank; omega) e r le_rfl he) (Nat.zero_lt_succ _)) (hF.meet _ _ le_rfl he) (fun i=>(hF.roof i).2)) ht.1

lemma amber {C C' T T':O→Castle G}{M M':O→ Kernel (TypeFace 2) (TypeFace 2)}{A A':O→Bed}{q:ℕ→ℕ→O→ℝ}(hS:Reckons D Γ w q v e r hq Z)(hd:∀ x,0 ≤ d x)(ht:FairT (D:=D) (K:=K) (Γ:=Γ) (G:=G) B B' v d)
    (hC:Book D C C' w d e r)(hR:Book D T T' q d e r)(h0:∀ x,Fair (C x))(h1:∀ x,Fair (C' x))(h2:∀ x,Fair (T x))(h3:∀ x,Fair (T' x))(hE:∀ x,overlooks (T x) e)(hf:∀ x,overlooks (T' x) e)
    (ht':Lapel D (w e r) (fun i=>C' i r e))(hM:∀ i,Duo G (Γ i) K (B i) (M i))(hN:∀ i,Duo G (Γ i) K (B' i) (M' i))(he:0<e)(hr:r ≤ e):
 ∃ p,D.Good p ∧ ∀ i,Held (carpet (Tone G.ColorIndex)) (v i) (p i*d i)
    (oyster (hq i) (B i) (B' i) (C i) (C' i) (T i) (T' i) Z (A i) (A' i) e r - voucher (M i) (C i r e-C' i r e)):=by
 obtain ⟨p,hp,H⟩:= sweeping hS hd ht hC hR h0 h1 h2 h3 hE hf hr
 have hx:Mount D (w e r) d (fun i=>C' i r e) (fun i=>C' i r e):=Bound.join ht'
 obtain ⟨x,hx,Hx⟩:= lancer hS.toQuarrying hd ht hx hr
 obtain ⟨n,_,hω⟩:=ht.1.1
 refine ⟨fun i=>p i+x i,D.hear _ _ hp hx,fun i=>?_⟩
 rw [swing' _ (hM i) (hN i) (h0 i) (h1 i) (hS.roof i).1 (hω i).1 (hω i).2.1 _ _ he hr,add_sub_cancel_left,add_mul]
 exact (H i|>.compare).add (Hx i|>.compare) (mul_nonneg (D.safe _ hp _) (hd _)) (mul_nonneg (D.safe _ hx _) (hd _))
end YM.RG08.Ducat
