import YM.RG08.Ducat.Wave

/-! # Remainder before coupling closure. Importantly inhale both with their own heritage, using
 exactly the finite alignment and analytic transport; resulting strict Y Cot contains NO
 same-rank input hypotheses. For variance add remaining geometry turnover with that other
 (absolute) representative. -/
noncomputable section
namespace YM.RG08.Ducat
open Filter Function Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior
open scoped Classical BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{P:Patch}{K:RG.KernelChoices}{A B:Bed}{C R:Castle G}{Z:ChartRatio G}
variable {e r:ℕ} {h:P.Branches K G}

-- exact summability through all rank terms at this step, just need some τ for the m matrix. assume Warm & Tagged there.
lemma linear_sub {I J:Type}[Fintype I][Fintype J]{X:Kernel I J}{σ p:ℝ}(he:Priced σ p X)(h:0<σ){n:ℕ}{V A:Flake n (Market I)}(hn:0<n)
     (hV:∃ s p:ℝ,0<s∧0 ≤ p∧ Held (carpet _) s p V)(ha:∃ s p:ℝ,0<s∧0 ≤ p∧Held (carpet _) s p A):
 Forms.raft (repeatLine X n) (V-A)=Forms.raft (repeatLine X n) V-Forms.raft (repeatLine X n) A:=by
 let L:=repeatLine X n
 have hh (V:Flake n (Market I))(w b:ℝ)(hw:0<w)(hp:0≤b)(ht:Held (carpet _) w b V)(y:Tape n (Market J)): Summable (Forms.vat L V y):=by
    let t:= min σ w;have hv:=lt_min h hw
    have hp':Priced t p X:=he.mono (min_le_left ..) le_rfl
    let H:=Isles.tagged (Spar.cardDeck hp') hv
    obtain ⟨hz,hQ⟩:=cover_cross (Gm:=L) (fun i=>H) hv.le
    exact (raft_sum hn (ht.mono (min_le_right ..) le_rfl (fun _=>le_rfl)) hp hz hQ y).of_norm
 funext i;obtain ⟨s,u,hu,hp,hV⟩:=hV;obtain ⟨t,d,ht,hd,hA⟩:=ha;change (∑' y:Tape n (Market I),(V-A) y*design L y i)= (∑' y:Tape n (Market I),V y*design L y i)- ∑' y:Tape n (Market I),A y*design L y i
 simp_rw [Pi.sub_apply,sub_mul];exact ((hh _ _ _ hu hp hV i).tsum_sub (hh _ _ _ ht hd hA i))

private lemma mines (h:P.Branches K G)(he:Fair C)(hr: 0<e)(hp:r ≤ e):∃ s c:ℝ,0<s ∧ 0 ≤ c ∧ Held (carpet _) s c (mine h C Z e r):=by
 let F:=inlet h C Z
 have hx κ:slaw F κ:=by
    by_cases hi:0<κ
    · intro n;unfold F inlet;rw [if_pos hi]; exact (((castle_room P C he.rails κ).add (bell_room h κ)).neg.add (dusk_room P Z κ)) n
    intro n;refine ⟨1,0,zero_lt_one,le_rfl,?_⟩;unfold F inlet;rw [if_neg hi];exact zero_held
 let n:=RG08.Mount.rank r
 obtain ⟨s,x,hs,hX,h⟩:=hx e n
 obtain ⟨he,w,W,hw,hW,H⟩:=he.honor r e -- h shadowing h: patch etc
 have hC:=poem_held (n:=n) H hW hw
 let t:=w/(n:ℝ)/32;have ht:0<t:=by unfold t n RG08.Mount.rank;positivity
 have hF:=Cairn.box_cost (σ:=t) hC ht.le P
 let p:=Real.exp (8*t)*(poem G r n w*W)
 have hp':0 ≤ p:=mul_nonneg (Real.exp_nonneg _) (mul_nonneg (poem_pos ..) hW)
 rw [show mine _ _ _ _ _=F e n+_ from sub_eq_iff_eq_add.mp (self_inlet _ _ _ hr hp).symm] -- A=B-C -> B=A+C ? eq_add_of_sub_eq 
 refine ⟨_,_,lt_min hs ht,add_nonneg hX hp',(h.mono (min_le_left ..) le_rfl (fun _=>le_rfl)).add (hF.mono (min_le_right ..) le_rfl (fun _=>le_rfl)) hX hp'⟩

def sweep (h:P.Branches K G)(A:Bed)(C R:Castle G)(Z:ChartRatio G)(e r:ℕ):Gird G r:=
 let n:=RG08.Mount.rank r; Anchor.extend 1 (-raft (repeatLine (Prism.rains P K A) n) (mine h C Z e r)-Steam.strict (Prism.ice P K A) (inlet h C Z) (Prism.rains P K A) e n - demand R e n)

def page (h:P.Branches K G)(A B:Bed)(C R:Castle G)(Z:ChartRatio G)(e r:ℕ):Gird G r:=
 Anchor.extend 1 ((-(Prism.vault G P K h C Z A B) - demand R) e (RG08.Mount.rank r))

lemma absorbs {σ p:ℝ}(M:Kernel (TypeFace 2) (TypeFace 2))(hT:Duo G P K A M)(hP:Priced σ p (Prism.rains (G:=G) P K A))(hf:0<σ)(hC:Fair C)(he:0<e)(hr:r ≤ e):page h A B C R Z e r=voucher M (C r e)+sweep h A C R Z e r:=by
 obtain ⟨hh,w,W,hw,hW,H⟩:=hC.honor r e
 let n:=RG08.Mount.rank r
 have ht:=poem_held (n:=n) H hW hw
 have hs:0<w/(n:ℝ)/32:=by unfold n RG08.Mount.rank;positivity
 have hQ:= Cairn.box_cost ht hs.le P
 let f:=inlet h C Z;let D:=Cairn.box P (completed (C r e) (stick r) n)
 have hb:=linear_sub (V:=mine h C Z e r) (A:=D) hP hf (by unfold RG08.Mount.rank;omega) (mines h hC he hr) ⟨_,_,hs,mul_nonneg (Real.exp_nonneg _) (mul_nonneg (poem_pos ..) hW),hQ⟩
 have hy := self_inlet h C Z he hr
 -- exact params on μ,B0 annotate G
 let μ:= Prism.rains (G:=G) P K A;let B0:=Prism.ice (G:=G) P K A
 have hp':Prism.bare (Prism.alum G B) e n=0:=by unfold Prism.bare;split_ifs <;> first|rfl | omega
 unfold page Prism.vault Prism.mill Steam.allG
 change Anchor.extend 1 (-(Prism.bare (Prism.alum G B) e n+(Forms.raft (repeatLine μ n) (f e n)+Steam.strict B0 f μ e n))-demand R e n)=_
 rw [hp',zero_add, show f e n=mine h C Z e r-D from hy,hb,surf (completed (C r e) (stick r) n)] -- D abbrev unfold
 rw [complete_top _ _ hh H hW hw]
 let Z0:=braces (Cell.plotted P K G A) (compress 1 (picture G.ColorIndex n (C r e)))
 have h1:=hT r (C r e) w W hw hW hh.path hh.beam H
 have add0(F V X U:Flake n (Market (Loc G 1))):Anchor.extend 1 (-(F-V+X)-U)=Anchor.extend 1 V+ Anchor.extend 1 (-F-X-U):=by
   ext i; unfold Anchor.extend;dsimp only [Pi.add_apply];split <;> simp ; abel
 rw [add0,h1]; rfl

variable {O:Type}{w q:ℕ→ℕ→O→ℝ}{v d:O→ℝ}{D:Exchange O}{I:O→Type}
variable {C U R V:O→Castle G}{Γ:O→Patch}
variable {h:∀ x,(Γ x).Branches K G}
lemma hinged {I:Type}{n:ℕ}(F V: Flake n (Carrel.Mix I 1)): Anchor.extend 1 (F-V)=Anchor.extend 1 F-Anchor.extend 1 V:=by ext x;unfold Anchor.extend;dsimp only [Pi.sub_apply];split <;> first| rfl|simp
lemma extension {I:Type}[Fintype I]{F V:O→Flake (RG08.Mount.rank r) (Carrel.Mix I 1)}(ht: Lance (I:=fun _=>Kind I 1) D v d F V):Lance (I:=fun _=>Tone I) D v d (fun i=>Anchor.extend 1 (F i)) (fun i=>Anchor.extend 1 (V i)):=by
 obtain ⟨p,hp,h⟩:=ht;refine ⟨_,hp,fun i=>⟨D.safe _ hp _,Anchor.expand_cost (h i).near,Anchor.expand_cost (h i).far,?_⟩⟩
 rw [← hinged];exact Anchor.expand_cost (h i).compare

structure Reckons (D:Exchange O)(Γ:O→Patch)(w q:ℕ→ℕ→O→ℝ)(v:O→ℝ)(e r:ℕ)(h:∀ x,(Γ x).Branches K G)(Z:ChartRatio G):Prop extends Quarrying D Γ w v e h Z where
 south:∀ i r x,0<q i r x
 retreat:Slice (G:=G) v e (RG08.Mount.rank r) D q
 scant:∀ i j,i<e → j ≤ i → ∀ x,v x ≤ trail j (q i j) x

def FairT (A A':O→Bed)(v d:O→ℝ):Prop:= Counter (D:=D) (fun x=>Tack.Head (Γ x) G) (fun _=>Loc G 1) v d (fun x=>Prism.rains (Γ x) K (A x)) (fun x=>Prism.rains (Γ x) K (A' x))∧
 Counter (D:=D) (fun x=>Tack.Head (Γ x) G) (fun x=>Tack.Head (Γ x) G) v d (fun x=>Prism.ice (Γ x) K (A x)) (fun x=>Prism.ice (Γ x) K (A' x))
lemma sweeping {A A':O→Bed}(hS:Reckons D Γ w q v e r h Z)(hd:∀ x,0≤d x)(ht:FairT (D:=D) (K:=K) (Γ:=Γ) (G:=G) A A' v d)
    (hC:Book D C U w d e r)(hR:Book D R V q d e r)(h0:∀ x,Fair (C x))(h1:∀ x,Fair (U x))(h2:∀ x,Fair (R x))(h3:∀ x,Fair (V x))(he:∀ x,overlooks (R x) e)(hf:∀ x,overlooks (V x) e)(hr:r ≤ e): Ducat.Mount D v d (fun i=>sweep (h i) (A i) (C i) (R i) Z e r) (fun i=>sweep (h i) (A' i) (U i) (V i) Z e r):=by
 let n:=RG08.Mount.rank r
 have hN:0<n:=Nat.zero_lt_succ _
 have hv(x):0<v x:=(hS.roof x).1
 apply extension
 refine (((Lance.reserve hv hd (self_lane h Z hS.toQuarrying hC h0 h1 hd hr) ht.1).opposite).sub ?_ hd).sub (pinched hS.south hd hR h2 h3 he hf hS.retreat hN hS.scant) hd
 exact receipt_step hv hd ht.1 ht.2 _ _ (fun i=>inlet_eligible (h i) Z (h0 i|>.rails)) (fun i=>inlet_eligible (h i) Z (h1 i|>.rails)) _ _ (fun i k H=>eligible_lane h Z hS.toQuarrying hC h0 h1 hd H) hN
end YM.RG08.Ducat
