import YM.RG08.Weald.Broadcast
import YM.RG08.Sedan.Mill

/-! # Before adjacent coupling replacement -- FULL gauge conservation on
 single cover report, arbitrary l and k-hal dependence w/o masks. Export
qualitative recursive constructor and *secondary* Ward theorem later. Handles
cofinal periods via header with K true. -/
noncomputable section
namespace YM.RG08.Weald
open Jetty Skiff Lattice Isles Forms Pert.Bulk Function Finset Laurent Filter Packets Steam Mount
open Room Gallery Camera MvPolynomial Glyph Hatch Quarry
open Exterior RG Wilson Stationary Precision Tack Tree Prism Slate Work.F05 Sedan
open scoped Topology BigOperators ENNReal Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix InnerProductSpace
set_option autoImplicit false
variable {G:Gauge}(P:Patch)(K:KernelChoices)(A B:Bed)(C:Castle G)(Z:ChartRatio G)
variable {l d:ℕ}

-- preserve l+e and transfer oracle
structure Permit {I:Type}[Fintype I](D:ℕ)(l:ℕ)(M:GrainS (Market I)):Prop where
 lit : Skiff.Lit l M
 fine : Trickle.Combed M
 price : Growth D M
lemma permit_baked (o:Site P.L){M:GrainS (Ed G Cover)}(hs:Permit d l M):Permit d l (plank P o M):=⟨braids P o hs.lit, (fun f i k=>Hatch.bowl _ (hs.fine f i k)),grip P o hs.price⟩

private lemma lit_breath {I:Type}{V:Steam.Grain I}{M:GrainS I}(he:Skiff.Lit l M)(hv:Eligible V)(Γ:Forms.Line I)(a:ℝ):Skiff.Lit l (Skiff.spin l Γ V M a):=by
 intro i n; contrapose!; intro hin; unfold Skiff.spin;apply sum_eq_zero;intro j hj
 rw [show skate Γ V M j i n=0 from Classical.not_not.mp fun h=>show False from by have := (Skiff.full he hv h).2;omega,smul_zero]
private lemma lit_mean {I J:Type}{M:GrainS I}(h:Skiff.Lit l M)(K:I→J→ℝ):Skiff.Lit l (Trickle.mouth K M):=by
 intro i n; contrapose!;intro hin;unfold Trickle.mouth Skiff.picture Skiff.reel decker; rw [show M i n=0 from Classical.not_not.mp fun hM=>show False from by have :=h _ _ hM; omega];ext; simp

lemma permit_woke {H:P.Branches K G}{M:GrainS (Market (Tack.Head P G))}{σ p:ℝ}(he:Mount.Stable C)(hs:Cell.Warm G K P A σ p)(ht:0<σ)(hu:σ≤1)(hw:Permit d l M): Permit d l (vessel P K A C Z H l M):=by
 refine ⟨lit_mean (lit_breath hw.lit (inlet_eligible H Z he) _ _) _,fun f e n=>?_,fun e n=>?_⟩
 · rw [vessel];rw [Trickle.water]; apply Sedan.raft_symm
   unfold Trickle.brook Skiff.spin;rw [Trickle.during_sum]
   have hg {R I:Type}{n:ℕ}(s:Finset R)(f:R→Flake n I)(h:∀ i, Forms.Sym (f i)):Forms.Sym (s.sum f):=by
      induction s using Finset.induction_on with
      | empty=> exact Forms.Sym.zero
      | @insert i t hi ih=> rw [Finset.sum_insert hi];exact (h i).add ih
   apply hg;intro i;rw [Trickle.during_smul]; exact (Trickle.comb (Prism.ice P K A) (inlet H C Z) hw.fine i f e n).smul _
 obtain ⟨τ,k,h⟩:= won P K A C Z H M hw.price hw.lit he hs ht hu e
 obtain ⟨C,h⟩:=h e le_rfl n
 exact ⟨h.openP,τ,k,C,h.cost,h.lead⟩

-- preOrigin mark from current fine W to coarse after push, same positive orientation Legend.
def carrier (H:P.Branches K G)(l:ℕ)(F:GrainS (Ed G Cover))(o:Site P.L):GrainS (Ed G Cover):=vessel P K A C Z H l (plank P o F)
variable (o:Site P.L)
set_option maxHeartbeats 720000 in
lemma instruction (c:Side){σ p τ u:ℝ}{H:P.Branches K G}(M:GrainS (Ed G Cover))(hM:Permit d l M)(he:Calls l M)
  (hC:Mount.Stable C)(hW:Cell.Warm G K P A σ p)(hZ:LocalRatio Z)(hc: Prism.Proceed C A (c*P.L)){L:Matrix (Body 1 (c*P.L)) (Body 1 c) ℝ}{v:Clip}(hf:Floor A v (c*P.L) τ u)(hi:Inputs (rung P K c) L (A.metric.acts (c*P.L)) (B.metric.acts c))
  (g:G.El)(f:Pearl):
  let U:=weldF P K A C Z c H l (plank P o M)
  ; belt (Weald.own g) (Trickle.mark l U f)= belt (fun i:Ed G (Site c)=>Room.rod (i.1, Sum.inl i.2)) (Trickle.mark l U f):=by
 intro U
 let S:=rung P K c;let F:=Line.green S
 let W:=Operandi S F A B Z hZ g
 let Y:=Weald.raft P (plank P o M) c
 have heP:=braised P (c:=c) (braids P o hM.lit)
 have hP:Trickle.Combed Y:=fun z i n=>Hatch.bowl _ (Hatch.bowl _ (hM.fine z i n))
 have hr:= welcomed P K F A B Z hZ g o M he hM.price.pops f
 obtain ⟨hu,hw,ht⟩:=hW.invert c
 let S₀:=Line.habitat P K c
 have hT: (grace G S F A B).Flourishes:= (illuminated G S₀ F A B (Γ:=Line.NativeLine S G A) (Given.mk hu hw ht) hf hi).1
 have h:= Wisp.rooted S F A B (Quarry.badge c) id W H hC hZ hc hT Y Y f heP hP heP hP hr
 unfold Wisp.review at h
 change (belt _) (Trickle.mark _ (Trickle.mouth (script _ _) (Skiff.spin _ (press _ _) _ Y 1)) _)=_ at h
 rw [ready_phases P K A B c hW,ready_mean P K A B c hW] at h
 change belt (fun i:Ed G (Site c)=>rescaleFields W.map (.inr i)) (Trickle.mark l U f)=belt (fun i:Ed G (Site c)=>Room.rod (.inr (Quarry.badge (G:=G) c i))) _ at h
 let z:Camera.Raw (Key F G) (Plot G (Site c))→Port (Plot G (Site c)):=Sum.elim (fun _=>0) rod
 have huup {W Y: Ed G (Site c)→Port (Camera.Raw (Key F G) (Plot G (Site c)))} {x:Port (Ed G (Site c))}(h:belt W x=belt Y x):belt (fun i=>belt z (W i)) x=belt (fun i=>belt z (Y i)) x:=by
    have he' (W)(x:Port (Ed G (Site c))):belt z (belt (J:=Camera.Raw (Key F G) (Plot G (Site c))) W x)=belt (fun i=>belt z (W i)) x:=by
       change ((belt z).comp (belt W)) x=_;rw [switched]
    rw [←he',←he',h]
 have hG:=huup h
 have hp(q:Ed G (Site c)): belt z (rescaleFields W.map (.inr q))= Weald.own g q:=by
    apply lamp;intro x; rw [Gallery.fugue]
    let r : Plot G (Site c)→Camera.Raw (Key F G) (Plot G (Site c)):=fun i=>.inr i
    change breath (fun i=>breath (kiosk x) (z i)) (eye (fun t=> arch (Quarry.badge (G:=G) c) (raise c g) (t ∘ r) q))=_
    rw [Quarry.prophet g q r,owned]
    unfold Weald.route; apply congrArg (fun v:foil G→Dig=>breath v (eye ((Quarry.hot g).fare _))); funext i; exact Gallery.bases_x (kiosk x) _ 
 change (belt (fun q:Ed G (Site c)=>belt z (rescaleFields W.map (.inr q)))) (Trickle.mark l U f)=_ at hG
 rw [_root_.funext hp] at hG;simp_rw [belt_x] at hG;exact hG

/-- Exact pre-reset gauge recursion each cover kernel (θ-independent,
 includes field-independent mark). -/
theorem self (H:P.Branches K G)(M:GrainS (Ed G Cover))(h:Foyer P K A B C Z)(hM:Permit d l M)(he:Calls l M):
   Permit d l (carrier P K A C Z H l M o) ∧ Calls l (carrier P K A C Z H l M o):=by
 obtain ⟨hC,⟨σ,p,hσ,hp,hW⟩,hB,hZ,hs,⟨a,b,v,hf⟩,⟨N,hN,hL⟩⟩:=h
 let X:=plank P o M
 have hx:Permit d l X:=permit_baked P o hM
 refine ⟨permit_woke P K A C Z hC hW hσ hp hx,fun f x y r=>?_⟩
 let z:= Quarry.art x y;let W:=portrait (hot r) z
 have ht:∀ᶠ k in atTop, mint l (weldF P K A C Z (Isles.chain (N k)) H l X) f (Gallery.native _ W) = mint l (weldF P K A C Z (Isles.chain (N k)) H l X) f (Gallery.native _ x):=by
   filter_upwards [Quarry.rear (hot r) z (Isles.rise.comp hN)] with k hk
   let Q:=Isles.chain (N k); obtain ⟨L,h'⟩:=hL k
   have ht:=congrArg (breath (Gallery.native Q z).get) (instruction P K A B C Z o Q (H:=H) M hM he hC hW hZ (hs _) (hf _) h' r f)
   rw [Gallery.fugue,Gallery.fugue] at ht; simp_rw [owned,bases_x] at ht
   have hP:(Gallery.native Q W).get=(fun j=>route Q r (Gallery.native Q z).get j):= _root_.funext (fun i=> hk i)
   change mint l _ _ _= _;rw [←told,←told,hP];exact ht
 ext e:1;change tap _ _=tap _ _
 obtain ⟨τ,u,hU⟩:= won P K A C Z H X hx.price hx.lit hC hW hσ hp e
 have hv: Tendsto (fun k:ℕ=>tap e (mint l (weldF P K A C Z (Isles.chain (N k)) H l X) f (Gallery.native _ W))) atTop (𝓝 (tap e (mint l (carrier P K A C Z H l M o) f W))):= (ascribed W f e hU).comp hN
 have hc:Tendsto (fun k=>tap e (mint l (weldF P K A C Z (Isles.chain (N k)) H l X) f (Gallery.native _ W))) atTop (𝓝 (tap e (mint l (carrier P K A C Z H l M o) f x))):= Tendsto.congr' (ht.mono (fun _ hi=>congrArg _ hi.symm)) ((ascribed x f e hU).comp hN)
 exact tendsto_nhds_unique hc hv
end YM.RG08.Weald
