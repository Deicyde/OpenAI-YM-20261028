import YM.TraceExtension.Terrace.Trail
import YM.TraceExtension.Terrace.CabinBook
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Trace.Terrace.Glade
open Function Filter Finset Lattice RG Wilson Labels Source Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price MergeProof.East Further.CorrectedLift Ward Climb Analysis Work Weir StressFlux
open Further.PhysicalPeriodLimitF933 Shunt PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells Pressure
open Motion MergeProof MergeProof.Accent Relay ProofPorts.GridRealModelsEstimates20261012
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
section linear
variable {j k i N p d:ℕ}
lemma linC (hk:k ≤ N)(a:ℝ)(V : Config G (C.side k p)→ℂ): backTo C.path N p hk (a • V)=a • backTo C.path N p hk V:=by simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact backTo_linear ..
lemma toss (x:C.label d)(c:ℝ): C.O N p (c • x) 0=c • C.O N p x 0:= ((C.linearO N p d 0).mk' _ |>.restrictScalars ℝ).map_smul ..
lemma toss_sub (x y:C.label d): C.O N p (x-y) 0=C.O N p x 0-C.O N p y 0:= ((C.linearO N p d 0).mk' _).map_sub ..
lemma conn {n:Side}{X:Set (Site n)}(V:Film G n) (h:Interior X V)(c:ℝ): Interior X (c • V):=by rw[RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact h.scale _
lemma fade {n:Side}(S:Tiling n)(V:Film G n)(β c:ℝ): S.rootTest β (c • V)= ‖c‖*S.rootTest β V:=by rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact (root_smul S β (c:ℂ) V).trans (by simp)
lemma stroll (N p k:ℕ)(h:k ≤ N)(f g:Film G (C.side k p))(hf:Envelope f)(hg:Envelope g): backTo C.path N p h (f-g)= backTo C.path N p h f - backTo C.path N p h g:=by
    rw [sub_eq_add_neg, backTo_add C.path N p h hf (show Envelope (-g) from ?_)]; swap; · rw[← neg_one_smul ℂ g]; exact (Envelope.constC _).mulC hg
    rw [← neg_one_smul ℂ g, backTo_linear, neg_one_smul];rfl
lemma weighing (d j k p:ℕ)(f:Film G (C.side k p)) : (C.S.a j/C.S.a k)^d • f=C.S.a j^d • (alto C.path k d • f):=by simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rw [smul_smul]; congr 1; change (((C.S.a j/C.S.a k)^d:ℝ):ℂ)= ↑(C.S.a j^d)* ((↑(C.S.a k):ℂ)^d)⁻¹; push_cast; ring
lemma prelude (W:Bid.Worth) {u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {ζ:ℕ→ℕ→ℝ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
    (hr:Scrim C W u ψ φ δ ζ r D)(H:C.Makes)(a:C.label d)(hj:C.ref d ≤ j)(hv:j≤N)(s:Motion):columns C d j N p (Prism _ s a)=Prism _ s (columns C d j N p a):=by
   obtain ⟨s,b⟩:=s; have ht:=(guarded C H hr (p:=p) hj hv a s).2; have hx:= (guarded C H hr hj hv ((C.labels.level d).act s.ortho a) s (p:=p)).1; cases b; exact ht;exact hx.trans (congr_arg star ht)
end linear
section horizon
variable (H:C.Makes)(θ:PostT C.path.levels)(h:G.Simple)(K:Stock.Tabs C.path.levels)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "T!"=> C.path
local notation "D!"=> C.labels.level 5
variable {W:Bid.Worth} {u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {ζ:ℕ→ℕ→ℝ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (hq:Scrim C W u ψ φ δ ζ r D)
include H θ K h hq
-- send B floats. `y=N sign β.M` .Bill exact through observation clocks.One horizon. integrated root.CNF.
set_option maxHeartbeats 600000 in
lemma tide :∀ᶠ i:ℕ in atTop,∀ p N,let k:=summit C.path.levels i; ∀ h:k<N,let f:=Tau C.path.levels i; let T:=tilesAt C.S p ((stellar A i).le.trans h.le); let q:= (C.S.a i/C.S.a k)^5; let a:=C.S.a i^ (5:ℕ); let t:=(A).clock.hatBeta k; let β:= C.path.β N p k; ∀ (x y: Axis→ Film G (C.side k p))(X Y: Axis→ C.label 5)(l:ℕ),
    (∀ i:Axis,Interior (Push.GridApprox.window 0 l) (x i)∧ Interior (Push.GridApprox.window 0 l) (y i)) →(∀ x:C.label 5, Interior (T.chamber 0) (C.O N p x 0))  → room (A) i k l → (∀ i,∃ v,Bill C N p 5 k (x i) v (X i)) →(∀ i,∃ v,Bill C N p 5 k (y i) v (Y i))→∀ d:Axis,
    let Z:= Reed (Prism (C.labels.level 5)) (X-β • Y); Crown C i N p h.le (Reed (present _) (q • (x-β • y)) d) → Probe C 4 i p N h (a • Z d):=by
    let T:=A; let k':=summit T;let L i:= T.clock.hatBeta (k' i); let F:= D!; let c:=orbitCost F; have Hc:0<c:= zero_lt_one.trans_le (orbitCost_one_le _)
    have hv:= (sapTree h T 1 zero_le_one).sum ((sapTree h T 2 zero_le_two).push (stickK T h θ)) h
    filter_upwards [stageCrown H θ h,open_budget T h θ K,tends_price (C:=C) h θ K 5,(bondB T K).eventually_ge_atTop (C.ref 5),toll_small (x:=230) (by norm_num) hv,((hrate T h).comp (Sstar T)).eventually_ge_atTop (6*c)] with i hΩ hh hi hw hx hb p N k hN T' q a β x y X Y l h₁ hF hL h₂ h₃ d Z hZ
    have hk:i≤k:= (stellar ..|>.le); have hl:k ≤ N:= hN.le; let b:= C.beta N p; let t:=L i; let f:= Tau T i; let E:= f (-430)
    let V:= X-β • Y; let J := q • (x-β • y)
    have hz: β ≤ 2*t:= (H.wilson.represents N p k hl).band.2; have hc:0<β:= Overlay.beta_positive H.wilson hl; have hm:0 < a:=pow_pos (C.S.a_pos _) _
    let j:=basin T K i; have ht:C.ref 5 ≤k:= hw.trans hh.le
    let O(t:C.label 5):= C.O N p (a • t) 0
    have hY(i:Axis): Interior (Push.GridApprox.window 0 l) (J i):= conn _ (Next.UVStress.minus ((h₁ i).1) (conn _ (h₁ i).2 β)) q
    let P d:=backTo C.path N p hl (J d)
    have hP (v): Interior (T'.chamber 0) (P v):=Broom i k N p hk hl _ l (hY v) hL
    let G':= backTo C.path N p hl (Reed (present _) J d)
    have hδ : O (Z d)=Reed (present _) (O ∘ V) d:=by
        let I:= Prism F; rw [show O (Z d)=a • _ from toss (Z d) a,show C.O N p (Z d) 0=_ from readY N p H 5 (ht.trans hl) V d];
        let Q(i):= C.O N p (V i) 0; have he : O ∘ V= a • Q:=funext fun i=> toss (V i) _; unfold Q at he; rw [he,map_smul]; rfl
    have hp' : G'=Reed (present _) P d:= readUp i k N p hk hl J d l hY
    have hV(e:Axis): T'.rootTest b (P e-O (V e)) ≤ f (-200):=by
        let B(g:Config G (C.side k p)→ℂ):=backTo C.path N p hl g; let u:= (q • x) e; let v:= (q • y) e
        have he: P e - O (V e)=(B u- O (X e))- β • (B v-O (Y e)):=by
           have hx: J e= u-β • v:=by unfold u v J; simp[smul_sub,smul_comm q];
           have hb: V e= X e-β • Y e:=rfl; unfold P O B; rw [hx,hb,smul_sub a,smul_comm a β, toss_sub, show C.O N p (β • (a • Y e)) 0=_ from toss (a • Y e) β,stroll N p k hl u (β • v) (cylinder_env (conn (x e) ((h₁ e).1) q)) (cylinder_env (conn v (conn (y e) ((h₁ e).2) q) β)), show backTo C.path N p hl (β • v)=_ from linC hl β v]
           rw [smul_sub]; abel
        have hy (M) (hp: Interior (Push.GridApprox.window 0 l) M)(v:C.label 5) (h:∃ s,Bill C N p 5 k M s v):T'.rootTest b (B (q • M)-O v) ≤ E:=by
           obtain ⟨w,h⟩:=h; change T'.rootTest _ (backTo _ _ _ _ (_ • M)-_)≤_; unfold O; rw [weighing,linC,toss,← smul_sub,fade,Real.norm_of_nonneg]; swap; · positivity [C.S.a_pos i]
           exact (mul_le_mul_of_nonneg_left (h.root i j l (tracks ..) hw hh hL hk hl hp) hm.le).trans hi
        have hp : ‖β‖=β:= Real.norm_of_nonneg hc.le; rw [he]; let t₀:= B u-O (X e); let v₀:= B v-O (Y e); rw [show (B u-O (X e))-β • (B v-O (Y e))= t₀+ (-β) • v₀ from by rw[neg_smul];rfl];
        have hv : Interior (T'.chamber 0) v₀:= Next.UVStress.minus (Broom i k N p hk hl v l (conn _ (h₁ e|>.2) _) hL) (hF _)
        apply ((seamless H N p).semi T' _ _ (Next.UVStress.minus (Broom i k N p hk hl u l (conn _ (h₁ e|>.1) q) hL) (hF _)) (conn _ hv (-β))).trans
        rw[fade,norm_neg,hp];refine (add_le_add (hy (x e) (h₁ e|>.1) _ (h₂ e)) (mul_le_mul_of_nonneg_left (hy (y e) (h₁ e|>.2) _ (h₃ e)) hc.le)).trans ?_
        change E+β*E ≤ _; have he1 : f 230*E=f (-200):=by unfold E f;rw[← Tau_add];norm_num
        exact (le_trans (le_of_eq (b:=(1+β)*E) (by ring)) ((mul_le_mul_of_nonneg_right ((add_le_add_right hz 1).trans hx) (Tau_pos ..|>.le)).trans_eq he1))
    have hA : T'.rootTest b (G'-O (Z d)) ≤ f (-200):=by rw[hδ,hp',← Pi.sub_apply, ← map_sub]; exact (teamW C.S (u:=P-O ∘ V) b (hk.trans hl) d (seamless H N p) (fun e=> Next.UVStress.minus (hP _) (hF _)) (f (-200)) hV).2

    have he(v:Axis): F.coeffSize (columns C 5 k N p (V v)) ≤2+β*2:=by
       obtain ⟨c,hc'⟩:=h₂ v; obtain ⟨t,ht'⟩:=h₃ v; let U:=(nib_linear C H (p:=p) ht hl).mk' _; let G:= U.restrictScalars ℝ
       change F.coeffSize (G (X v-β • Y v))≤_; rw[map_sub,map_smul,sub_eq_add_neg]; apply (Size.add ..).trans; rw[← neg_smul, count_smul,norm_neg,Real.norm_of_nonneg hc.le]; exact add_le_add (majesty _ _ _ hc') (mul_le_mul_of_nonneg_left (majesty _ _ _ ht') hc.le)
    refine ⟨?_,frames_night F ((Bowl F).smul_mem a (blade F V) |> fun H=>Subtype.mk _ H) d, Reed (present _) J d,(Broom i k N p hk hl _ _ (reedRoad _ J d _ hY) hL),hA,fun x z hx g hB hP hL'=> (hΩ N p hl _ hZ g hB hP hL' x z hx).trans (tau_mono _ _ (by norm_num))⟩
    let U:=(nib_linear C H (p:=p) ht hl).mk' _; let L:=U.restrictScalars ℝ
    change F.coeffSize (L (_ • _)) ≤ _; rw [map_smul,count_smul,Real.norm_of_nonneg hm.le]; apply mul_le_mul_of_nonneg_left _ hm.le
    have hv : L (Z d)= Reed (Prism _) (fun i=> L (V i)) d:=by unfold Z; rw [reedEq,reedEq,map_sum]; refine sum_congr rfl (fun i _=>?_); rw [map_smul]; exact congr_arg ( (rent*hued i d) • ·) (prelude W hq H (V (prev i d)) ht hl i)
    rw[hv]; apply le_trans (blade_cost _ _ _ (fun i=>he i) d); change c*(2+β*2) ≤ t^4; have hh : 6*c ≤ t:= hb;have ht:1 ≤ t:= (A|>.fits.delayed k).le
    calc
      _ ≤ c*(6*t):=by apply mul_le_mul_of_nonneg_left _ Hc.le; linarith only[hz,ht]
      _ ≤ t^2:=by linarith only [mul_le_mul_of_nonneg_left hh (zero_le_one.trans ht)]
      _ ≤ _:= pow_le_pow_right₀ ht (by norm_num)
end horizon
end YM.Trace.Terrace.Glade
