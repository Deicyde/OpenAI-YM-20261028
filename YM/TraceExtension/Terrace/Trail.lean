import YM.TraceExtension.Terrace.Turf
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace.Glade
open Function Filter Finset Lattice RG Wilson Labels Source Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price MergeProof.East Further.CorrectedLift Ward Climb Analysis Work Weir StressFlux
open Further.PhysicalPeriodLimitF933 Shunt PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells Pressure
open Motion MergeProof ProofPorts.GridRealModelsEstimates20261012
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}
section motion
variable {i k j m N p l d:ℕ}
def present (n:Side)(s:Motion): Module.End ℝ (Film G n) where
    toFun := dance s
    map_add' a b:= funext fun U=> scalar_add s _ _
    map_smul' a b:=by funext U; change scalar s (a • (_:ℂ))= a • _; simp [dance,scalar,Complex.real_smul]
@[simp] lemma mirrorP {n:Side}(s:Motion) (u:Film G n)(U:Config G n): ‖present n s u U‖= ‖u (pull s.1 0 U)‖:= norm_scalar s _
lemma preset {C:Family G} (N p k i:ℕ)(hk:k ≤ N)(hj:i ≤ k)(s:Motion) (u:Film G (C.side k p))(h:Envelope u) : backTo C.path N p hk (present _ s u)=present _ s (backTo C.path N p hk u):=by
   rcases s with ⟨s,b⟩
   let Q:= (0:Site (C.side i p)); have he:= backTo_orient C.path N p hj hk Q s h
   rw[show anchor C.path.S p hj Q=0 from (C.S.toDepth _ _).root.map_zero, show anchor _ p (hj.trans hk) Q=0 from (C.S.toDepth _ _).root.map_zero] at he
   cases b; exact he
   change backTo C.path N p hk (fun x=>star ((u ∘ pull s 0) x))=present _ (s,true) (backTo C.path N p hk u)
   rw [backTo_star (F:=u∘pull s 0) C.path N p hk (h.comp_env (continuous_pull ..).measurable), he]; rfl
lemma TrailX {n:Side}(s:Motion)(u:Film G n)(hx:Interior (Push.GridApprox.window 0 l) u) : Interior (Push.GridApprox.window 0 l) (present n s u):=by
   rcases s with ⟨s,i⟩; have ht:= hx.unchanged s 0 (by simpa [affine] using! window_affine (n:=n) (r:=l) 0 0 s); cases i; exact ht; exact ht.real
lemma trailRoot (S:Schedule)(hk:i≤k)(s:Motion)(u:Film G (S.side k p))(β:ℝ)(hx: Interior ((tilesAt S p hk).chamber 0) u) : Interior ((tilesAt S p hk).chamber 0) (present _ s u) ∧ (tilesAt S p hk).rootTest β (present _ s u)=(tilesAt S p hk).rootTest β u:=by
   constructor
   · have he : (tilesAt S p hk).chamber 0=Push.GridApprox.window 0 ((S.toDepth hk p).count.val/2):=(tiling_window S p hk (0:Site (S.side i p))).trans (by rw [show anchor S p hk 0=0 from (S.toDepth hk p).root.map_zero]); rw[he] at hx ⊢; exact TrailX s u hx
   obtain ⟨s,b⟩:=s; have h:=root_oriented S hk β s u hx; cases b; exact h; exact (Work.B15.rootTest_star _ β _).trans h
lemma formed {C:Family G}(N p:ℕ)(H:C.Makes)(s:Motion)(d:ℕ)(hi:C.ref d ≤ N)(v:C.label d): C.O N p (Prism _ s v) 0= present _ s (C.O N p v 0):=by
    obtain ⟨s,b⟩:= s; funext U; cases b
    · have hp:= C.rotated H hi v s 0 0 U; rw [show affine (R:=Per (C.side N p)) s 0 0=0 from by simp[affine]] at hp; exact hp
    change C.O N p (star _) 0 U=_; rw[C.reality H hi]; apply congr_arg star; have ht:= C.rotated H hi v s 0 0 U; rw [show affine (R:=Per (C.side N p)) s 0 0=0 from by simp[affine]] at ht; exact ht
-- Root Price rotation coin.
set_option maxRecDepth 4096
abbrev muC (i:Axis)(s:Motion):ℝ:= rent*hued s i
lemma mu_norm (s:Motion)(i) : ‖muC i s‖=rent:=by rw[Real.norm_eq_abs]; unfold muC; rw [abs_mul,stamp s i i,abs_of_pos rent_pos,mul_one]
lemma reedRoad(n:Side)(v:Axis→Film G n)(i:Axis)(l:ℕ)(hp:∀ i,Interior (Push.GridApprox.window 0 l) (v i)):
   Interior (Push.GridApprox.window 0 l) (Reed (present n) v i):=by rw[reedEq]; exact interior_sum _ _ (fun s _=>by rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)];exact (TrailX s _ (hp _)).scale _)
lemma teamW (S:Schedule){u:Axis → Film G (S.side k p)}(β:ℝ)(hk:i≤ k)(l:Axis)(H:Seam G (S.side k p) β)
    (hx:∀ a, Interior ((tilesAt S p hk).chamber 0) (u a)) (t:ℝ)(h:∀ a,(tilesAt S p hk).rootTest β (u a) ≤ t) : Interior ((tilesAt S p hk).chamber 0) (Reed (present _) u l) ∧ (tilesAt S p hk).rootTest β (Reed (present _) u l) ≤ t:=by
    let Q(m:Motion):=present _ m (u (prev m l)); let X:=tilesAt S p hk
    rw [show Reed (present _) u l= ∑ m:Motion, (↑(muC l m):ℂ) • Q m from (reedEq ..).trans (sum_congr rfl fun m _=> RCLike.real_smul_eq_coe_smul (K:=ℂ) _ _)]
    obtain ⟨hz,hK⟩:= root_sum X β Finset.univ Q (fun m=>(muC l m:ℂ)) (fun m _=> (trailRoot S hk m _ β (hx (prev m l))).1) H
    refine ⟨hz,hK.trans ((sum_le_sum (fun m _=>?_)).trans_eq (rent_collect t))⟩; rw [Complex.norm_real,mu_norm]; exact mul_le_mul_of_nonneg_left ((trailRoot S hk m _ β (hx (prev m l))).2.le.trans (h _)) rent_pos.le
lemma readUp {C:Family G}(i k N p:ℕ)(hk:i ≤ k)(hn:k ≤ N) (f:Axis→ Film G (C.side k p))(a:Axis)(l:ℕ)(hf:∀ x,Interior (Push.GridApprox.window 0 l) (f x)) : backTo C.path N p hn (Reed (present _) f a)= Reed (present _) (fun i=>backTo C.path N p hn (f i)) a:=by
   simp_rw[reedEq,RCLike.real_smul_eq_coe_smul (K:=ℂ)];
   change backTo C.path N p hn (∑ j:Motion, (↑(muC a j):ℂ) • (present (C.side k p) j (f (prev j a)))) = _; rw [show backTo C.path N p hn (∑ j, _) = _ from backTo_linSum (C:=C) N p hn (fun m=>present (C.side k p) m (f (prev m a))) (fun m=> ↑(muC a m)) (fun m=> cylinder_env (TrailX m _ (hf _)))];
   exact sum_congr rfl (fun j _=>by rw[preset (C:=C) N p k i hn hk j _ (cylinder_env (hf _))];rfl)
lemma readY {C:Family G}(N p:ℕ)(H:C.Makes)(d:ℕ)(hi:C.ref d ≤ N)(v:Axis→ C.label d)(x:Axis): C.O N p (Reed (Prism (C.labels.level d)) v x) 0= Reed (present _) (fun i=> C.O N p (v i) 0) x:=by
   let f := ((C.linearO N p d 0).mk' _).restrictScalars ℝ; change f _=_; rw[reedEq,reedEq,map_sum]; simp_rw[map_smul]; exact sum_congr rfl (fun j _=>by
       change _ • C.O N p (Prism _ j _) 0= _; rw [formed N p H j d hi])
lemma const_zero {n:Side}(v:Axis→ℂ): Reed (present (G:=G) n) (fun i _=> v i)=0:=by
   funext a U; let x(s:Motion):= (rent*hued s a) • present (G:=G) n s (fun _=>v (prev s a));
   have hp(s): (x (splitP archV s)) U= -(x s U):=by
       have he : hued (splitP archV s) a= -(hued s a):=by
          have hv:= hue_step s archV a; simpa [archV,sign] using! hv
       have hx:prev (splitP archV s) a=prev s a:= prev_step s archV a
       unfold x; rw [he,hx,mul_neg,neg_smul];rfl
   have he:= Equiv.sum_comp (splitP archV) (fun s=> x s U); simp only [hp,sum_neg_distrib] at he; rw [reedEq,Finset.sum_apply]; change _= (0:ℂ); change ∑ j, x j U= (0:ℂ);linear_combination -(1/2)*he
end motion
end YM.Trace.Terrace.Glade
