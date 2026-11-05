import YM.TraceExtension.Shepherd.Lake
import YM.TraceExtension.Cask.Votive
import YM.MergeProof.South.Window
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi StressFlux MeasureTheory Cells Accent Menu
open Push.GridApprox
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{C:Family G}{r:ℕ→ℕ}{δ u:ℕ→ℝ}{W:∀ N p k:ℕ,k<N→GaugeDoor (C.path.rep N p (k+1)) (C.path.rep N p k)}
set_option quotPrecheck false
variable (h:C.Makes) (hp:Moonlit C.path r δ u W){m l k p N J:ℕ}
local notation "R"=> (C.path.rep N p k)
local notation "S"=> C.S
local notation "M"=> (C.path.levels)
local notation "I!"=> Site (C.S.side J p)
local notation "T"=> Mix.camp C p J
lemma camb (hi:J ≤ k) (j:I!) : Mix.camp C p J k j=anchor S p hi j:=by unfold Mix.camp; rw[dif_pos hi]
lemma ranchK (hJ:J ≤ m)(w:ℕ→ℝ)(hR: ∀ i,m ≤ i→ i ≤ k→2 ≤ r i)(hw:∀ i,m ≤ i→i ≤ k→0<w i)(hh:∀ i,m ≤ i→i<k→w i≤δ i*w (i+1)) : Matchup (C.path) r δ p k m (fun j=> T j ∘ Prod.fst) (fun i _=>w i) (Twin (Site (C.S.side J p))):=by
   let v:=Site (C.S.side J p); let Z :=Twin v; let o(i): Duel v → Site (C.side i p):=T i ∘ Prod.fst
   have hz(i)(hi:m ≤ i)(t':ℕ)(hp:2 ≤ t'):Occupancy (o i) t':=by
      intro x; unfold o; apply le_trans _ hp; let t:= univ.filter (fun q:Duel v=> T i q.1=x)
      change t.card ≤ 2; have hw:t.card≤(univ:Finset Bool).card:=by
         apply card_le_card_of_injOn Prod.snd (by intro p hp; exact mem_univ _) ; intro a ha b hb he; apply Prod.ext ?_ he
         have hx : T i a.1=T i b.1:= ((mem_filter.mp ha).2).trans ((mem_filter.mp hb).2).symm; rw [camb (hJ.trans hi),camb (hJ.trans hi)] at hx
         let f:=C.S.toDepth (hJ.trans hi) p; exact (by have ht:= congr_arg f.parent hx; change f.parent (f.embed _)=f.parent (f.embed _) at ht; rwa[Ratio.embed_parent,Ratio.embed_parent] at ht)
      simpa using hw
   refine ⟨fun i hi hk _=>hw _ hi hk,fun i hi hk=>hz i hi (r i) (hR i hi hk),fun i hi hk=>hz (i+1) (hi.trans i.le_succ) (r i) (hR i hi hk.le),fun i hi hk=>?_,fun i hi hk=>?_⟩
   · funext q; simp only[Function.comp_apply,← Work.I03.camp_step C p (hJ.trans hi),Ratio.embed_parent]
   intro s ht x hX
   have hF:= hw i hi hk.le
   rw [one_mul]; unfold Marker.Poly.toll; simp only[prod_const]
   apply le_trans (pow_le_pow_left₀ hF.le (hh i hi hk) _); have hy:=hF.trans_le (hh i hi hk); exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
include h hp
variable (x: Site (C.side k p))(d:Axis)(ν:G.El→ G.El)(f:Config G (C.side k p)→ G.El →ℂ){P:Support (C.side k p)}{D:ℝ} (hD:ProofC (C.path.rep N p k) x f ν P D)
include hD
set_option maxHeartbeats 400000 in
lemma garnet (hK:k ≤ N) (hm:m<k)(hJ:J ≤ m) (hS: Geo.Width (C.path.rep N p k).p (C.path.rep N p k|>.clip) (M|>.params k|>.width)) (hv:WilsonStartup.Decent (C.path.rep N p k|>.clip) (C.path.rep N p k).p)(he:4 ≤ (C.path.rep N p k).p.supportExponent)(hR:∀ i,m ≤ i→i ≤ k→2 ≤ r i)
    (l n b:ℕ)(hB:1 ≤ b)(hk: coverNumber (C.path.rep N p k).p.B P ≤ l)(ho:x∈P)(hz:0∈P)
    (hw: ∀ hj:J ≤ k, let t:= 2*(separation 0 x); let V:=(C.S.toDepth hj p).count.val; 2*pierSize (C.path.rep N p k).p n l+2+t < V ∧ 64*(C.path.rep N p k).p.B*b+2*(C.path.rep N p k).p.B+t≤ V) (hs:Push.GridApprox.room C.path.levels J k (2*pierSize (C.path.rep N p k).p n l)) (F:ℝ) (hF:0≤ F)(hU:∀ U v, ‖f U v‖ ≤ F)
    (w:ℕ→ℝ)(hw':∀ i,m ≤ i→i ≤ k→0<w i)(h':∀ i,m ≤ i→i<k→w i ≤ δ i*w (i+1))(hL: ExpenseH (C.path.levels.params k).paths (C.path.levels.clock.loopCap k) (C.path.levels.clock.forcedAllowance k) (C.path.levels.clock.allowance k) 1 (C.path.levels.params k).width F D (w k) R l n b):
    (tilesAt C.S p (hJ.trans (hm.le.trans hK))).rootTest (C.beta N p) (backTo C.path N p hK (lensF R x d ν f n)) ≤ Real.exp ((C.S.a J/C.S.a m)^4 * Vac.treasury C.path.levels m+4)/(w m)^2 :=by
    let t:=hJ.trans hm.le; let X:=tilesAt C.S p t; let s (i:I!):Seat (C.side k p):= (X.omega i,X.translateBy i); let B(i:I!):= X.hand i
    let z:=joinD x ∘ s; let P':= fun i=>Seat.spread (s i) P; let f':=fun i=> Ink f (s i) (B i)
    let p':=(C.S.toDepth t p).count.val; have ht(i:I!): Mix.camp C p J k i=(s i).2:=by rw[camb t]; exact (tile_translate ..).symm
    let H: I! ↪ Site (C.side k p):={ toFun:= T k, inj':=fun i j he=> by rw[camb t,camb t] at he; let F:= C.S.toDepth t p; exact (F.embed_parent i|>.symm.trans ((congr_arg F.parent he).trans (F.embed_parent j))) }
    have hu (i:I!): separation (T k i) (z i)=separation 0 x:=by
       have hn:= Push.Local.turn_sep (s i).1 (s i).2 0 x; change separation (affine _ _ 0) _ = _ at hn; simp only[affine,Signed.act_zero,zero_add] at hn; rw[ht]; exact hn
    obtain ⟨ht',hf⟩:= hw t
    have hQ (i j:I!) (he:i≠j): 2*pierSize (C.path.rep N p k).p n l+2 < separation (z i) (z j) ∧ 64*(C.path.rep N p k).p.B*b+2*(C.path.rep N p k).p.B ≤ separation (z i) (z j):=by
       have hv:=Corona.below (C.S.toDepth t p) i j; have hp:1≤ separation i j:= Nat.pos_of_ne_zero fun hh=> he (by exact (Corona.line_home i j).symm.trans (Corona.line_end i j hh.le)); have hA : p' ≤ separation (T k i) (T k j):=by rw [camb t,camb t];exact (le_mul_of_one_le_right (Nat.zero_le _) hp).trans hv
       have hB:= separation_triangle (T k i) (z i) (T k j); have h':=separation_triangle (z i) (z j) (T k j); rw [hu] at hB; rw [separation_comm (z j) _,hu] at h'; omega
    have H' := passport R x d ν f (h.wilson.represents N p k hK|>.good) hS hv he n hD s B H ht ho hz l hk (fun i j hh=>(hQ i j hh).1)
    let Y:= hull R n H'.terse H'.seats (d:=rose d ∘ s) (ν:=ν) (J:=fun i=> Ink f (s i) (B i))
    have hp:= h.wilson.represents N p k hK|>.good
    have hZ : Decked (agency Y) R (lance Y) (fun _=>w k) ((C.path.rep N p k).p.supportExponent-4) 1:=welfare hp hS hv he n H' (w k) F hF l b hB (fun i=>(Seat.visit_count ..).trans_le hk) (fun i j hh=>(hQ i j hh).2) (fun i U k=>(pecked ..).le.trans (hU _ _)) hL
    have hhK:(R|>.p).supportExponent=(C.path.levels.budget k).supportExponent:= congr_arg _ (h.wilson.represents _ _ _ hK).vac
    rw [hhK] at hZ
    refine quaff C h ‹_› Y hJ hm hK (polo R hp hS hv he n H') hZ (ranchK hJ w hR hw' h') rfl ?_ _ (panel R x d ν f hp hS hv he n hD ho l hk hz) hs
    intro i; have ht:= copyP R x d ν f hp hS hv he n hD s B H H' i; refine ht.trans ?_; funext U; change peck (decide (X.hand i)) _ = X.copy i _ U; unfold peck Tiling.copy; by_cases hx:X.hand i<;> simp only[hx, decide_true,decide_false,↓reduceIte]<;> first| rfl | simp [s]
end YM.Trace.Shepherd
#print axioms YM.Trace.Shepherd.garnet
