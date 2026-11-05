import YM.TraceExtension.Cask.Oversea
import YM.MergeProof.North.Broom
import YM.TraceExtension.Anchor.PriceTest
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function Ribbons Cells
open GridApprox Local Extra.Trajectories Source Extra.Multi Accent Menu Overlay Extraction
open scoped Classical
variable {G:Gauge}{V L A:Type}[DecidableEq V][Fintype V]
section
variable (H:History G) {p N k:ℕ}
lemma forfeit (hm:k ≤ N)(hh:H.Selected)(F:Config G (H.S.side k p)→ℂ) (hp:Envelope F): (∫ U:Config G (H.S.side k p),(↑((H.rep N p k).eval U):ℂ)*F U∂prior G _)= (Wilson.partition G (H.S.side N p) (H.β N p N):ℂ)*moment (H.β N p N) (backTo H N p hm F):=by
   let v(i):=Complex.ofReal ∘ (H.rep N p i).eval; have he:∀ i:ℕ,∀ hi:i ≤ N,v i=pushTo H N p hi (v N):=by
      intro i hi; induction hi using Nat.decreasingInduction with
      | self=>rw [pushTo_self]
      | of_succ i hi IH=>
         rw [Birth.push_first H N p hi, ← IH]; unfold v; rw [(hh.steps N p i hi).1]; exact (MergeProof.Float.flash _ (H.rep N p (i+1)) _).symm
   have hx:= v N; have hw: v N=Complex.ofReal ∘ (bare (H.β N p N)):=by unfold v; rw[(hh.starts N p).2]
   rw [moment_formula (H.β N p N) _ ((backTo_env H N p hm hp).integrableC _),mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (partition_pos _).ne')]
   change (∫ U,v k U*F U∂prior G _)=_
   rw[he k hm, pushTo_dual H N p hm hp (v N) _,hw]; rfl
   rw [hw]; exact (Complex.continuous_ofReal.comp (bare_cont (G:=G) (n:=H.S.side N p) _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end
section
variable (C : Family G) {r:ℕ→ℕ}{δ u:ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable {p N J k m:ℕ}
local notation "K"=>C.path
local notation "n!"=>C.side k p
local notation "R"=> (C.path.rep N p k)
set_option quotPrecheck false
local notation "a"=> (C.path.levels.budget k).supportExponent
local notation "V!"=> Site (C.S.side J p)
variable [Fintype L][Fintype A][DecidableEq L][DecidableEq A]
variable (hw:C.Makes)(hx: Moonlit C.path r δ u D) (Q:TourC (C.path.rep N p k) (Site (C.S.side J p)) L A)
variable {f:Config G (C.side k p)→ℂ}{w:ℕ→ℝ}{o:∀ i:ℕ,Duel (Site (C.S.side J p))→Site (C.side i p)}
set_option quotPrecheck false
local notation "W!"=> (fun i (_ : Duel (Site (C.S.side J p)))=>w i)
include hx hw
-- Users with full Score from morale
set_option maxHeartbeats 600000 in
lemma quaff (hJ:J ≤ m)(hm:m<k)(hk:k ≤ N)(h:AirC Q)(hc: Decked (agency Q) (C.path.rep N p k) (lance Q) (fun _=> w k) ((C.path.levels.budget k).supportExponent-4) 1)
    (H:Matchup K r δ p k m o W! (Twin (Site (C.S.side J p))))(he:o k=focusS (agency Q))
    (ht: ∀ i, plebe (markA Q) (highA Q) i=(tilesAt C.S p (hJ.trans hm.le)).copy i f)(x:ℕ)(hy: Interior (GridApprox.window 0 x) f) (hb:GridApprox.room C.path.levels J k x): (tilesAt C.S p (hJ.trans (hm.le.trans hk))).rootTest (C.beta N p) (backTo C.path N p hk f) ≤ Real.exp ((C.S.a J/C.S.a m)^4 * Vac.treasury C.path.levels m+4)/((w m)^2):=by
   let W:= C.path.rep N p k; let s :=Stock.final (Duel (Site (C.side J p))); let F:= shore (agency Q) W (lyrics (agency Q) (lance Q)); let X:= tilesAt C.S p (hJ.trans hm.le)
   have H₀:=hw.wilson.represents N p k hk; have hX:= hymns W (lance Q) hc (H.pos k hm.le le_rfl)
   have hG: Served W (0) (0) F (o k) (W! k) (a-4) 1:= by rw [he]; exact Cache.presents _ _ hX (H.pos k hm.le le_rfl)
   have hi:Integrable F (prior G _):= ode W (lance Q) hc H₀.good
   have hl:= floor_s hw.wilson hx hm hk H hG hi
   let E:= gust K N p k F m hm.le; have hW:Integrable E (prior G _):=gust_live K N p k F hi hm.le
   have ha : Vault (W! m) (0:Duel (Site (C.side J p))→ Config G (C.side m p)→ℂ) 0 (0:ℝ) (0:ℝ):= ⟨fun i U=>by simp,fun i U=> by simp⟩
   let g:= fun U=> ∏ i:Site (C.side J p),X.copy i f U; let g':=backTo K N p hk g; let t:= (C.beta N p); let q:=moment t g'
   have hf: backTo K N p hk g=fun U=> ∏ i: Site (C.side J p),(tilesAt C.S p (hJ.trans (hm.le.trans hk))).copy i (backTo K N p hk f) U:= backTo_copies C.path N p (hJ.trans hm.le) hk univ f x hy hb
   have ht':(∫ U,(F U).part s∂prior G _) = (Wilson.partition G (C.side N p) t:ℂ)*q:=by
       rw [show (∫ U,(F U).part s∂prior G _) = _ from cove W Q.who (midland Q) (lance Q) hc (ana Q) H₀.good (meadow Q h H₀.good.labels)]
       simp_rw[ht]; exact forfeit K hk hw.wilson g (Joint.incoming_env K p (hJ.trans hm.le) (cylinder_env hy) univ)
   have ht'':(∫ U,(E U).part s∂prior G _)= (Wilson.partition G (C.side N p) t:ℂ)*q:=by
       let f:=fun U=> (F U).part s; have hc:=gust_choose K N p F hi hm.le s; exact ((congr_arg (fun f:Config G (C.side m p)→ℂ=>∫ U,f U∂prior G _) hc).trans ((pushTo_integral _ _ _ hm.le _ (((Poly.get s).restrictScalars ℝ).integrable_comp hi)).trans ht'))
   have hu:0 < w m:=H.pos m le_rfl hm.le (0,true); let v:=Fintype.card (Site (C.side J p)); let b:=(C.S.a J/C.S.a m)^4 * Vac.treasury C.path.levels m+ (4:ℝ); let u:=(w m)^2
   have hy:= spiker C N m p hw s q (hm.le.trans hk) (H.pos _ le_rfl hm.le) hl ha hW ht''
   unfold Tiling.rootTest; have hr:‖q‖^ (v:ℝ)⁻¹ ≤ Real.exp b/u:=by
      refine Stock.spacer ‖q‖ b u v (norm_nonneg _) (pow_pos hu _) Fintype.card_pos ?_
      have he:(Fintype.card (Site (C.side m p)):ℝ)* Vac.treasury C.path.levels m+ Fintype.card (Duel (Site (C.side J p)))*(0+0+(2:ℝ)*1)=v*b:=by rw [Stock.tallies C.S J m p]; unfold Duel; simp only [Fintype.card_prod, Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]; unfold v b; ring
      rw [he,show Poly.toll (W! m) s=u^v from ?_] at hy; exact hy
      simp only [Poly.toll,s,Stock.final,prod_const,Finset.card_univ,Duel,Fintype.card_prod,Fintype.card_bool]; rw [mul_comm, pow_mul]
   convert! hr using 1; unfold q g'; rw [hf]; rfl
end
end YM.Trace.Cask
#print axioms YM.Trace.Cask.quaff
