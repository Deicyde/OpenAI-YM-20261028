import YM.MultipleContact.Bunch.Arrangement
import YM.MultipleContact.Bunch.Arco
import YM.MultipleContact.Matching.Mutate
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Bunching
open YM.MergeProof YM.MergeProof.Ribbons YM.MergeProof.BatchRibbon
open Matching
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
open Relay Exponential Extraction Bid
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}(C:Family G) (N m p d:ℕ){W:Bid.Worth}{u ψ φ δ: ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}
    {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> C.path
local notation "P'"=> C.path.levels.budget
local notation "R"=> C.path.rep N p
local notation "Q'"=> C.path.levels.budget (m+1)
local notation "T'"=> (Labels.frames G).level d
local notation "U"=> Next.Foundations.localSection G d
variable (J k:ℕ){σ χ:ℕ→ℝ}{μ j:ℕ}{η A x e:ℝ}
    (lamp:Side)(b w : ℝ) (a:slot→ℝ) (o:slot→Site (C.side j p)) (hf:J≤k) (hk:k ≤ m) (hN:j < N) (hm:m+1 < j)
local notation "v"=> Site (C.side J p)
local notation "Q"=> hands C p J
local notation "ξ"=> Mix.camp C p J
local notation "y"=> marks C J j p o
local notation "T"=> center C.S p (le_trans hf (le_trans hk (le_trans (m.le_succ) (le_trans hm.le hN.le)))) 0
local notation "Wt"=> march (fun _:Site (C.side J p)=> b) φ k m
private def fpeepers (A:Levels G)(t:Side) (i:ℕ):=(2*(extra A t i)+1)^4
def basket {G:Gauge} (A:Levels G) (lamp:Side)(j i:ℕ) (δ φ:ℕ→ℝ)(η:ℝ)(a:slot→ℝ) := ∏ s:slot, Matching.wicket A lamp j i δ φ η (fun _=>a s) false
def expense {G:Gauge} (A:Levels G)(r:ℕ→ℕ)(χ:ℕ→ℝ)(η:ℝ)(i:ℕ):=let B:=A.budget i; BatchRibbons.Salt.scent (slot:=slot) B.B (r i) (B.supportExponent+1/2) 1 η 1 (χ i)
variable (t:slot→ℕ) (s: (i:slot)→ C.label (t i)) (h:C.Makes)(hh:Scrim C W u ψ φ δ ζ r D)(ht':μ ≤ m)(hR:Created C)
local notation "t!"=> (lamp*C.S.block m)
local notation "l"=> fpeepers C.path.levels t! (m+1)
local notation "W'"=> (fuga C.path.levels (m+1))
local notation "k₀"=> expense (slot:=slot) C.path.levels r χ η (m+1)
local notation "h!"=> lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm.le hN.le)
local notation "A!"=> basket C.path.levels t! j (m+1) δ φ η a
local notation "B!"=> ((Q').B^2+1+2*Matching.patch C.path.levels t! (m+1))
-- consumer at arbitrary two compatible placements. financial later
include h hh ht' hR
lemma mutationWide (L:Stock.Tabs C.path.levels) (hx: Stock.Tabs.opens C.path.levels 1 J k)(hK:C.ref d ≤ k)(ht:∀ i,C.ref (t i) ≤ j) (hM:∀ i,a i*Spindle.paid C (t i) j N p (s i) ≤ ζ (t i) j)(hw:∀ i,0<a i)(htq:GridApprox.room C.path.levels J m (lensScope C d))
   (hΩ: B! ≤ (C.S.toDepth (le_trans hf (le_trans hk (m.le_succ))) p).count.val)(ho:o default=0)(hg:∀b c,b≠c →W'/16 ≤ ‖C.S.place (o b - o c)‖)(hy:∀b,‖C.S.place (o b)‖ ≤4*topZone C.path.levels t! (m+1)) (f:slot→ Config G (C.side N p)→ℂ) (hF:∀ i, f i = MergeProof.item C (t i) N p (s i) (fun j=> y j (0,i)) (1,false))(hi:∀ i,Continuous (f i))(ha:∀ i, Interior ((T).chamber 0) (f i)) (hc₀:∀ z:C.label d,Interior ((T).chamber 0) (C.O N p z 0)) (hr:BatchRibbons.Thor (slot:=slot) C.path δ r D σ χ μ) (hη:0<η)(hq:η≤1)(hD:Throws C.path N p m (D N p m h!) (Next.Foundations.hol G) U x)(hx':1≤x)(hc:χ j≤1)(hY:∀ i:ℕ,m+1 ≤ i→∀ hi:i<j, MergeProof.Float.Runs (D N p i (hi.trans hN)) (C.path.levels.clock.op i p) (6*((C.S.block i).val:ℝ)))
   (hFq:(((Q').B + (Q').B+1 :ℕ):ℝ)^4*k₀ ≤ 1/2)(hΔ:Real.exp k₀-1≤1) (hb: 0 < b)
   (hL:march (fun _:Unit=>b) φ k m () ≤ δ m * (A!/(16*x)))
   (hV:0< A!)(hA:4*(1+(C.path.levels.params m).columns)*(2*(C.S.a (m+1)^d*(x*(4*(1/A!)))))≤ e)
   (hp:32*(1+(C.path.levels.params m).columns)*b * ‖alto C.path k d‖*(e/gainChart C.path m k) ≤ ζ d k/2)
   : ∃ z:C.label d,Next.UVStress.quota C d m N p z ≤ 2*e∧ (T).rootTest (C.beta N p) ((∏ s,f s) - C.O N p z 0) ≤ 2*(stakes C J k / b):=by
   let hm':= hf.trans hk; let hJN:= hm'.trans (show m<N from by omega).le; let h'J:= hm'.trans m.le_succ; have he:=hm.trans hN
   let F:BatchRibbon.Name v slot → Config G (C.side N p) → ℂ := fun x=> capped C J p N hJN (fun _=>f x.2) (x.1,true); let P:=fun i:v=> Equiv.swap 0 i
   have hξ:=wide_gap C j p (m+1) o hm.le hg; have hz(b:slot):=loops_upper C j p (m+1) t! (o b) hm.le  (hy b); have hv:Brine C.path k δ φ:=⟨fun i _=> hh.costs.stay.water _ (Nat.zero_le i),fun i _=> hh.costs.stay.mint _ (Nat.zero_le i),fun i _=> hh.costs.stay.split _ (Nat.zero_le i),fun i _=> hh.costs.stay.support _ (Nat.zero_le i)⟩
   have hS:= Bunching.spaced C J j p (m+1) o (show Brine C.path (m+1) δ φ from ⟨fun i h=>hv.water i (by omega),fun i h=>hv.mint i (by omega),fun i h=>hv.split i (by omega),fun i h=>hv.support i (by omega)⟩) h'J hξ hz hΩ
   have hU:Integrable (birth (BatchRibbon.Aged v slot) (R N) F) (prior G _):= (hatCont C N p F (fun i=>cappedC C J p N hJN (fun _=>f i.2) (i.1,true) (hi _)) (show Continuous (R N|>.eval) by rw [(h.wilson.starts ..).2]; exact bare_cont _) _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   have hX(i : ℕ)(he:J ≤ i):Occupancy (ξ i) (r m):= fun a=> (Occupancy.of_injective (show Injective (ξ i) by rw [show ξ i=(C.S.toDepth he p).embed from funext fun j=> elev C J p i he j]; exact (C.S.toDepth he p).embed_injective) a).trans (hh.back _)
   have hVq (i:v)(s:slot): F (i,s)=stepUp (Q i) (ξ N i) (F (0,s)):= by dsimp [F]; rw [cappid]; exact canned ..
   let p':= C.S.a (m+1)^d*(x*(4*(1/A!)))
   let s':= (∏ s,f s); let q i c:= ∏ s:slot,F (i,s) c; let Y:=gust C.path N p N (birth (Ribbon.Bud v) (R N) q) m (h!).le
   have ht'(i:v): Wt i=march (fun _:Unit=>b) φ k m ():=by
      suffices h:∀ j:ℕ,march (fun _:Site (C.side J p)=>b) φ k j i=march (fun _:Unit=>b) φ k j () by exact h m
      intro j; induction j with
      | zero=>rfl
      | succ j ih=> by_cases hv:k ≤ j <;> simp [march,hv,ih]
   have hT: ∃ Q₀:Coefficient T' (C.side m p), Q₀.Format 0 (Next.Foundations.hol G) (R m)∧Q₀.remBound 0 (R m) (kappa H m) p'∧ (T').coeffSize Q₀.x≤p'∧Served (R m) (fun i=> radiant (alto H m d) (Q i) (ξ m i) (Q₀.exponentialEntry 0 U (R m))) (fun i=> sunny (R m) Q₀.forced (Q i) (ξ m i) (alto H m d)) Y (ξ m) Wt (P' m).supportExponent 1:=
      BatchRibbons.sail C N m p d ξ y Q 0 P Wt t s (fun _=>(1,false)) a F hN hm h hh.costs hr ‹μ≤ m› (hK.trans (hk.trans m.le_succ)) ht hM hw (uphill C J m p N hm') (P_on C J p) (zeroMama C J p m hm') (fun i=>marks_center C J j p o (m+1) ho i) (fun i _=>Equiv.swap_apply_left ..) (fun b hb h i he c=> bit C J j p b (o c) (by omega) i true) (ascending C J j p o (by omega) N)
      (fun i _ he=> by rw [show (C.path.levels.clock.op i p).ratio= C.S.toDepth (Nat.le_succ i) p from ratio_same ..]; exact groups C J j p i o (i+1) (by omega) i.le_succ he) (fun i hK' he a=> (Occupancy.of_injective (Edition.injected _ _ (P' i|>.B_pos) (hS i hK' he)) a).trans (hh.back _)) (fun i hK' he=> ⟨fun _ _ a _ b _=> hS i hK' he a b⟩) (fun i _ j=>hVq i j)
      (fun i=>(cappid ..).trans (hF i)) hU hc hY (hX m hm') (hX _ h'J) hη hq (by change ∀ _,_ ≤ fpeepers C.path.levels (lamp*C.S.block m) (m+1); unfold fpeepers; apply cover C J j p _ o h'J; exact fun b=> (hz b).trans (le_of_eq (by unfold Matching.patch; ring))) hFq hΔ (A:= A!) rfl (march_pos C.path k δ φ (fun _:v=>b) (fun _=>hb) hv _ hk) (fun i=> (ht' i).le.trans hL) hD hx'
   obtain ⟨Q₀,hR,hφ,hB,hZ⟩:= hR.bridge C N p d m (Q) (ξ m) Wt Y hT
   have he : q=(fun i=>(T).copy i s'):= funext (fun i=> funext fun c=> by
       unfold q F s' capped Tiling.copy; split <;> simp
   )
   have hu:= lt_of_lt_of_le zero_lt_one hx'; have hw:0 < p':= mul_pos (pow_pos (C.S.a_pos _) _) (mul_pos hu (mul_pos (by norm_num) (by positivity)))
   have hy':(C.labels.level d).coeffSize Q₀.x+p' ≤ 2*p':=by linarith only [hB]
   have hc0: Continuous s':= by
      have h(vs:Finset slot): Continuous (vs.prod f):= by rw [show vs.prod f=(fun x=>∏ j∈vs, f j x) by funext x; exact Finset.prod_apply x vs f]; exact continuous_finsetProd vs (fun i _=>hi i)
      exact h _
   have ha0: Interior ((T).chamber 0) s':= by
       have hu(ms:Finset slot): Interior ((T).chamber 0) (ms.prod f):=by
          induction ms using Finset.induction with
          | empty=> rw [Finset.prod_empty]; exact Interior.constant _ (1:ℂ)
          | insert i ms hx ih=> rw [prod_insert hx]; exact (ha i).times ih
       exact hu _
   refine bequeathed C N m k p d h b hh L J hx s' Q₀ hK (hk:=hk) h! htq hc₀ hc0 ha0 hR hφ hy' (mul_pos zero_lt_two hw) hA hb hp ?_
   unfold Y at hZ; rw [he] at hZ; exact hZ
end
end YM.MultipleContact.Bunching

