import YM.OPE.Sweep.Ballet

/-!
# Capture at root parent

A particularly simple choice: place root envelope strictly inside the single step
block of root and interiors. (The propagated family handles interim prices;
we're free to choose all final slots at this same site at m+1.)
Adapted from `Ribbons.mutation` (see that theorem for the B²-radius layout).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
open Relay Exponential Extraction Bid
variable {V I: Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]{G:Gauge}(C:Family G) (N m p d:ℕ){W:Bid.Worth}{u ψ φ δ χ x :ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}
    {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> C.path
local notation "P'"=> C.path.levels.budget
local notation "R"=> C.path.rep N p
local notation "Q'"=> C.path.levels.budget (m+1)
local notation "T'"=> (Labels.frames G).level d
local notation "U"=> Next.Foundations.localSection G d
variable (J k:ℕ){σ :ℕ→ℝ}{j:ℕ}{α A e:ℝ}(i₀:I)
    (b w : ℝ) (a:I→ℝ) (o:I→Site (C.side j p)) (hf:J≤k) (hk:k ≤ m) (hN:j < N) (hm:m+1 ≤ j)
local notation "v"=> Site (C.side J p)
local notation "Q"=> hands C p J
local notation "ξ"=> Mix.camp C p J
local notation "y"=> fun (i:ℕ) (t:v×I)=> bites C J j p (o t.snd) i (t.1,true)
local notation "T"=> center C.S p (le_trans hf (le_trans hk (le_trans (m.le_succ) (le_trans hm hN.le)))) 0
local notation "Wt"=> march (fun _:Site (C.side J p)=> b) φ k m
variable (t:I→ℕ) (s:(i:I)→ C.label (t i))(h:C.Makes)(hh:Scrim C W u ψ φ δ ζ r D)(hR:Created C)
local notation "h!"=> lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm hN.le)
local notation "f'" => C.S.toDepth (le_trans hf (le_trans hk (m.le_succ))) p
variable (hr:SwornClusterCuts C (δ:=δ) (μ:=D) (r:=r) (C.ref d) d χ δ x)
include hf hk
lemma parentY {i i':ℕ}(hi:m+1 ≤ i)(hs:i ≤ i')(hj:i'≤j): (C.S.toDepth hs p).parent ∘ (y) i'=(y) i:=funext fun t=>congr_fun (bitesParent C J j p i (o t.2) (by omega) hs hj) (t.1,true)
lemma rootY (hΩ:∀ i,loops C j p (o i) (m+1)=0) (i:v×I) : (y) (m+1) i=ξ (m+1) i.1:=by dsimp only; rw [bit C J j p (m+1) (o i.snd) (by omega) _,biteT C J j p (m+1) (o i.snd) (by omega),hΩ]; simp [affine]
lemma hatchY (hΩ:∀ i,loops C j p (o i) (m+1)=0) (hg:(P' (m+1)).B^2+1≤(C.S.toDepth (le_trans hf (le_trans hk (m.le_succ))) p).count.val)(ht:Brine C.path (m+1) δ φ)(i:ℕ)(hi:m+1 ≤ i)(hj:i ≤ j) : Cross (P' i).B ((y) i):=by
    intro x z h
    let Z:= C.S.toDepth hi p; let L:=Z.count.val; have he:= parentY C m p J k o hf hk (i':=i) le_rfl hi hj
    have hx j:2*separation ((y) i j) (Z.embed ((y) (m+1) j))< L:=by rw [← congr_fun he j]; exact midway Z (C.S.toDepth_odd hi p) _
    let t:=(P' (m+1)).B; have hh:L*(t^2+1)≤ separation (Z.embed ((y) (m+1) x)) (Z.embed ((y) (m+1) z)):= by
       rw [Station.both,rootY C m p J k o hf hk hΩ x,rootY C m p J k o hf hk hΩ z,elev C J p (m+1) (by omega),elev C J p (m+1) (by omega),Station.both]; exact Nat.mul_le_mul_left _ (hg.trans (Nat.le_mul_of_pos_right _ (separation_pos x.1 z.1 h)))
    have h₁:= separation_triangle (Z.embed ((y) (m+1) x)) ((y) i x) (Z.embed ((y) (m+1) z)); have h₂:=separation_triangle ((y) i x) ((y) i z) (Z.embed ((y) (m+1) z)); rw [separation_comm (Z.embed ((y) (m+1) x)) ((y) i x)] at h₁; have hu:(P' i).B^2 ≤ L*t^2:= gap_comp C p (m+1) i ht hi; rw [mul_add,mul_one] at hh; have h₃:=hx x; have h₄:=hx z; omega

include h hh hR hr hm hN i₀
lemma joins (L:Stock.Tabs C.path.levels)(hx: Stock.Tabs.opens C.path.levels 1 J k) (hK:C.ref d ≤ k)(ht:∀ i,C.ref (t i) ≤ j)(hM:∀ i,a i*Spindle.paid C (t i) j N p (s i) ≤ ζ (t i) j)(hw:∀ i,0<a i)(htq:GridApprox.room C.path.levels J m (lensScope C d))
    (hΩ:∀ i,loops C j p (o i) (m+1)=0)(hg:(P' (m+1)).B^2+1≤(C.S.toDepth (le_trans hf (le_trans hk (m.le_succ))) p).count.val)(hy:Edition.Spaced (P' j).B o)
    (ha:0<α)(hφ:α≤1)(hΨ:∀ k:ℕ,m≤ k→ k<j→ α ≤ license C.path δ (Fintype.card I) (carpet C.path k) (k+1))
    (f:I→ Config G (C.side N p)→ℂ)(hF:∀ i,f i=C.O N p (s i) ((C.S.toDepth hN.le p).embed (o i)))(hi:∀ i,Interior ((T).chamber 0) (f i))(hc₀:∀ z:C.label d, Interior ((T).chamber 0) (C.O N p z 0))
    (hz:0<A)(hY:A≤ initial C.path δ φ m j α (∏ i,a i) (Fintype.card I))
    (hb:0<b)(hL:march (fun _:Unit=>b) φ k m ()≤ δ m * (A/(16*x m)))
    (hA:4*(1+(C.path.levels.params m).columns)*(2*(C.S.a (m+1)^d*(x m*(4*(1/A)))))≤ e)
    (hp:32*(1+(C.path.levels.params m).columns)*b * ‖alto C.path k d‖*(e/gainChart C.path m k) ≤ ζ d k/2)
    : ∃ z:C.label d, let g : Config G (C.side N p)→ℂ := (fun u=>∏ i,f i u); Next.UVStress.quota C d m N p z ≤ 2*e ∧ Interior ((T).chamber 0) (g-C.O N p z 0)∧ (T).rootTest (C.beta N p) (g-C.O N p z 0) ≤ 2*(stakes C J k / b):=by
    let F(x:v×I):=(T).copy x.1 (f x.2); let P:=fun i:v=> Equiv.swap 0 i; let hm':=hf.trans hk; let hJ':=hm'.trans m.le_succ
    have hv:Brine C.path k δ φ:=⟨fun i _=> hh.costs.stay.water _ (Nat.zero_le i),fun i _=> hh.costs.stay.mint _ (Nat.zero_le i),fun i _=> hh.costs.stay.split _ (Nat.zero_le i),fun i _=> hh.costs.stay.support _ (Nat.zero_le i)⟩
    have hZ:∀ i≥m+1, Collar ((y) i) 0 (ξ i) Q:= fun i hi s _ t=> bit C J j p i (o t) (by omega) s true
    have he':Brine C.path (m+1) δ φ:=⟨fun i h=> hv.water i (by omega),fun i h=> hv.mint i (by omega),fun i h=>hv.split i (by omega),fun i h=> hv.support i (by omega)⟩
    have hX:=fun i (he:m+1 ≤ i) hj=> hatchY C m p J k o hf hk hΩ hg he' i he hj
    have hδ j:Continuous (f j):=by rw [hF]; exact C.continuousO ..
    have hδ'(j:v×I):Continuous (F j):= cappedC C J p N (by omega) (fun _=> f j.snd) (j.1,true) (hδ _)
    have hU:Integrable (birth (Names v I) (R N) F) (prior G _):= (hatCont C N p F hδ' (show Continuous (R N|>.eval) by rw [(h.wilson.starts ..).2]; exact bare_cont _) _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hSp:Edition.Spaced (P' j).B ((y) j):= (hX j hm le_rfl).together (hZ j hm) (show Edition.Spaced (P' j).B (fun i=> bites C J j p (o i) j (0,true)) from (by rw [show (fun i=> bites C J j p (o i) j (0,true))= o from funext fun i=>(biteT C J j p j (o i) (by omega)).trans (Ribbons.same C j p (o i))];exact hy))
    have hF0(i): F (0,i)=f i:= cappid C J p N (by omega) (fun _=> f i) true
    have hu(i:v)(b'): F (i,b')=stepUp (Q i) (ξ N i) (F (0,b')):= by rw [hF0 b']; exact canned C J p N (by omega) (fun _=> f b') i true
    have hY(i):F (0,i)=MergeProof.item C (t i) N p (s i) (fun k=> (y) k (0,i)) (1,false):= by rw [hF0,hF i]; unfold MergeProof.item; rw [itemT C N p _ h (s i)  _]; dsimp only; rw [(show bites C J j p (o i) N (0,true)= _ from (biteT C J j p N (o i) (by omega)).trans (vect C j p N (o i) hN.le))]
    let p':= C.S.a (m+1)^d*(x m*(4*(1/A))); let g u:=∏ i,f i u; let q (i:v) u:=∏ a',F (i,a') u; let Y:=gust C.path N p N (birth (Bud v) (R N) q) m (h!).le
    have ht'(i:v): Wt i=march (fun _:Unit=>b) φ k m ():=by
       suffices h:∀ j:ℕ,march (fun _:Site (C.side J p)=>b) φ k j i=march (fun _:Unit=>b) φ k j () by exact h m
       intro j; induction j with
       | zero=>rfl
       | succ j ih=> by_cases hv:k  ≤  j <;> simp [march,hv,ih]
    have hξ(i : ℕ)(he:J  ≤  i):Occupancy (ξ i) (r m):= fun a=> (Occupancy.of_injective (show Injective (ξ i) by rw [show ξ i=(C.S.toDepth he p).embed from funext fun j=> elev C J p i he j]; exact (C.S.toDepth he p).embed_injective) a).trans (hh.back _)
    have hE (i:v×I): coverNumber (P' (m+1)).B ({(y) (m+1) (i.1,i₀),(y) (m+1) i}:Support _)  ≤  carpet H m:=by
       rw [rootY C m p J k o hf hk hΩ,rootY C m p J k o hf hk hΩ]; refine (pairCover (P' (m+1)).B_pos (ξ _ i.1) (ξ _ i.1) 0 (by simp only [separation_self,zero_mul,le_refl])).trans ?_
       simp only [two_mul,add_zero, zero_add,one_pow]; unfold carpet OPE.haloUnits; exact Nat.succ_le_of_lt (by positivity) -- arg position
    have hT: ∃ Q₀:Coefficient T' (C.side m p), Q₀.Format 0 (Next.Foundations.hol G) (R m)∧Q₀.remBound 0 (R m) (kappa H m) p'∧ (T').coeffSize Q₀.x ≤ p'∧Served (R m) (fun i=> radiant (alto H m d) (Q i) (ξ m i) (Q₀.exponentialEntry 0 U (R m))) (fun i=> sunny (R m) Q₀.forced (Q i) (ξ m i) (alto H m d)) Y (ξ m) Wt (P' m).supportExponent 1:=
      Ballet C N p m j d ξ (y) Q 0 P i₀ Wt t s (fun _=>(1,false)) a F hm hN h hh (hK.trans hk) hr ht hM hw (uphill C J m p N hm') (P_on C J p) (zeroMama C J p m hm') (fun i=>rootY C m p J k o hf hk hΩ (i,i₀)) (fun i _=> Equiv.swap_apply_left ..) (fun i hi _=> hZ i hi) ⟨fun i he hp=> funext fun j'=> congr_fun ((retina C J j p N (o j'.2) (by omega)).mare i he hp) (j'.fst,true)⟩ (fun i hi hx=>by rw [show (C.path.levels.clock.op i p).ratio=C.S.toDepth (Nat.le_succ i) p from ratio_same ..]; exact parentY C m p J k o hf hk hi i.le_succ hx)
        hX hSp (fun i _ j=>hu i j) hY hU (hξ _ hm') (hξ _ hJ') ha hφ (fun i h=> hΨ i (by omega)) (hΨ m le_rfl hm) hE hz ‹A  ≤  initial ..› (march_pos C.path k δ φ (fun _:v=>b) (fun _=> hb) hv _ hk) (fun i=> (ht' i).le.trans hL)
    obtain ⟨Q₀,hR,hφ,hB,hT⟩:= hR.bridge C N p d m (Q) (ξ m) Wt Y hT
    have hV: q=(fun i=>(T).copy i g):=by funext i u; change ∏ j,F (i,j) u=_; unfold F g Tiling.copy; split_ifs <;> simp only [star_prod]
    have hu':= zero_lt_one.trans_le (hr.dollars m (hK.trans hk)); have hw:0 < p':= mul_pos (pow_pos (C.S.a_pos _) _) (mul_pos hu' (mul_pos (by norm_num) (by positivity)))
    have hy':(C.labels.level d).coeffSize Q₀.x+p'  ≤  2*p':=by linarith only [hB];
    have hi':Interior ((T).chamber 0) g:= Interior.combines f _ (fun i _=> hi i)
    unfold Y at hT; rw [hV] at hT; obtain ⟨z,hU,hG⟩:= bequeathed C N m k p d h b hh L J hx g Q₀ hK (hk:=hk) h! htq hc₀ (continuous_finsetProd _ (fun i _=> hδ i)) hi' hR hφ hy' (mul_pos zero_lt_two hw) hA hb hp hT
    refine ⟨z,hU, Next.UVStress.minus hi' (hc₀ _),hG⟩
end
end YM.MergeProof.Ribbons.ManyCopies
