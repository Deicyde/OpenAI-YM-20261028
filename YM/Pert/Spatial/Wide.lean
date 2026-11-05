import YM.Pert.Spatial.Prices

/-!
Layout adjustment of the two-inner-slot actual bound. A tile may have its inner
separation enlarged by at most the intervening calendar's block ratio, itself
between the same two levels. Only the preimage spacing and fine packing count
use this enlargement. In particular we pay `Salt.tow` with this wider integer
budget before applying `sail`; merely exporting `bricks` with a larger interval
would not justify that bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories  Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge} {n:Side} (C:Family G) (J j m p k N d:ℕ)
set_option quotPrecheck false
local notation "H"=> C.path
local notation "Rb"=> C.path.levels.budget
local notation "P"=> hands C p J
local notation "V'"=> Site (C.side J p)
local notation "E"=> Mix.camp C p J
local notation "S"=> C.S
variable (a:Site (C.side j p))
local notation "o"=> bites C J j p a
local notation "v"=> loops C j p a
local notation "t"=> (Rb k).B
local notation "y"=> (C.S.place a)
def spacingFactor (A : Levels G) (k : ℕ) : ℕ := (A.S.block (k-1)).val
def pollsW (A:Levels G)(k:ℕ): ℕ := (spacingFactor A k)*polls A k
private lemma factor_pos (k : ℕ) : 0 < spacingFactor C.path.levels k := (C.S.block _).pos
local notation "X"=> pollsW C.path.levels k
local notation "W"=> fuga C.path.levels k
variable (hk:k≤j)
include hk
lemma maximizingWide (hp:W/16≤ ‖C.S.place a‖)(hh:‖C.S.place a‖ ≤(spacingFactor C.path.levels k : ℝ)*(4*W)) :
    t^2+1 ≤ separation (v k) 0 ∧ separation (v k) 0 ≤ X:=by
    obtain ⟨h₁,h₂⟩:= normC C j p a
    let Z:= C.S.toDepth hk p; let B:= separation (v k) 0; let c:= Z.count.val
    have hV: 2*separation a (Z.embed (v k))< c:= (by rw [vote C _ _ _ _ hk]; exact midway _ (C.S.toDepth_odd hk p) _)
    have hz : separation (Z.embed (v k)) 0 = c*B:=by nth_rw 1 [show _= v k from rfl]; nth_rw 1 [show (0:Site (C.side j p))=Z.embed 0 from Z.root.map_zero.symm]; exact Station.both ..
    have hL:= separation_triangle a (Z.embed (v k)) 0; have hq:= separation_triangle (Z.embed (v k)) a 0; rw [separation_comm (Z.embed (v k)) a,hz] at hq; rw [hz] at hL
    have hy : C.S.a j*c=C.S.a k:= C.S.embeds_scale Z; have ha:= C.S.a_pos j; have hp':= C.S.a_pos k; have hb:1 ≤ ((t:ℕ):ℝ):=by exact_mod_cast (Rb k).B_pos
    constructor
    · have hs: C.S.a j*(separation a 0:ℝ) ≤ C.S.a k*(B+1:ℝ):=by
         rw [← hy]; refine (mul_le_mul_of_nonneg_left (show (separation a 0:ℝ)≤ ((c*B+c:ℕ):ℝ) from ?_) ha.le).trans_eq (by push_cast; ring)
         exact_mod_cast (show separation a 0 ≤ c*B+c by omega)
      have hv : (128*(t:ℝ)^2*C.S.a k)/16 ≤ 2*(C.S.a k*(B+1:ℝ)):= hp.trans (h₂.trans (le_trans (le_of_eq (mul_assoc ..)) (mul_le_mul_of_nonneg_left hs zero_le_two)))
      have ht:8*((t:ℕ):ℝ)^2 ≤ 2*((B:ℝ)+1):= by apply le_of_mul_le_mul_right (a:=C.S.a k) _ hp'; linarith only [hv]
      exact_mod_cast (show ((t:ℕ):ℝ)^2+1≤ (B:ℝ) from by nlinarith only [ht,hb])
    have hR: C.S.a k*B ≤ C.S.a k+‖y‖:= by
       rw [← hy,mul_assoc]; have hx: ((c*B:ℕ):ℝ)≤ c+(separation a 0:ℝ):= by exact_mod_cast (show c*B≤ c+separation a 0 by omega)
       rw [Nat.cast_mul] at hx; exact (mul_le_mul_of_nonneg_left hx ha.le).trans (by rw [mul_add]; linarith only [h₁])
    change B ≤ (X)
    let K := spacingFactor (C.path.levels) k
    have hk : (1:ℝ) ≤ K := Nat.one_le_cast.mpr (factor_pos C k)
    change B ≤ K*(1024*t^2); suffices hu:(B:ℝ)≤(K:ℝ)*1024*(t:ℝ)^2 by refine Nat.cast_le.mp (show (B:ℝ) ≤ (↑(K*(1024*t^2):ℕ):ℝ) from ?_);push_cast;nlinarith only [hu]
    have hC : (B:ℝ)≤ 1+512*K*(t:ℝ)^2:= by
        apply le_of_mul_le_mul_left (a:=C.S.a k) _ hp'; change ‖y‖ ≤K*(4*(128*((t:ℕ):ℝ)^2*C.S.a k)) at hh; linarith only [hR,hh]
    nlinarith only [hC,hb,(show (1:ℝ) ≤ K*(t:ℝ)^2 from one_le_mul_of_one_le_of_one_le hk (by nlinarith only [hb]))]
end
end YM.MergeProof.Ribbons
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
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
    (b w : ℝ) (a:Bool→ℝ) (o:Site (C.side j p)) (hf:J≤k) (hk:k ≤ m) (hN:j < N) (hm:m+1 < j)
local notation "v"=> Site (C.side J p)
local notation "Q"=> hands C p J
local notation "ξ"=> Mix.camp C p J
local notation "y"=> bites C J j p o
local notation "T"=> center C.S p (le_trans hf (le_trans hk (le_trans (m.le_succ) (le_trans hm.le hN.le)))) 0
local notation "Wt"=> march (fun _:Site (C.side J p)=> b) φ k m
def crowd (A:Levels G)(k:ℕ):= (2*(spacingFactor A k*1024*(A.budget k).B)+1)^4
def picketW (A:Levels G)(j i:ℕ)(δ φ:ℕ→ℝ)(η:ℝ)(a:Bool→ℝ)(b:Bool) : ℝ:=
    Salt.tow (fun x:Name Unit=>δ i * krill A.S j (i+1) (δ j*(φ j*a x.2))) ((A.budget i).supportExponent+1/2) η (crowd A i) ((),b)
def ventWide (A:Levels G)(j i:ℕ)(δ φ:ℕ→ℝ)(η:ℝ)(a:Bool→ℝ):= picketW A j i δ φ η a false*picketW A j i δ φ η a true
variable (t:Bool→ℕ) (s: (i:Bool)→ C.label (t i)) (h:C.Makes)(hh:Scrim C W u ψ φ δ ζ r D)(ht':μ ≤ m)(hR:Created C)
local notation "l"=> crowd C.path.levels (m+1)
local notation "W'"=> (fuga C.path.levels (m+1))
local notation "k₀"=> scurry C.path.levels r χ η (m+1)
local notation "h!"=> lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm.le hN.le)
local notation "A!"=> ventWide C.path.levels j (m+1) δ φ η a
local notation "B!"=> ((Q').B^2+1+2*pollsW C.path.levels (m+1))
-- consumer at arbitrary two compatible placements. financial later
include h hh ht' hR
lemma mutationWide (L:Stock.Tabs C.path.levels) (hx: Stock.Tabs.opens C.path.levels 1 J k)(hK:C.ref d ≤ k)(ht:∀ i,C.ref (t i) ≤ j) (hM:∀ i,a i*Spindle.paid C (t i) j N p (s i) ≤ ζ (t i) j)(hw:∀ i,0<a i)(htq:GridApprox.room C.path.levels J m (lensScope C d))
   (hΩ: B! ≤ (C.S.toDepth (le_trans hf (le_trans hk (m.le_succ))) p).count.val)(hg: W'/16 ≤ ‖C.S.place o‖)(hy:‖C.S.place o‖ ≤(spacingFactor C.path.levels (m+1):ℝ)*4*W') (f:Bool→ Config G (C.side N p)→ℂ) (hF:∀ i, f i = MergeProof.item C (t i) N p (s i) (fun j=> y j (0,i)) (1,false))(hi:∀ i,Continuous (f i))(ha:∀ i, Interior ((T).chamber 0) (f i)) (hc₀:∀ z:C.label d,Interior ((T).chamber 0) (C.O N p z 0)) (hr:Thor C.path δ r D σ χ μ) (hη:0<η)(hq:η≤1)(hD:Throws C.path N p m (D N p m h!) (Next.Foundations.hol G) U x)(hx':1≤x)(hc:χ j≤1)(hY:∀ i:ℕ,m+1 ≤ i→∀ hi:i<j, MergeProof.Float.Runs (D N p i (hi.trans hN)) (C.path.levels.clock.op i p) (6*((C.S.block i).val:ℝ)))
   (hFq:(((Q').B + (Q').B+1 :ℕ):ℝ)^4*k₀ ≤ 1/2)(hΔ:Real.exp k₀-1≤1) (hb: 0 < b)
   (hL:march (fun _:Unit=>b) φ k m () ≤ δ m * (A!/(16*x)))
   (hV:0< A!)(hA:4*(1+(C.path.levels.params m).columns)*(2*(C.S.a (m+1)^d*(x*(4*(1/A!)))))≤ e)
   (hp:32*(1+(C.path.levels.params m).columns)*b * ‖alto C.path k d‖*(e/gainChart C.path m k) ≤ ζ d k/2)
   : ∃ z:C.label d,Next.UVStress.quota C d m N p z ≤ 2*e∧ (T).rootTest (C.beta N p) (f false*f true-C.O N p z 0) ≤ 2*(stakes C J k / b):=by
   let hm':= hf.trans hk; let hJN:= hm'.trans (show m<N from by omega).le; let h'J:= hm'.trans m.le_succ; have he:=hm.trans hN
   let F:= capped C J p N hJN f; let P:=fun i:v=> Equiv.swap 0 i
   obtain ⟨hξ,hz⟩:= maximizingWide C j p (m+1) o hm.le hg (by simpa only [mul_assoc] using hy); have hv:Brine C.path k δ φ:=⟨fun i _=> hh.costs.stay.water _ (Nat.zero_le i),fun i _=> hh.costs.stay.mint _ (Nat.zero_le i),fun i _=> hh.costs.stay.split _ (Nat.zero_le i),fun i _=> hh.costs.stay.support _ (Nat.zero_le i)⟩
   have hS:= vizier C J j p (m+1) o (show Brine C.path (m+1) δ φ from ⟨fun i h=>hv.water i (by omega),fun i h=>hv.mint i (by omega),fun i h=>hv.split i (by omega),fun i h=>hv.support i (by omega)⟩) h'J hξ hz hΩ
   have hU:Integrable (birth (Aged v) (R N) F) (prior G _):= (hatCont C N p F (fun i=> cappedC C J p N hJN f i (hi _)) (show Continuous (R N|>.eval) by rw [(h.wilson.starts ..).2]; exact bare_cont _) _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   have hX(i : ℕ)(he:J ≤ i):Occupancy (ξ i) (r m):= fun a=> (Occupancy.of_injective (show Injective (ξ i) by rw [show ξ i=(C.S.toDepth he p).embed from funext fun j=> elev C J p i he j]; exact (C.S.toDepth he p).embed_injective) a).trans (hh.back _)
   have hVq (i:v)(j:Bool): F (i,j)=stepUp (Q i) (ξ N i) (F (0,j)):= by unfold F; rw [cappid]; exact canned ..
   let p':= C.S.a (m+1)^d*(x*(4*(1/A!)))
   let s':= (f false*f true); let q i c:= F (i,false) c * F (i,true) c; let Y:=gust C.path N p N (birth (Bud v) (R N) q) m (h!).le
   have ht'(i:v): Wt i=march (fun _:Unit=>b) φ k m ():=by
      suffices h:∀ j:ℕ,march (fun _:Site (C.side J p)=>b) φ k j i=march (fun _:Unit=>b) φ k j () by exact h m
      intro j; induction j with
      | zero=>rfl
      | succ j ih=> by_cases hv:k ≤ j <;> simp [march,hv,ih]
   have hT: ∃ Q₀:Coefficient T' (C.side m p), Q₀.Format 0 (Next.Foundations.hol G) (R m)∧Q₀.remBound 0 (R m) (kappa H m) p'∧ (T').coeffSize Q₀.x≤p'∧Served (R m) (fun i=> radiant (alto H m d) (Q i) (ξ m i) (Q₀.exponentialEntry 0 U (R m))) (fun i=> sunny (R m) Q₀.forced (Q i) (ξ m i) (alto H m d)) Y (ξ m) Wt (P' m).supportExponent 1:=
      Ribbons.sail C N m p d ξ y Q 0 P Wt t s (fun _=>(1,false)) a F hN hm h hh.costs hr ‹μ≤ m› (hK.trans (hk.trans m.le_succ)) ht hM hw (uphill C J m p N hm') (P_on C J p) (zeroMama C J p m hm') (fun i=> biteF ..) (fun i _=>Equiv.swap_apply_left ..) (fun b hb h i he c=> bit C J j p b o (by omega) i c) (retina C J j p N o (by omega))
      (fun i _ he=> by rw [show (C.path.levels.clock.op i p).ratio= C.S.toDepth (Nat.le_succ i) p from ratio_same ..]; exact bitesParent C J j p i o (by omega) i.le_succ he) (fun i hK' he a=> (Occupancy.of_injective (Edition.injected _ _ (P' i|>.B_pos) (hS i hK' he)) a).trans (hh.back _)) (fun i hK' he=> ⟨fun _ _ a _ b _=> hS i hK' he a b⟩) (fun i _ j=>hVq i j)
      (fun i=>(cappid ..).trans (hF i)) hU hc hY (hX m hm') (hX _ h'J) hη hq (by unfold crowd; apply coverB C J j p _ o h'J; exact hz.trans (le_of_eq (by unfold pollsW polls; ring))) hFq hΔ (A:= A!) rfl (march_pos C.path k δ φ (fun _:v=>b) (fun _=>hb) hv _ hk) (fun i=> (ht' i).le.trans hL) hD hx'
   obtain ⟨Q₀,hR,hφ,hB,hZ⟩:= hR.bridge C N p d m (Q) (ξ m) Wt Y hT
   have he : q=(fun i=>(T).copy i s'):= funext (fun i=> funext fun c=> cap_mul C J p N hJN f i c)
   have hu:= lt_of_lt_of_le zero_lt_one hx'; have hw:0 < p':= mul_pos (pow_pos (C.S.a_pos _) _) (mul_pos hu (mul_pos (by norm_num) (by positivity)))
   have hy':(C.labels.level d).coeffSize Q₀.x+p' ≤ 2*p':=by linarith only [hB]
   refine bequeathed C N m k p d h b hh L J hx s' Q₀ hK (hk:=hk) h! htq hc₀ ((hi _).mul (hi _)) ((ha false).times (ha true)) hR hφ hy' (mul_pos zero_lt_two hw) hA hb hp ?_
   unfold Y at hZ; rw [he] at hZ; exact hZ
end
end YM.MergeProof.Ribbons
