import YM.UVExtension.Hearth.Spoon
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Hearth
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open MeasureTheory Push GridApprox Mast Steady
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} (S:Uses Q hG) (v:Keys S) {C:ℕ→ℝ}{W:Bid.Worth}(R:Legato.Bandage Q C W)
    (d m N n:ℕ)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T'"=> (Orchard.Path S v).levels
local notation "π"=> localSection G d
local notation "O!"=> hol G
open Metric Wet Wren
variable {V:Org.Bolt A}(a:Upland.Arc Q S V)
variable (x:Rose S)(hv : Tendsto (fun i=>(v i n).val) atTop (𝓝 x.val))
open Relay Mast.Cellar Steady Push GridApprox Accent Cells

variable {t:ℕ→ℕ}{S v R} (U:Cellar S t R) (K:ℕ→ℕ)(h:Scrim (U.yard v) W (far A.B.a) (waybill A.B.a) (near A.B.a) (renal A.B.a) (Legato.Bandage.fly A.B.a) (mutt A.B.a K) (Orchard.roof S v))
    (hK: Stock.Tabs A.B.a) (J k:ℕ)(w:ℝ)(hw:0<w)(hz:Stock.Tabs.opens A.B.a 1 J m)
local notation "C0"=> yard v U
local notation "F"=> (C0|>.labels.level d)
local notation "K0"=> lensScope C0 d
local notation "o!"=> (0:Site ((C0).side k n))
local notation "T!"=> A.B.a.S

open Extraction OS RelayDifference
open Pans Lacing Lyrics Motion
variable (p: Keys S)(hp:v N n= p N n)(hx:t d ≤ N)
local notation "l"=> t d
local notation "Q'"=> Orchard.Path S p
local notation "P0"=> yard p U
-- manufacture Top terrain depends on only this rep. Proof irrelevance Keeper.
include hp
omit hp in
private def glaze {n:Side}(A : Activities G n) : Activities G n := { A with
  forced := fun i => {A.forced i with extraTest:=fun _ => True} }
omit hp in
private def plate (n:Side)(R : RG.Rep G n) : RG.Rep G n := {R with activities:=glaze R.activities}
open Planned.GuardedAtom.Guard
omit hp in
private def bornAt {n:Side}(d:ℕ)(T:RG.Rep G n)(h: HasSlots T.p T.activities): ((frames G).level d).Coeff→ Coefficient ((frames G).level d) n :=
   let V:=Keeper.sufficient h
   let Y: Shelf (glaze T.activities):=⟨V.code,V.support,V.inventory,fun _ _=>trivial,Keeper.blank h⟩
   Extra.Histories.born (localSection G d) (plate n T) 0 Y d
omit hp in
private lemma alone (d N n:ℕ)(T:History G)(h:HasSlots (T.rep N n N).p (T.rep N n N).activities) (x:((frames G).level d).Coeff): terrain T N n (hol G) N (Planned.GuardedAtom.Guard.summit _ (localSection G d) T N n (Keeper.sufficient h) (Keeper.blank h) d) x = (Eyelet.Eye (bornAt d (T.rep N n N) h x) (hol G) (T.rep N n N) (Real.sqrt (T.levels.clock.forcedAllowance N))).2 := rfl
omit hp in
private lemma replaceR {k:Side}(d:ℕ)(T Z: RG.Rep G k)(h:T=Z)(x: HasSlots T.p T.activities)(y: HasSlots Z.p Z.activities)(q:ℝ)(U:((frames G).level d).Coeff): HEq ((Eyelet.Eye (bornAt d T x U) (hol G) T q).2) ((Eyelet.Eye (bornAt d Z y U) (hol G) Z q).2):=by subst Z; rfl
omit hp in
private lemma wicks (d N n:ℕ)(T:Levels G)(U V: ∀ (j:ℕ)(i p:ℕ), RG.Rep G (T.S.side p i))(he: U N n N=V N n N)(hx:HasSlots (U N n N).p (U N n N).activities)(hy:HasSlots (V N n N).p (V N n N).activities)(x:((frames G).level d).Coeff) : let Z:=History.mk T U; let Q:=History.mk T V; HEq (terrain Z N n (hol G) N (Planned.GuardedAtom.Guard.summit _ (localSection G d) Z N n (Keeper.sufficient hx) (Keeper.blank hx) d) x) (terrain Q N n (hol G) N (Planned.GuardedAtom.Guard.summit _ (localSection G d) Q N n (Keeper.sufficient hy) (Keeper.blank hy) d) x):= by
    intro Z Q; exact HEq.trans (heq_of_eq (alone d N n Z hx x)) ((replaceR d (U N n N) (V N n N) he hx hy (Real.sqrt (T.clock.forcedAllowance N)) x).trans (heq_of_eq (alone d N n Q hy x).symm))
omit hp in
private def highest (z:Rose S)(d:ℕ)(X:((frames G).level d).Coeff): Eyelet.Cow G (A.B.a.S.side N n) (A.B.a.budget N) d (hol G):=
   let P:=S.realBeat (z.val) N n N
   (Eyelet.Eye (bornAt d P (S.slotReady N n z.2) X) (hol G) P (Real.sqrt (A.B.a.clock.forcedAllowance N))).2
include hx
omit hp in
private lemma top_price (x: ((frames G).level d).Coeff): Vista ((U.cantors v d n).lyr N hx) N x=highest (N:=N) (n:=n) (S:=S) (v N n) d x:=by
   let h := (U.cantors v d n).lyr N hx; let T:=(U.cantors v d n).song N; have he: T.tone N=TopHat S v d n N:=h.head
   rw [h.takes N hx le_rfl]; change terrain H N n (hol G) N (T.tone N) x=_; rw [he]; exact alone d N n H (Vintage.YM.PhysicalNext.Repeat.Graces.Nest.born (housed S v) N n) x
omit hx

omit hp
-- avoid dependence on the other Keys in index-comparison proof
private abbrev Zf (G:Gauge) (d:ℕ):= ((frames G).level d).Coeff
private abbrev Staff (S:Levels G) (d n i:ℕ) := (Zf G d ≃ₗ[ℂ] Zf G d) × Card («H»:=S) ((frames G).level d) (p:=n) (A:=hol G) i
private def treater (z:Rose S): Staff A.B.a d n N :=
    (LinearEquiv.refl ℂ _,if h:IsLinearMap ℂ (highest (N:=N) (n:=n) z d) then IsLinearMap.mk' _ h else 0)
private def bandC (U:Cellar S t R) (z: Rose S) (i:ℕ)(w:Staff A.B.a d n (i+1)) : Staff A.B.a d n i :=
    let V:=Cellar.line U d n i N z; (w.1.trans (Lacing.steer (fun _:Motion=>V) (fun _:Motion=>w.2) (glaring A.B.a i n)), Lacing.crown (fun _: Motion=>V) (fun _:Motion=>w.2) (glaring A.B.a i n))
private def warp (z: Rose S) (m:ℕ)(h:m ≤ N): Staff A.B.a d n m:= Nat.decreasingInduction (motive:=fun i _=> Staff A.B.a d n i) (fun i _=> bandC (S:=S) d N n U z i) (treater (S:=S) d N n z) h
private lemma warp_self (z:Rose S): warp (S:=S) d N n U z N le_rfl=treater d N n z:=by unfold warp; exact Nat.decreasingInduction_self ..
private lemma warp_step (z: Rose S)(i:ℕ)(h:i<N): warp (S:=S) d N n U z i h.le= bandC d N n U z i (warp d N n U z (i+1) h):=by unfold warp; exact Nat.decreasingInduction_succ_left ..
private def wants (v:Keys S) (h:t d ≤ N)(m:ℕ): Staff A.B.a d n m := let X:= U.cantors v d n; ((X.song N).tone m|>.index, Vista (X.lyr N h) m)
private lemma timing (v:Keys S)(h:t d ≤ N)(i:ℕ)(hi:i<N)(hk:t d ≤ i): wants (v:=v) d N n U h i= bandC d N n U (v N n) i (wants (v:=v) d N n U h (i+1)):=by
    obtain ⟨ha,hb⟩:= Lyrics.eqst R (L:=Cellar.paths S v R U d n) (U.pay v d n) ((U.cantors v d n).lyr N h) i hk hi; exact Prod.ext (LinearEquiv.ext ha) hb
private lemma peakC (v:Keys S)(h:t d ≤ N): wants (v:=v) d N n U h N=treater d N n (v N n):=by
    let Y:= U.cantors v d n; let X:=(Y.lyr N h).Vista N; let V:= (Y.song N).tone N; let T:=highest (S:=S) (N:=N) (n:=n) (v N n) d; have he:(X: Zf G d→_)=T:=funext fun x=> top_price (v:=v) d N n U h x
    have hP:IsLinearMap ℂ T:= by rw [← he]; exact X.isLinear
    rw [treater, dif_pos hP]; apply Prod.ext; · change V.index=_; rw [show V= _ from (Y.lyr N h).head]; rfl
    exact DFunLike.coe_injective he
include hx
private lemma psalma (m:ℕ)(hm:m ≤ N)(ht:t d ≤ m): wants (v:=v) d N n U hx m= warp d N n U (v N n) m hm:=by
    induction hm using Nat.decreasingInduction with
    | self=> rw [warp_self]; exact peakC (v:=v) d N n U hx
    | of_succ i hi IH=> rw [warp_step (h:=hi), ← IH (ht.trans i.le_succ)]; exact timing (v:=v) d N n U hx i hi ht
omit hx
private lemma terminalC (v:Keys S)(h:t d ≤ N): (yard v U|>.factory d N n|>.terminal)= (warp d N n U (v N n) (t d) h).1:= (peak (v:=v) d N n U h).trans (congr_arg Prod.fst (psalma (v:=v) d N n U h _ h le_rfl))
include hp hx
lemma joinM : (yard v U|>.factory d N n|>.terminal)=(yard p U|>.factory d N n|>.terminal):=by
   exact (terminalC (v:=v) d N n U hx).trans ((congr_arg (fun z=> (warp d N n U z (t d) hx).1) hp).trans (terminalC (v:=p) d N n U hx).symm)
omit hx hp
-- exposé actual numeric family for every h-operation
abbrev roster (U:Cellar S t R): _root_.YM.Register G:= ⟨frames G, fun i=> A.B.a.S.a (t i), fun i=> A.B.a.S.a_pos (t i)⟩
def capsule (U:Cellar S t R)(x: Rose S)(d:ℕ)(L: ((frames G).level d).Coeff)(s: Site (A.B.a.S.side N n)): Config G (A.B.a.S.side N n) → ℂ := if hp:t d ≤ N then
   ((A.B.a.S.a N:ℂ)^d)⁻¹ • (localSection G d).places (((frames G).level d).scaled (A.B.a.clock.threshold N)⁻¹ ((warp d N n U x (t d) hp).1.symm L)) s
 else 0
lemma aligned (v:Keys S)(h:t d ≤ N)(x:((frames G).level d).Coeff)(s: Site (A.B.a.S.side N n)): (yard v U|>.O N n (d:=d) x s) = capsule (N:=N) (n:=n) U (v N n) d x s:=by
   unfold Family.O TransferData.cylinder; rw [terminalC d N n U v h]; unfold capsule; rw [dif_pos h]; rfl -- v argument order?

def served (U:Cellar S t R)(x: Rose S)(i:ℕ)(X': Fin i→ (roster U).Token)(o:Fin i→ Site (A.B.a.S.side N n)) := moment ( (S.realBeat x.val N n N).beta) (fun P=> ∏ j,capsule N n U x (X' j).1 (X' j).2 (o j) P)
lemma cordial (v:Keys S)(i:ℕ)(X':Fin i→ (roster U).Token)(hx:∀ j,t (X' j).1 ≤ N) (x:Fin i→ Site (A.B.a.S.side N n)): (yard v U|>.numeric N n X' x)= served N n U (v N n) i X' x:=by
    let F':Config G (A.B.a.S.side N n)→ℂ:=fun P=>∏ j,capsule N n U (v N n) (X' j).1 (X' j).2 (x j) P
    refine congr_arg (moment ((yard v U).beta N n) ·) (show (fun (V':Config G (A.B.a.S.side N n))=>∏ j,(yard v U|>.seen (X' j) (x j) V'))=F' from funext fun P=>?_); exact Finset.prod_congr rfl fun i _=> congr_fun (aligned (X' i).fst N n U v (hx i) _ (x i)) P

def smeared (x:Rose S)(i:ℕ)(F': Fin i→ (roster U).Token)(t': Test i):=
    (A.B.a.S.a N:ℂ)^(4*i)* ∑ r: Fin i→ Site (A.B.a.S.side N n), t' (points fun i=> A.B.a.S.place (r i))*served N n U x i F' r
lemma erose (v:Keys S)(i:ℕ)(F':Fin i→ (roster U).Token)(t':Test i)(hp:∀ j,t (F' j).1 ≤ N) : Order.smears (yard v U) N n F' t'= smeared N n U (v N n) i F' t' :=by
   unfold Order.smears; refine congr_arg (fun x=>(A.B.a.S.a N:ℂ)^(4*i)*x) (Finset.sum_congr rfl fun k _=> ?_); exact congr_arg (t' (Order.cells (yard v U) N n k)*·) (cordial N n U v i F' hp k)
-- avoid transporting schedule casts through opaque calibration in this proof
abbrev Depict (S: _root_.YM.Register G) d:= S.Ref d→L[ℂ] ℂ
def portrait (v: Keys S)(d:ℕ)(X:Dash.Shot (roster U)): Depict (roster U) d:= X.scan (C:=yard v U) d N n

def snapshot (z: Rose S) (d:ℕ)(X:Dash.Shot (roster U)): Depict (roster U) d :=
    let f (x : (roster U).Ref d):= smeared N n U z X.n (X.record x) X.f
    if h:IsLinearMap ℂ f then LinearMap.toContinuousLinearMap (IsLinearMap.mk' f h) else 0
lemma slipP (v:Keys S)(X:Dash.Shot (roster U))(h:t d ≤ N)(hz:∀ j,t (X.left j).fst ≤ N): portrait N n U v d X = snapshot N n U (v N n) d X :=by
   let f (x: (roster U).Ref d) := smeared N n U (v N n) X.n (X.record x) X.f
   let V:= portrait N n U v d X
   have he:⇑V=f:=by
       funext x; let L:= X.record x; have hL j:t (L j).1 ≤ N:=by by_cases he:j=X.i <;> simp [L,Dash.Shot.record,he,h,Function.update_of_ne,hz]
       exact erose N n U v X.n L X.f hL
   have hv : IsLinearMap ℂ f := by rw [← he]; exact V.toLinearMap.isLinear -- tactics
   rw [snapshot, dif_pos hv]; exact ContinuousLinearMap.ext (fun x=> congr_fun he x)
end YM.UVExtension.Hearth
