import YM.FullVolume.Glide.Bill
/-! One-step norms & betas. On Common orbit, not required balanced. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lark.Glide
open Function Filter Set MeasureTheory Lattice RG Pressure RG.Shoot Wilson Precision RG.Supply Input Org
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Song Geo
open ConnectedActivityE6
open Push.PriceCompiler Further.StrongStartup UniformSpace
open WilsonStartup Progress.DirectedRecipe Time UVNext.CouplingReset Roof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f:Side}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A} {p m N n:ℕ}
open Muse Pass FullVolume.Urns FullVolume.Shadow FullVolume.Amp
variable {t ξ w d q:ℝ} {L:Lyrics R t t}
    (Y:Plato L q w d ξ)(O:Ops L N p)
-- layout norm at all periods does not forget Reads; val if proof.
local notation "Ω"=> A.B.a.clock.hatBeta
local notation "B"=> A.B.a
local notation "K"=> A.B.kin
namespace Window
-- normalized angle scripts. not necessarily tied back to fixed beta0
structure Runup (O:Ops L N p) (U:ℕ→ℝ) where
    liftP : ∀ i (h:i ≤ N), suites O i h
    valid:∀ i h,‖liftP i h‖ ≤1/8
structure Cage {N p:ℕ} (O:Ops L N p)(U:ℕ→ℝ) (d':ℕ)(B':Runup O U):Prop where
    moods : ∀ i,i≤N → mild (A.B.a.clock.hatBeta i) (U i)
    route:∀ i (hi:i<N),i<d' → room O (B'.liftP i hi.le) = room O (offer O hi (U (i+1), B'.liftP (i+1) hi))
    seats:∀ h:d' ≤ N, room O (B'.liftP d' h)=0 ∨ N=d'
variable {O} {U:ℕ → ℝ}
include Y
lemma guild {O:Ops L N p}(h:∀ i,i≤N→mild (A.B.a.clock.hatBeta i) (U i))(z:ℕ): ∃ W:Runup O U, Cage O U z W ∧ (∀ hx:z ≤ N, W.liftP z hx=0):=by
    let Q(i):=∀ h:i≤N,{x:suites O i h// ‖x‖≤1/8}
    let e(i:ℕ):Q i:= fun hx=> ⟨0,by norm_num⟩
    let f (i:ℕ) (hv:i<N)(w: Q (i+1)): Q i:=fun hy=> if i< z then ⟨offer O hv (U (i+1), (w hv).val), compass Y O (h:=hv) (U (i+1), (w hv).val) (h _ hv) (w hv).property|>.1⟩ else e i hy
    let R (m:ℕ)(h:m≤N): Q m:= Nat.decreasingInduction (motive:=fun i _=> Q i) f (e N) h
    refine ⟨⟨fun i h=>(R i h h).val,fun i h=> (R i h h).property⟩,⟨h,fun i hi hx=> ?_,fun hx=> ?_⟩,fun hz=>?_⟩
    · dsimp only
      unfold R; rw [Nat.decreasingInduction_succ_left _ _ hi]; unfold f; rw [if_pos hx]
    · dsimp only; rcases hx.eq_or_lt with hz|hz
      · exact Or.inr hz.symm
      left; unfold R; rw [Nat.decreasingInduction_succ_left _ _ hz]; unfold f; rw [if_neg (by omega)]; exact Completion.coe_zero
    dsimp only; unfold R; rcases hz.eq_or_lt with h'|h'
    · subst N; rw [Nat.decreasingInduction_self]
    rw [Nat.decreasingInduction_succ_left _ _ h']; unfold f; rw [if_neg (by omega)]
omit Y
section comp
variable {O:Ops L N p}{d':ℕ} {T B':Runup O U}
def gifts (B':Runup O U)(i:ℕ): cloud (A.B.a) i p:= if h:i≤N then room O (B'.liftP i h) else 0
def price (T:Runup O U)(m:ℕ):ℝ:= if h:m<N then costP O h (U (m+1),T.liftP (m+1) h) else 0
lemma gems (i:ℕ) : ‖gifts T i‖≤ 1/8:=by
    unfold gifts; split
    · rw [normP]; exact T.valid ..
    norm_num
lemma prime (i:ℕ)(h:i<N):price T i=costP O h (U (i+1),T.liftP (i+1) h):=dif_pos h
lemma lifts (i:ℕ)(h:i≤N):gifts T i= room O (T.liftP i h):=dif_pos h
variable {Sp:Runup O U} (W:Cage O U d' T) (h:Cage O U N Sp)
include W h Y
local notation "c₀"=> 8*glint
lemma culprit (hn:d'≤ N)(i:ℕ)(hi:i≤ d'): dist (gifts T i) (gifts Sp i) ≤ (c₀)^(d'-i):=by
      induction hi using Nat.decreasingInduction with
      | self=> rw [dist_eq_norm]; simp only [Nat.sub_self,pow_zero]; exact (norm_sub_le ..).trans ((add_le_add (gems _) (gems _)).trans (by norm_num))
      | of_succ i hi ih =>
        have hx:= hi.trans_le hn
        let V:= room O (T.liftP (i+1) hx); let q:= room O (Sp.liftP (i+1) hx)
        rw [lifts _ (show i+1 ≤ N from hx), lifts _ (show i+1≤N from hx)] at ih
        have hz := (curls Y O ((U (i+1), T.liftP (i+1) hx):ℝ × Home (O.plan (i+1) hx)) (W.moods _ hx) (T.valid ..) ((U (i+1), Sp.liftP (i+1) hx):ℝ× Home (O.plan (i+1) hx)) (h.moods _ hx) (Sp.valid ..)|>.1); dsimp only at hz; rw [dist_self, max_eq_right (dist_nonneg : 0≤ dist V q)] at hz
        rw [lifts i hx.le, lifts i hx.le, W.route i hx hi, h.route i hx hx]; apply hz.trans; rw [show d'-i=d'-(i+1)+1 from (by omega), pow_succ']; exact mul_le_mul_of_nonneg_left ih (by norm_num [glint])
end comp
section actor
open Contest
variable (O) (p':Contest N p L)
abbrev saga (Z:Contest N p L) (i:ℕ):= toLambda (Ω i) (Z.trail i).beta
def dices (Z:Contest N p L):Runup O (saga Z) := ⟨fun i hi=>homeP Y O Z i hi,fun i hi=> sparkN Y O Z ⟨i,by omega⟩⟩
include Y O p'
lemma cageM : Cage O (saga p') N (dices Y O p'):=by
    refine ⟨mildS Y p',fun i hi hk=>?_,fun _=>Or.inr rfl⟩
    let k:Fin N:= ⟨i,hi⟩
    let x:=offer O hi (p'.pose Y O k.succ); let y:suites O i hi.le:=p'.chair Y O k.castSucc; change room O y= room O x
    have hc : ((x:Completion _):Completion (Home (O.plan i hi.le)))=↑y:= (p'.forthB Y O k).1
    apply dist_eq_zero.mp; rw [firm,← Completion.dist_eq,hc,dist_self]
lemma census (i:ℕ)(h:i<N):price (dices Y O p') i= p'.owed ⟨i,h⟩:=by rw [prime i h]; exact forthB Y O p' ⟨i,h⟩|>.2
end actor
end Window
end YM.PhysicalNext.Repeat.Lark.Glide
