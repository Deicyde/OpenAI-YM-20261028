import YM.MergeProof.North.Angled
import YM.MergeProof.North.Shawl
import YM.MergeProof.Thimble





set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Graces
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}(g:G.Simple) {X : Metals G} {D:Rolls X.p} {A:Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n d:ℕ} (hm:m<N) {Z:Bolt A} (h:Nest R Z) {Q: In A.B.a m n}
local notation "H" => Issue.trail Z
set_option quotPrecheck false
local notation "O" => (H).rep N n m
local notation "S" => (H).rep N n (m+1)
local notation "i₀" => A.B.a.clock.J m
local notation "j₀" => A.B.a.clock.J (m+1)
local notation "B" => A.B.a.budget m
local notation "ΔB" => A.B.a.budget (m+1)
local notation "Q'" => R.target j₀ i₀
local notation "P" => X.p.profile i₀
local notation "o" => (0:Site (A.B.a.S.side m n))
local notation "L₀" => D.L j₀
local notation "f₀"=>A.B.a.clock.hatBeta m
local notation "δ" => A.B.a.clock.forcedAllowance m
local notation "ξ" => (R.shape.μ j₀ i₀)
local notation "T₀" => YM.Labels.frames G
local notation "F" => ((YM.Labels.frames G).level d)
local notation "S'" => A.B.a.clock.op m n
variable (hC:Mallow.Arrives R.shape A.delay)(U: Spring R N m n l v Q)(x:Icc l v)
    (he: (Issue.trail Z).rep N n m = U.result x.val) (ht: (Issue.trail Z).rep N n (m+1) = Q x.val) -- careful Hull.L
variable {a:ℝ}{K: ℕ→ℝ} {W:Bid.Worth} (hp : Doors.Budget A.B.a K W)(hh : Comply R.shape A.delay)
    (hd : d ≤ A.B.a.clock.J m) (T:Cloud (Q x)) (hω: (0:Site (A.B.a.S.side m n))∈T.live.crest.image (A.B.a.clock.op m n).ratio.parent)
local notation "T!" => houseS U x
local notation "V₁" => pupil U x T.live
local notation "V₂" => pupil U x T.pale
set_option quotPrecheck false
local notation "v'" => ((D.L (A.B.a.clock.J (m+1))).val:ℂ)^d
local notation "X!" => Blush.scope (T!) T o
local notation "M" => Blush.screen (T!) T V₁ V₂ v' F
local notation "w" => authors A.B.a m
local notation "κ" => Real.sqrt δ
local notation "fi" => coinFee G P d L₀ -- ambig
local notation "vh" => vigors G P d
include hd hp
open MergeProof
local notation "sandbox" => sandboxK U x
include hm g hC
local notation "aT" => ((D.L (A.B.a.clock.J (m+1))).val:ℝ)^d
include ht he h hh
-- ANY budgets.at rooted posterior marks
variable {d':ℝ}

lemma respects (T:Lotus.Leaf (Q x)) (Qe:ℝ)(heH : (fi+|2*aT*(Mercury.volt f₀ ((P).order) ((P).power)*((Q').goal L₀ f₀)⁻¹)|) * host G P d ≤ Qe) (i: Set Wing)(hi:T.turn∈i)(htS:0∈ T.crest):
    MergeProof.Coupon (localSection G d) (Issue.trail Z) N n m (hol G) (MergeProof.prose T) (entry T) 0 (duet _ _ _ _ he ht sandbox) i (Complex.ofReal ∘ T.cicada) 0 (Qe*MergeProof.load T) (Qe*MergeProof.load T) (2*MergeProof.load T):=by
   let M' : Lotus.Leaf (Q x):= ⟨T.turn,0,(fun _ _ _ _=>rfl),fun _ e=> (e rfl).elim,T.blank,T.weight,fun i=>by simpa using T.profit,(fun _ _=> rfl),measurable_const⟩
   let Z':= Blush.Cloud.mk T M' rfl rfl
   have hω : o∈T.crest.image (S').ratio.parent:=support_zero _ _ htS
   let F':=T.cicada; have hE : M'.cicada=0:=by
      funext i; unfold Lotus.Leaf.cicada; have ht(k): M'.bun k i=0:=by
        unfold Lotus.Leaf.bun; split
        next=> unfold Lotus.Leaf.bill; split; exact zero_mul _; rfl
        next=> rfl
      simp_rw [ht,tsum_zero,mul_zero]; rfl
   have hz:M'.ingredient=0:=rfl; have hk: (Complex.ofReal ∘ T.cicada)=Z'.milk:=by funext i; rw [Cloud.milk,show Z'.pale=M' from rfl,hE]; simp; rfl
   let r:= Qe*MergeProof.load T; erw [hk]
   have hv : MergeProof.prose M'=0 := by funext i; unfold MergeProof.prose; rw [hz]; cases M'.turn <;> simp
   have hz':entry M'=0:=by funext i V; unfold entry; rw [hz]; cases M'.turn <;> simp
   refine thunder g hm h hC U x he ht hp hd Z' i hi htS Z'.milk (MergeProof.prose T) (entry T) _ _ _ (by rw [show Z'.live=T from rfl,show Z'.pale=M' from rfl,hv,smul_zero,add_zero]) (by rw [show Z'.live=T from rfl,show Z'.pale=M' from rfl,hz',smul_zero,add_zero]) ?_
   have hU := Rain.jersey (A:=A) (m:=m); have hR:= step_paid A.B.a m; have hy:=hC _ _ (A.B.valid.pays m) _ hR
   let C:= houseS U x; obtain ⟨A₀,ba,q,t',z,F'₀,t₃,t₄,t₅,t₆,k',hB,hX,N₀,hN'⟩:=hy.1.2 _ _ _ _ (Opera.protocol A.B hm R.pledging.conducts.full) (Q x) _ C
   have hEx:= R.pledging.agenda _ _ hR|>.1; rw [← hU.2.2.1] at hEx
   obtain ⟨f,hV,hP⟩:= Mercury.shelves C N₀ hN' hB hEx hy.1.1 rfl rfl hU.1 o Z' hω v'
   let E:=2*aT*(Mercury.volt f₀ ((P).order) ((P).power)*((Q').goal L₀ f₀)⁻¹); let z:=MergeProof.load T
   have hx:0 ≤ z:= T.profit.trans ((Q x|>.p).loMass _ _ T.profit)
   apply suppliesLeaf g hm h hC U x he ht hp hh hd Z' hω ((fi+|E|)*z) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg E)) hx)
   · refine ⟨f,budget_loosen hV ?_,hP⟩; have hk: ‖v'‖= aT:=by simp
     rw [hk,hU.2.1]; exact mul_le_mul_of_nonneg_right ((le_abs_self E).trans (le_add_of_nonneg_left (coin_pos ..).le)) hx
   show _ ≤ r; rw [mul_right_comm _ z]; exact mul_le_mul_of_nonneg_right heH hx
end YM.PhysicalNext.Repeat.Graces
