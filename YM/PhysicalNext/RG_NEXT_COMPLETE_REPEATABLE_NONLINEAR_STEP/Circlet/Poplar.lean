import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Circlet.Blare
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Circlet.Gongs
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Circlet.Meets
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Crowns
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Eagles
/-!
 # Dual inspections on age.Budget τ, reveal Φ survey.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Circlet
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury Graces
open Planned.PrimaryIntegral295 WaterLevels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{M : Metals G}{D:Rolls M.p}{A:Alloy M D}{Q:ℕ→ℕ→ Teller G}{C: Programs M.p}
   {r p:ℕ→ℕ} {R:ℕ→ℕ→Record}{B:Factor A}{V:Bolt A}
local notation "cc"=> A.B.a
variable {m N n d:ℕ} (hm:m<N)
local notation "J"=> A.B.a.clock.J (m+1)
local notation "T"=> A.B.a.clock.J m
local notation "B₁"=> A.B.a.budget m
local notation "B₂"=> A.B.a.budget (m+1)
local notation "X"=> A.B.a.clock.op m n
local notation "V0"=> ships A.B N m n
local notation "V1"=> forecast V m N n
local notation "L"=> D.L J
local notation "y"=> A.B.a.clock.hatBeta m
local notation "v"=> R J T
local notation "u"=> C J T
-- V prescription uses from conductor as well.
lemma shifting : (B₂).threshold=fiery G y L ∧ (B₂).B=radiusB (betaF G y L):=by
    have he : A.B.a.clock.hatBeta (m+1)= betaF G y L:= PriceCompiler.beta_eq A.B.valid m
    unfold fiery; rw [← he]; exact ⟨rfl,rfl⟩ -- fiery temp requires unfold
set_option quotPrecheck false
variable (hP:Circlet.Pitch M.p M.K Q C r) (hp: Pads D R Q M.K C A.delay) (hc: Decked C D R B.span B.shape A.delay) (hb:goodD M.p J T d)(hV:Nest B V)
include hm hP hp B hV
lemma united :Plays u v B₁ B₂ (query M.p M.K J T) V0 y∧ Plays u v B₁ B₂ (Q J T) V1 y:=by
  have hv:= step_paid A.B.a m; let W:= B.pledging.conducts
  have hi:=A.B.valid; have he:=hi.pays m
  have hF := hp _ _ he _ hv (first_le hi m)
  have hH n k s (h:s ≤ n) : Bid.Sworn (A.B.M.H n s) (A.B.a.S.side s k) G:=W.full _ _ _ h
  have hs:= (shifting (A:=A) (m:=m))
  obtain ⟨hX,hY⟩:= boats (p:=n) hP.crown V hm hH
  have hJ:= Rain.jersey (A:=A) (m:=m); have ht:= Rain.jersey (A:=A) (m:=m+1); have hD (T':Tube G (X)):= hF.earn B₁ B₂ rfl hs.1 hs.2 hJ.1 ht.1 hJ.2.1 ht.2.1 _ T' rfl (PriceCompiler.block_eq A.B.valid m)
  have hk:= venture (p:=n) V hm; have hx:100*(1+radiusB y)≤(A.B.a.S.side m n).val:=by rw [add_comm 1]; exact A.B.a.fits.sizeT ..
  -- Bulletin TRUE.Doesn't use acct hVat record.R.C? from Tube Offers.
  have h: Plays u v B₁ B₂ (Q J T) V0 y:= hD _ hk.1 hX hx
  refine ⟨{h with bulletin :=?_}, hD _ hk.2 hY hx⟩
  obtain ⟨l,T',Q,hS,a,hx,-,-⟩:= (hV.held N m n hm).1
  have hB:=hS.knows a hx
  exact (Psalm.Stage.directed W.hearing A.B hm hB.2 hB.1 (fun m' h'=>W.full _ _ _ (by simp at h'; omega))).1.enabled.make.bulletin
omit hm hV hp hP
include hc hb
omit hb
lemma vastly: 100*(B.span J T+20)*((B₁).B+1) ≤ (A.B.a.S.side m n).val:=by
  obtain ⟨h,hV⟩:= hc.width _ _ (step_paid A.B.a m); apply le_trans _ (A.B.valid.volume m n)
  apply Nat.mul_le_mul h
  change _+1 ≤ (1+(B₁).B+(B₂).B)^_
  exact le_trans (by omega : (B₁).B+1≤1+(B₁).B+(B₂).B) (le_self_pow₀ (by omega) (by omega : A.delay.growth J ≠0))
end YM.PhysicalNext.Repeat.Circlet
