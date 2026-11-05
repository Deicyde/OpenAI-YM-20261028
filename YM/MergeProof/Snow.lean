import YM.MergeProof.Portions
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Postsale
import YM.Progress.CLASSICAL_KIN_RECURSION.Tent
import YM.Push.LOOP_COEFFICIENT.Frame.Panels



/-!
Exists binding ALL epochs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
variable {G:Gauge}
section
variable {M:Metals G}{D:Rolls M.p}{A:Alloy M D} (R:Factor A){f:ℕ→ℕ→ℝ}
-- on every calibration on this history, with epK well on-f
abbrev snows {s: Sheet G} (D:Rolls s) (j:ℕ) := 100*(j+7)*(D.L j).val
include R
lemma castle (B : Bolt A) (h : ShapePort A.B.a A.B.M f) {C : Family G} (ht:C.path=A.B.bake.make B.history) (hr:∀ j:ℕ,snows D j≤ A.delay.shells j) : ∃ K : RankCovariance.Binding C, K.world≍ A.B.M ∧ K.prices=M.K:=by
   have hh N i p (hh:i ≤ N): ((A.B.bake.make B.history).rep N p i).path=A.B.kin.path N i := by
      change (B.history N p i).path= _; rw [((B.sticks N p).prices i (Nat.zero_le _) hh).1.path,A.B.bases]
   have hl (m p : ℕ) : Bid.Larger (G:=G) (A.B.a.clock.op m p) := by
      let a:= A.B.a; let W:= A.delay; let S:= a.clock.op m p
      have hv := A.B.valid.volume m p; let j := a.clock.J (m+1)
      have h1 : W.shells j ≤ (a.S.side m p).val := (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)).trans hv
      refine ⟨(a.blocks m p).branches, ?_, ?_⟩
      · have he : Pressure.macroR S.patch = (j+7)*(a.S.block m).val := by change (j+3)*(a.S.block m).val+4*(a.S.block m).val= _; ring
        change 100 * Pressure.macroR S.patch ≤ _
        rw [he, Extra.Iteration.block_eq A.B.valid,← Nat.mul_assoc]; exact ((hr _).trans h1).trans (by rw [S.sizes]; exact Nat.le_mul_of_pos_right _ S.patch.L.pos)
      change _ < (a.clock.schedule.side m p).val
      have := a.fits.sizeT m p; omega
   have hw := R.pledging.conducts.full
   rcases C with ⟨path,w,y,t,z,r⟩; change path = _ at ht; subst path
   exact ⟨⟨A.B.M,M.K,_,h,A.B.plan,fun N i hi _=> hw N i _ hi,hl,fun N i hv p=> (hh _ _ _ hv).symm ▸ A.B.support.links N i hv⟩,HEq.rfl,rfl⟩
end
-- pan votes. leave timeline on receipt. costs after-L possible. no shape/scalar claims on projections.
lemma capitalSnow (s:Sheet G) (K:MapPrices) (ht:Tendsto (fun i=>(s.profile i).order) atTop atTop) : ∃ k P μ, PreStand s K P k μ ∧ Shops K s k P μ ∧ (∀ i,∀ᶠ j in atTop,i∈k j) ∧∀ l:ℕ→ℕ, PreStand (ThroughLaunch.raise s l) K P k μ ∧ Shops K (ThroughLaunch.raise s l) k P μ:=by
   choose g hp using InteractingRank.entries s K; obtain ⟨p,k,t,hp',-,hf,hT⟩:= cultivate s K (fun _=>g) (fun i=>i+6) (fun _=>le_rfl) (fun _=>hp) ht
   obtain ⟨N,hN⟩:= Soft.shapers K s k p
   let m : ℕ→ℕ := N⊔t
   have hx : PreStand s K p k m:= by
      exact ⟨fun i j he=> ⟨(hT.reg i j he).1,fun L hL=> (hT.reg i j he).2 L ((le_max_right ..).trans hL)⟩,fun i j he L hL=> hT.potion i j he L ((le_max_right ..).trans hL)⟩
   have hv : Shops K s k p m:= ⟨fun j L hr=> hN.poles j L ((le_max_left ..).trans hr)⟩
   exact ⟨k,p,m,hx,hv,fun i=> (hp' i).2,fun l=> ⟨⟨hx.reg,hx.potion⟩,⟨hv.poles⟩⟩⟩
variable {s: Sheet G} {D:Rolls s}{Θ:Protection D}{Y: Delays Θ}{b:Bar Y}
lemma franchise (K: MapPrices)(O : HaarBudget G)(g : ℕ→ℝ)(hg:∀ i,0≤ g i) (hG:G.Simple)
   {P k μ} (hs:PreStand s K P k μ)(hv : Shops K s k P μ)(hl:∀ j,μ j ≤ (D.L j).val)(hp:∀ i,∀ᶠ j in atTop,i∈k j) (J:Wait b) : ∃ (Q : ∀ d,Tapes.Panel d) (U : Wait b), (J.readyHere ≤ U.readyHere ∧ J.window ≤ U.window ∧ J.minLength ≤ U.minLength) ∧ ∀ C : Family G, Paid U C.path.levels →∀ B:RankCovariance.Binding C,B.prices=K→∀ i:ℕ,
    ∃ᶠ j:ℕ in atTop, let v:= (Q i).patronize C (hg i); Tender v j ∧ Metering v O j (-3) ∧ (∃ l r, ShowHours (chart G) B (v.current j) j (-3) l r ∧ Vents B (v.current j) (chart G) l r j) :=by
   obtain ⟨Q,hQ,hpQ,v',z,Yq,hY,hY',hh⟩:= Soft.retailers K (chart G) hv (w:=D) hl (fun _=>1) (fun _ _=>1) (fun _ _=>one_pos) (chart_ok G)
   obtain ⟨I,hB,hb,-,hI⟩:= Soft.revolving K O (chart G) z Q g hg hG hpQ (chart_ok G) (recultivate s K hs v' Yq hY') hl hh J fun i=>(hp i).frequently
   exact ⟨fun i=>curtain (P i) (v' i) (Yq i),I,⟨fun j=> (hb j).1,fun j=> (hb j).2,hB⟩,fun C h B hV i=> (hI C h B hV i).mono (by rintro j ⟨h1,h2,h3,h4⟩; exact ⟨h1,h2,_,_,h3,h4⟩)⟩
end YM.PhysicalNext.Repeat.Legato
