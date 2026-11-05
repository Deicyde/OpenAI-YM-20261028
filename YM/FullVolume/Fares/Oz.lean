import YM.FullVolume.Gables.Vendee
import YM.FullVolume.Fares.Grand
import YM.FullVolume.Roll.Meridian
/-! Retrieve actual witnesses; layout for all mark stems. Ref t fixed pre calibration and ≥1: will allow reference motions auxiliary. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set MeasureTheory Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent
open Muse
namespace Campaign
set_option quotPrecheck false
structure Sky (R:Run G)(T:Campaign R) (Θ:Luna.Tableau T.width 300)(v:ℕ→ℕ→ℝ):Prop where
    supports i:100 ≤ (R.alloy.B.a.budget i).supportExponent
    fee i j:Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((R.metals.p.profile j).supportExponent+2) (R.kit.span i j)) ≤ (R.rolls.L i).val
    paid:Jams.PaysW R.kit.shape T.pay R.alloy.delay
    spire:Luna.Spire Θ R.kit.shape (Luna.costP R.metals.p R.rolls) R.alloy.delay
    sav:FullVolume.Paint.Tower.Sav G R.metals.p.profile R.y Θ v R.rolls.L
    earned:Mallow.Canyon T.width R.kit.shape R.y Θ v R.alloy.delay
open Boutique
section
variable {M : Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:ℕ→ℝ}{K:Bid.Worth}{b:Bandage X Y K}
/- Construction independent of p sampling. k>=1. later reserve may request hard-limit recipe. -/
lemma pillarCanyon (h:G.Simple){q:ℕ→ℕ}(hh:Ahead b q){c u t τ:ℝ}{L: Roof.Lyrics X u u}(Φ:Muse.Plato L c t t τ) (hP : Stationary.Artes.Cadre A.post A.B.kin)(he : Next.Free.Amplify A.B.M)(hy:Jams.Wild X.shape A.delay)(θ1:Luna.Tableau c 300) (v:ℕ→ℕ→ℝ)(hν:Jams.PaysW X.shape t A.delay)(hΩ:Luna.Spire θ1 X.shape (Luna.costP M.p P) A.delay)(hPγ:FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 v P.L) (hv:∀ i:ℕ,100 ≤ (A.B.a.budget i).supportExponent)(hψ:∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) (hG:Mallow.Canyon c X.shape Y θ1 v A.delay):∃ (R:Run G)(T:Campaign R), Locrian R∧ Jams.Wild R.kit.shape R.alloy.delay ∧ Nonempty (Pillars R T)  ∧ R.family.path.levels=A.B.a ∧ ∃ Θ, Sky R T Θ v :=by
    let C:=b
    choose s hp using fun d:ℕ=> ((eventually_ge_atTop 1).and (A.B.a.fits.deep.eventually_ge_atTop (d+3))).exists
    have hb (d): 1 ≤ s d:= hp d|>.1
    obtain ⟨T,⟨Z⟩,hD⟩:= FullVolume.rodB X Φ
    let ht(d):d+3 ≤ (Issue.trail T).levels.clock.J (s d):= hp d|>.2
    have hZ:=Z.receipts
    choose B hB using fun N p m (hm : m < N)=> Boutique.taste h (F₀:=L) hZ (hD N p) hm
    let U (N p:ℕ):Branch X T.history N p 0 := ⟨T.choice,fun i _ hm=> hZ.samples h _ _ _ hm,fun m _ he=> B N p m he⟩ -- dots need explicit
    obtain ⟨V,hC,hY,H⟩:= Bandage.coming h b hZ s ht U; let R : Run G:= ⟨M,P,A,X,Y,K,b,q,hh,T,Z,s,ht,ease U,V,hC,fun N m p hx=> Boutique.mountain T (B N p m hx),hY⟩
    let T':Campaign R:= ⟨c,τ,u,t,L,Φ,hD⟩; exact ⟨R,T',⟨hP,he⟩,hy,⟨hb,U,rfl,fun N p m hm=> hB N p m hm,H⟩,rfl,θ1,⟨hv,hψ,hν,hΩ,hPγ,hG⟩⟩
end
lemma operaShip (h:G.Simple)(w:ℝ)(hw:0<w):∃ (R:Run G)(T:Campaign R), Locrian R∧ Jams.Wild R.kit.shape R.alloy.delay∧ Nonempty (Pillars R T) ∧ R.family.path.levels.clock.kernel.penalty=w∧ ∃ v:ℕ→ℕ→ℝ, ∃ Θ, Sky R T Θ v:=by
   obtain ⟨X,P,A,F,L,Q,b,hY,hC,hYs,hW,hH,ξ,v,t,a,D,Φ,θ1,hν,hφ,hv,hψ,UΩ,hP,hZ⟩ := factorShip h hw
   obtain ⟨R,T,hx,hp,hb,h,hγ⟩:= pillarCanyon h hH Φ hY hC hYs θ1 UΩ hν hφ hP hv hψ hZ; rw [← h] at hW; exact ⟨_,_,hx,hp,hb,hW,UΩ,hγ⟩
end Campaign
end YM.PhysicalNext.Repeat.Legato
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.operaShip
