import YM.FullVolume.Fares.Fio
import YM.FullVolume.Roll.Ebb
import YM.FullVolume.Stage.Rods
import YM.FullVolume.Trident
import YM.FullVolume.Rods
import YM.FullVolume.Scalar
import YM.MergeProof.South.FinalG
import YM.MergeProof.West.Ozone


/-! Calendared proof thru actual Base+Seed. Can pay more beforeL, delays and Wait. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
-- Unconditional existence through the actual Wcmain, ranks and Seed.
variable (hG:G.Simple)
include hG
theorem factorShip {β:ℝ} (h:0<β) : ∃ (M:Metals G)(P:Rolls M.p)(A:Alloy M P)(X:Factor A)(Y:ℕ→ℝ)(K:Bid.Worth)(b:Bandage X Y K),
    Stationary.Artes.Cadre A.post A.B.kin ∧ Next.Free.Amplify A.B.M ∧ Jams.Wild X.shape A.delay ∧ A.B.a.clock.kernel.penalty=β ∧ Ahead b (fun _=>1) ∧ ∃ ξ t τ a, ∃ (V:Roof.Lyrics X t t), Muse.Plato V ξ a a τ ∧ ∃ θ1:Luna.Tableau ξ 300,Jams.PaysW X.shape a A.delay ∧ Luna.Spire θ1 X.shape (Luna.costP M.p P) A.delay ∧ (∀ i:ℕ,100 ≤ (A.B.a.budget i).supportExponent) ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) ∧ ∃ UX,FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 UX P.L ∧ Mallow.Canyon ξ X.shape Y θ1 UX A.delay := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G β h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨q,hq⟩:=Muse.concert.exists
  obtain ⟨θ1⟩:= Luna.Tableau.access 300 (show 1≤q by linarith [hq.1])
  let a':ℝ:= 1/1024; have hh:0<a':=by norm_num [a'];
  obtain ⟨t,ht,hu,hU⟩:=Jams.ball_on (q:=q) (s:=a') (r:=1) (by linarith [hq.1]) hh (by norm_num [a']) (by norm_num)
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= freakFare hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) θ1 hU hE
  let M:=ThroughLaunch.bountyV s T l
  obtain ⟨⟨P⟩,H⟩:= hK l le_rfl
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨V',H',Hp'⟩:=Tent.quotes V hh
  obtain ⟨Vx,hx,hV⟩:=Muse.header hG V' hh q
  obtain ⟨D,-⟩:= Bar.exists_above Vx 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK Vx (H'.trans hx) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,hU⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  obtain ⟨hA,hC,hM,hη,hW,hL,hU',hE,hR,hCσ,hPΩ,U₁,HΩ,hYe,hYv,hY₁,hYs⟩:=W
  have ht':= Hp' Vx hx
  obtain ⟨p,hh'⟩:= Tent.verses R ht' hR hE
  exact ⟨_,_,_,_,_,_,c,hCσ,hPΩ,hYs,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hU,q,t,a',a',p,⟨hL,hU',by norm_num [a', FullVolume.Amp.glint],hq, ht', hR,hB.symm ▸ hV Vx (DelayLe.refl _) D Y a ha,by norm_num [a', FullVolume.Amp.glint],hh',hG, Drifting.pay B.valid⟩,θ1,U₁,HΩ,hYe,hYv,hY₁⟩


end YM.PhysicalNext.Repeat.Legato
