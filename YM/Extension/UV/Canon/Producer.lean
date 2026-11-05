import YM.Extension.UV.Canon.Finish
import YM.Extension.UV.Build
noncomputable section
set_option autoImplicit false
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
open YM.MergeProof MergeProof.Accent Extension.UV

variable (hG:G.Simple)

def AttachedStart (X:UVBuild G) : Prop := Archive X.tower ∧ ∀ N p,X.engine.history N p N=Startup.canonical X.tower.kin N p (X.engine.history N p N).beta
include hG
theorem uv_canonical_delivery {b:ℝ} (h:0<b) : ∃ X:UVBuild G, X.prices.B.a.clock.kernel.penalty=b ∧ X.Shared ∧ Linear.SizeFloor b X.tower.a ∧ Secure X ∧ AttachedStart X := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= himalayasV hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  let F := fun j=> max (l j) ⌈Linear.Dcost b j⌉₊
  have hLF : l ≤ F := fun j=> le_max_left ..
  let M:=ThroughLaunch.currency s T F
  obtain ⟨⟨P⟩,H⟩:= hK F hLF

  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  let H₂ := H P
  obtain ⟨w,h⟩:= H₂
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  let V' : Delays θ := { V with betaEntry:=fun i=> max (max (V.betaEntry i) ((waitAbove M.p).choose i)) (demand G P i) }
  have hV : DelayLe V V' := ⟨fun _=> (le_max_left ..).trans (le_max_left ..),le_rfl,le_rfl,le_rfl⟩
  obtain ⟨D,hD⟩:= Bar.exists_above V' ((sum_cap_target G hG).choose); let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V' hV D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,T,t,S,D',hT,hArc,hT',hq,hu⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S
  change Velour Z (renal B.a) _ D' ∧ (∀ f:Extraction.Order,MergeProof.East.CompleteWeak Z f) at hu
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S,rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu.1 hq hv hF,hq, Ribbons.fugacious Z hG hu.1⟩ -- fix argument order
  let W : UVBuild G:= ⟨M,P,Alloy.mk F θ V' D Y X B,R,_,_,c,T,fun _=>1,t,S,D'⟩
  have hsFloor : Linear.SizeFloor b W.tower.a := @blockFloor _ M P W.prices b (fun j=> max (l j) ⌈Linear.Dcost b j⌉₊) rfl (fun j=> (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right (l j) ⌈Linear.Dcost b j⌉₊)))
  have hZ : W.C = Z:= rfl
  have h₉ : W.Shared := by
    exact ⟨hT,hF,hc,hW,hπ,fun f hf=>⟨grilled Z hF hU hq hf,hu.2 f⟩,fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩⟩
  refine ⟨W,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,h₉,hsFloor,W.reserved hG h₉ (numerical_admission hG W.tower.valid (fun i=>le_max_right ..) hD W.engine.sticks W.engine.choice) (fun i=> (le_max_right ..).trans (le_max_left ..)),hArc,hT'⟩ -- uses defeq

end YM.PhysicalNext.Repeat.Legato
