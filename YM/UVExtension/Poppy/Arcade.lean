import YM.UVExtension.Poppy.Glade
import YM.UVExtension.Upland.Plinth
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
open UVExtension UVExtension.Harvest
/-! price from same schedule, Barn pins together all projections and histories,
    Transfers peak & radiances, see e.g. Poppy.Fountain. Real offset laws
    on `.yard` are the marked families actually tested. At the center exact
    CLOSED acquisitions via UV-stress.Weak L output. -/
def Getup (C:Family G) : Prop:= ∃ (M:Metals G)(P:Rolls M.p)(A:Alloy M P)(R: Roost.Factor A)(T:Bolt A)(S:Spire.Uses R hG), Upland.Arc R S T ∧ ∃ (t:ℕ→ℕ), ∃ K Y,∃ (b:Bandage R K Y)(U:Mast.Cellar S t b),C=Mast.Cellar.yard (Mast.roseA S) U∧ Barn S b (fun _=>1) U ∧ (∃ hv:Upland.Arc R S T, let Q:=Mast.roseA S; Chateau b (fun _=>1) (Mast.centerB S hv) t (Mast.Cellar.gate Q U) (Orchard.roof S Q)) ∧ Velour (Mast.Cellar.yard (Mast.roseA S) U) (renal A.B.a) (mutt A.B.a (fun _=>1)) (Orchard.roof S (Mast.roseA S))
include hG
theorem uv_whole {b:ℝ} (h:0<b) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    Getup hG C ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= uv_glades hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  let M:=UVExtension.Case.provider s T l
  obtain ⟨⟨P⟩,H⟩:= hK l le_rfl
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,T,t,S,Hx,Hk,hT,hq,hu,hD,hE⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let V:= Mast.centerB S Hx; let W:=Mast.cellar S c Hx t Hk; let S':= Mast.Cellar.gate (Mast.roseA S) W
  let Z:= Family.mk (Issue.trail V) (hol G) (Labels.frames G) (localSection G) t S'
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S',rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu hq hv hF,hq, Ribbons.fugacious Z hG hu⟩
  exact ⟨_,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hc,hF,hW,⟨M,P, Alloy.mk F θ _ _ Y X B,R,T,S,Hx,t,_,_,c,W,rfl,hD,⟨Hx,hT⟩,hu⟩, hπ,fun f hf=>⟨grilled Z hF hU hq hf,hE f⟩,fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩⟩
end YM.PhysicalNext.Repeat.Legato
