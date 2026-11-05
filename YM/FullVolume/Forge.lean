import YM.MergeProof.Summit
import YM.MergeProof.Emanate
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
theorem dagger {β:ℝ} (h:0<β) : ∃ (M:Metals G)(P:Rolls M.p)(A:Alloy M P)(X:Factor A)(Y:ℕ→ℝ)(K:Bid.Worth)(b:Bandage X Y K),
    A.B.a.clock.kernel.penalty=β ∧ Unlatched b (fun _=>1) (fun T t S _ => let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; ∀ f:Extraction.Order, MergeProof.East.CompleteWeak Z f) := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G β h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= trident hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  let M:=ThroughLaunch.currency s T l
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
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,hU⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  exact ⟨_,_,_,_,_,_,c,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hU⟩

/-- Public ingredients can use ANY T,t,S,D from this same unlatched
purchase. Thus can enforce UV refinements before choosing them. -/
def Ahead {M : Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:ℕ→ℝ}{K:Bid.Worth}(b:Bandage X Y K) (Q:ℕ→ℕ):= Unlatched b Q (fun T t S _ =>
    let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; ∀ f:Extraction.Order, MergeProof.East.CompleteWeak Z f)

variable {M : Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:ℕ→ℝ}{K:Bid.Worth}{b:Bandage X Y K}{Q:ℕ→ℕ} {T:Bolt A}{t:ℕ→ℕ} {S:∀ d N p:ℕ,TransferData ((Labels.frames G).level d) (Issue.trail T) N p} {D:∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail T).rep N p (m+1)) ((Issue.trail T).rep N p m)}

set_option quotPrecheck false
local notation "Z" => Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S
lemma ahead (hx:Ahead b Q)(hy:Nest X T)(ht:∀ d,d+3 ≤ (Issue.trail T).levels.clock.J (t d))(hm:(Z).Makes)
    (hp:∀ N m p (h:m<N), Climbs X T N m p (D N p m h))(he:∀ d N p : ℕ, t d ≤ N→ Freight T hy N p d (S d N p) (t d) K (D N p)):
    Extraction.Wcmain Z ∧ Stock.Tabs A.B.a ∧ Scrim Z K (far A.B.a) (waybill A.B.a) (near A.B.a) (renal A.B.a) (fly A.B.a) (mutt A.B.a Q) D ∧
       Fridge Z (far A.B.a) (fly A.B.a) ∧ (∃ (V:∀ d, SectionData ((Z).labels.level d)) (W:Push.Mark.Weave G), ∃ U e,(∀ d:ℕ,Push.Mark.Portfolio (Z).params (V d) (W d)) ∧ Hearthside Z V W U e (fly A.B.a)) ∧
         (∀ S':Table (Z).book,∀ d, ∃ (X:Cells.Columns Z S' d) (Y:X.Trials), Market.Purchases Y) ∧ ∀ f:Extraction.Order,∃ (g:Extraction.Order)(S':Table (Z).book), Nonempty (Spec.Final Z (f.refine g) S'):=by
  obtain ⟨hT,hq,hU,hf,⟨V,W,U,e,H,hK⟩,hw,hαP,hh⟩ := hx _ hy t ht S D hm hp he
  obtain ⟨hc,hF,hQ,hS,hW,B',-,-,U',F',X',-,h'⟩:= hT.reception
  have hv: Ribbons.Created Z:= ⟨_,t,S,rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hS hU hq hv hF,hq, Ribbons.fugacious Z hG hU⟩
  refine ⟨hW,hq,hS,hf,⟨V,W,U,e,H,hK⟩,hw,fun f=> ?_⟩
  obtain ⟨g,A,L,R,z,T,E,h,hA,s,hN⟩:= h' f
  obtain ⟨M,I,hI,p⟩:= Acme.emanate (W:=E) hπ hG (grilled _ hF hS hq s.copies) (hh _) s hA.clean.ready hA.clean.tilt
  exact ⟨g,T,Acme.glistens hc hA.clean.ready hA.clean.tilt p⟩
end YM.PhysicalNext.Repeat.Legato
