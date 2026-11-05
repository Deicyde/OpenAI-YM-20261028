import YM.UVExtension.Oasis.Hall
import YM.RemainderComparison.Chron.Pole
import YM.Pert.Spatial.CrowdPay

/-! Mirror baseline wrapper calls in YM/UVExtension/Oasis/Hall since extra purchase must pass unchanged through SAME constructors. -/
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

open YM.RemainderComparison
-- Keep the same inward traveller; all exterior consumers can call
-- Fayette with this W. Full-basis UV opacity afterwards remains.
-- Startup order `hg` not overwritten.
namespace Stagehands
structure Origin (S: Chron.Contemple G) (C:Family G) : Prop where
   provenance : ∃ (M:Metals G) (D:Rolls M.p)(A:Alloy M D)(R:Factor A),∃ (k:ℕ→ℝ) (w:Bid.Worth) (B:Bandage R k w) (p:ℕ→ℕ) (H:UVExtension.Spire.Uses R hG)
           (T:Org.Bolt A) (Z: UVExtension.Upland.Arc R H T) (hV: UVExtension.Mast.Lisle p A.B.a), C= UVExtension.Mast.Cellar.yard (UVExtension.Mast.roseA H) (UVExtension.Mast.cellar H B Z p hV) ∧ News R S
   subscriptions : YM.MergeProof.Ribbons.Plenty C
end Stagehands
namespace RealClock
/- Merge.Proof.Pert.Deeper's explicit beta-entry purchase recipe for K kinetic
  works also with these ANY upper launch budgets and while retaining UV data. -/
variable {s:Sheet G} (D:Rolls s){θ:Protection D}{H:Delays θ}{K : Bar H}

def gate (i:ℕ):ℝ:=(((s.profile i).supportExponent+2)*((D.L i).val:ℝ)^4)^2
variable (hG:G.Simple)
include hG
lemma plenty {C:Family G}{a:Levels G}{P:Wait K}(hp:Paid P a)(he:∀ i, RealClock.gate D i ≤ H.betaEntry i)(hx:C.path.levels=a): Ribbons.Plenty C:=by
   intro i; let j := a.clock.J ((i-1)+1)
   have hj : a.clock.J i = j := by
      cases i with
      | zero=> unfold j; rw [hp.firstZero,show 0-1+1=1 by norm_num,hp.firstOne]
      | succ i=> rfl
   have hm : (a.budget i).supportExponent= (s.profile j).supportExponent:= by
      change (a.clock.stage (a.clock.J i)).supportExponent=_; rw [hj,hp.stage]
   have hu : a.clock.hatBeta (i-1) ≤ a.clock.hatBeta i:=by
      unfold Calendar.hatBeta; gcongr
      · exact (Gauge.slopeConstant_pos hG).le
      cases i with
      | zero=>rfl
      | succ i => change a.S.scale i ≤ a.S.scale (i+1); rw [a.S.scale_succ]; exact (by linarith [Real.log_nonneg (Nat.one_le_cast.mpr (a.S.block i).pos)])
   have hg:= (he j).trans ((hp.pays (i-1)).trans hu); unfold RealClock.gate at hg
   have hh : ((s.profile j).supportExponent+2)*((D.L j).val:ℝ)^4 ≤ Real.sqrt (a.clock.hatBeta i) := Real.le_sqrt_of_sq_le hg
   rw [hx]; unfold Ribbons.spacingFactor
   rw [show a.S=(a.clock.schedule) from rfl,← a.fits.sameFactor (i-1)]
   change ((a.budget i).supportExponent+1)*(a.clock.factor j |>.val:ℝ)^4 ≤ _
   refine le_trans ?_ hh; rw [hm,hp.lengths]; gcongr; linarith
end RealClock
include hG
theorem posted_flowered (Ω: Chron.Contemple G) {b:ℝ} (h:0<b) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    Stagehands.Origin hG Ω C ∧ UVExtension.Oasis.Floral (hG:=hG) C ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= posted_wishes hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) Ω hE
  let M:=UVExtension.Case.provider s T l
  obtain ⟨⟨P⟩,H⟩:= hK l le_rfl
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun i=>RealClock.gate P i,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,hΩ,c,T,t,S,Hx,Hk,hT,hq,hu,hD,h_lease,h_rate,⟨hh',hH,h_Φ,h_sh⟩,hE⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let V:= Mast.centerB S Hx; let W:=Mast.cellar S c Hx t Hk; let S':= Mast.Cellar.gate (Mast.roseA S) W
  let Z:= Family.mk (Issue.trail V) (hol G) (Labels.frames G) (localSection G) t S'
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S',rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu hq hv hF,hq, Ribbons.fugacious Z hG hu⟩
  exact ⟨_,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hc,hF,hW,(show Stagehands.Origin hG Ω Z from ⟨⟨M,P,_,R,_,_,c,t,S,T,Hx,Hk,rfl,hΩ⟩,RealClock.plenty hG P ha h₁.beta hB⟩),Oasis.survives W Hx hD hQ hh' hH (hB.symm ▸ h_Φ) h_sh h_lease h_rate hT hu, hπ,fun f hf=>⟨grilled Z hF hU hq hf,hE f⟩,fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩⟩
end YM.PhysicalNext.Repeat.Legato
