import YM.Pert.Spatial.CrowdPay
import YM.Pert.Spatial.Prices

/-! Keep additional ledger from *same* `himalayas` at one common Wilson construction.
No changes to target definitions and no inference from a theorem that doesn't preserve the witnesses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pert
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
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
theorem deeper {b:ℝ} (h:0<b) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Ribbons.Plenty C ∧ Ribbons.Materials C ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= himalayas hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  let M:=ThroughLaunch.currency s T l
  obtain ⟨⟨P⟩,H⟩:= hK l le_rfl
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun i=> (((M.p.profile i).supportExponent+2)*((P.L i).val:ℝ)^4)^2,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,T,t,S,D',hT,hq,hu⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S
  change Velour Z (renal B.a) _ D' ∧ (∀ f:Extraction.Order,MergeProof.East.CompleteWeak Z f) at hu
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S,rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu.1 hq hv hF,hq, Ribbons.fugacious Z hG hu.1⟩ -- fix argument order
  exact ⟨_,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,by
    change Ribbons.Plenty Z
    have haZ : Z.path.levels = a := by change B.a=a; exact hB 
    unfold Ribbons.Plenty Ribbons.spacingFactor; intro i;rw [haZ]; rw [show a.S=(a.clock.schedule) from rfl,← a.fits.sameFactor (i-1)]
    let j := a.clock.J ((i-1)+1)
    have h0 : i = (i-1)+1 ∨ a.clock.J i = a.clock.J ((i-1)+1) := by
       cases i with
       | zero => rw [ha.firstZero, show 0-1+1=1 by norm_num, ha.firstOne]; exact Or.inr rfl
       | succ i => exact Or.inl rfl
    have hj : a.clock.J i = j := by rcases h0 with h|h; exact congr_arg _ h; exact h
    have he : ((a.budget i).supportExponent)= (M.p.profile j).supportExponent := congr_arg (fun z=> (z j).supportExponent) ha.stage |> fun h=>by
       change (a.clock.stage (a.clock.J i)).supportExponent=_; rw [hj,h]
    have hpay : a.clock.hatBeta (i-1) ≤ a.clock.hatBeta i := by
       unfold YM.RG.Calendar.hatBeta; gcongr
       · exact (Gauge.slopeConstant_pos hG).le
       cases i with
       | zero=>rfl
       | succ i =>
         change a.S.scale i ≤ a.S.scale (i+1); rw [a.S.scale_succ]; exact (by linarith [Real.log_nonneg (Nat.one_le_cast.mpr (a.S.block i).pos)])
    have hLow : (((M.p.profile j).supportExponent+2)*((P.L j).val:ℝ)^4)^2 ≤ a.clock.hatBeta i := le_trans (h₁.beta j) ((ha.pays (i-1)).trans hpay)
    have hh : ((M.p.profile j).supportExponent+2)*((P.L j).val:ℝ)^4 ≤ Real.sqrt (a.clock.hatBeta i) := by nlinarith only [hLow,Real.sq_sqrt (zero_lt_one.trans (a.fits.delayed i)).le,Real.sqrt_nonneg (a.clock.hatBeta i)]
    change ((a.budget i).supportExponent+1)*(a.clock.factor j |>.val:ℝ)^4 ≤ _
    refine le_trans ?_ hh; rw [he,ha.lengths]; gcongr; linarith,⟨hG,hF,hv,hq,_,D',_,_,_,hu.1,hU⟩,hc,hF,hW,hπ,fun f hf=>⟨grilled Z hF hU hq hf,hu.2 f⟩,fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩⟩
end YM.Pert
