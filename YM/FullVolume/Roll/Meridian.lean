import YM.FullVolume.Roll.Ariva
import YM.FullVolume.Stage.Coup
/-! Price Calendar + Same.K.Data, largest fixed R from scratch. Next goal Sci.Day with same Campaign. -/
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
abbrev Locrian (R:Run G): Prop := Stationary.Artes.Cadre R.alloy.post R.alloy.B.kin ∧ Next.Free.Amplify R.alloy.B.M
lemma meridian (h:G.Simple)(wl:ℝ)(hw:0<wl):∃ R: Run G, Nonempty (Campaign R)∧ Locrian R ∧ Jams.Wild R.kit.shape R.alloy.delay ∧ R.family.path.levels.clock.kernel.penalty=wl:=by
   obtain ⟨X,P,A,F,L,Q,b,hY,hC,hYs,hW,hH,ξ,v,t,a,D,Φ⟩ := factorGK h hw
   obtain ⟨T,⟨Z⟩,hD⟩:= FullVolume.rodB F Φ
   choose t' ht using fun d:ℕ=> (A.B.a.fits.deep.eventually_ge_atTop (d+3)).exists
   obtain ⟨p,S,hm,hc,hF,hE⟩:= squad h b T Z.receipts t' ht
   exact ⟨⟨X,P,A,F,L,Q,b,_,hH,T,Z,t',ht,p,S,hm,hF,hE⟩,⟨ξ,t,v,a,D,Φ,hD⟩,⟨hY,hC⟩,hYs,hW⟩
end YM.PhysicalNext.Repeat.Legato
#print axioms YM.PhysicalNext.Repeat.Legato.meridian
