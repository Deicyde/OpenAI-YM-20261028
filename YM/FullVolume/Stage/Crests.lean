import YM.FullVolume.Stage.Grand
import YM.FullVolume.Profiles

/-! Same arc Campaign.H. all campuses. -/
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
structure Campaign (X: Run G) where
    width :ℝ
    ζ : ℝ
    fee : ℝ
    pay : ℝ
    L : Roof.Lyrics X.kit fee fee
    gains : Muse.Plato L width pay pay ζ
    goes (N n:ℕ) : Competes L.tunes n N 0 (X.T.history N n)
lemma brink (h : G.Simple)(wl : ℝ)(hw:0<wl): ∃ (R:Run G), Nonempty (Campaign R) ∧ R.family.path.levels.clock.kernel.penalty=wl:=by
   obtain ⟨X,P,A,F,L,Q,b,hW,hH,ξ,v,t,a,D,Φ⟩ := factorG h hw
   obtain ⟨T,⟨Z⟩,hD⟩:= FullVolume.rodB F Φ
   choose t' ht using fun d:ℕ=> (A.B.a.fits.deep.eventually_ge_atTop (d+3)).exists
   obtain ⟨p,S,hm,hc,hF,hE⟩:= squad h b T Z.receipts t' ht
   exact ⟨⟨X,P,A,F,L,Q,b,_,hH,T,Z,t',ht,p,S,hm,hF,hE⟩,⟨ξ,t,v,a,D,Φ,hD⟩,hW⟩
variable {R:Run G} (T: Campaign R)
def Campaign.center (N p:ℕ):Contest N p T.L := ⟨_,T.goes N p,(real N p) ▸ interior_subset (centers R.alloy.B.a)⟩ where
 real N p : (R.T.history N p 0).beta=R.alloy.B.a.clock.bar:=R.makes.wilson.reaches .. -- name
end YM.PhysicalNext.Repeat.Legato
