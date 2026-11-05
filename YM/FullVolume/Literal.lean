import YM.FullVolume.Discrete
import YM.FullVolume.Cross
import YM.FullVolume.Moneys

/-! Unconditional marks on SAME story book. Uniform in period for the entire
unrefined mesh on finite d,h families. Use centered physical sides after
fixing any scale within the estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Run
open FullVolume
open Function Filter Set Lattice RG Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract MergeProof Extraction Extraction.Lease Cells Push.RelayDifference
variable (R:Run G) (hG:G.Simple) (d:ℕ)
include hG
lemma financed {w : Bid.Rowe R.family d} {C:ℝ} (hw : ∀ᶠ i in FullVolume.mesh, ‖w i‖ ≤ C) (l : List Axis) : Funded (FullVolume.hops (Bid.upper R.family w) l):=by
  let A:= R.family; set F := FullVolume.hops (Bid.upper R.family w) l
  obtain ⟨⟨hW,hT,hC,hR,⟨V,W,U,e,H,h⟩,hd⟩,hp⟩:= again R hG
  have hx : Tucked F (d+l.length):=
    (Tucked.up R.makes hG w (Coin.from_bound R.makes hw)).hops (borrowed (W:=fun i=> Push.RelayDifference.jump (A.path.levels.budget i)) (hR.shifts Order.full)) l
  obtain ⟨x,hx,he⟩:= prepared_rows (C:=A) R.makes hT hC hG hR (hops_solid (F:=Bid.upper A w) (Eventually.of_forall fun i x=> A.continuousO ..) l|>.mono fun i hi=> hi 0) ((Stencil.visits R.makes w).hops l) hx
  -- use the common field detector, not any bootstrapped tables
  obtain ⟨g,S',hS⟩:= hp Order.full
  obtain ⟨X,T,hy⟩:= hd S' (d+l.length)
  exact improved T R.makes hT hW (took T R.makes hy) V W H e h (Funded.primaries R.makes hW w hw) (fun N p x=> R.family.continuousO ..) x hx _ he (flown (by norm_num))
end YM.PhysicalNext.Repeat.Legato.Run
namespace YM.FullVolume
open Function Set Filter MeasureTheory Lattice Wilson Cells Extraction Extraction.Lease Gaps Difference
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}


lemma funding (C:Family G)(hM:C.Makes)(hq:∀ d:ℕ,∀ x:C.label d,∀ l:List Axis,Funded (FullVolume.hops (Bid.upper C (fun _=>x)) l)) : FixedBounds C:= by
   constructor; intro n v l r hr
   let f (j:Fin n):Trial C:= Bid.visits C (v j).1 (v j).2
   have hw (l):∃ g:Fin n→Trial C,(∀ j,∃ l, g j=hops (f j) l)∧ ∀ᶠ i in mesh,expose g i=gKernel C v l i.1 i.2:=by
     induction l with
     | nil => exact ⟨f,fun j=>⟨[],rfl⟩,Eventually.of_forall fun _=>rfl⟩
     | cons a l ih=>
       obtain ⟨g,hg,hv⟩:=ih; choose b H using hg
       have ht(j:Fin n):∀ᶠ i in mesh,∀ o, Continuous (g j i.1 i.2 o):=by rw [H j]; exact hops_solid (Eventually.of_forall fun i o=> C.continuousO ..) _
       refine ⟨update g a.1 (farther (g a.1) a.2), fun j=>?_,((eventually_all.mpr ht).and hv).mono fun i hi=> ?_⟩
       · by_cases he: j=a.1
         · subst j; exact ⟨a.2::b _,by rw [Function.update_self, H]; rfl⟩
         exact ⟨b _,(Function.update_of_ne he ..).trans (H _)⟩
       rw [actuate g i hi.1,hi.2]; rfl
   obtain ⟨g,hg,hv⟩:= hw l
   have he (i) : Funded (g i):=by
       obtain ⟨b,hp⟩:=hg i; rw [hp]; exact hq _ (v i).2 b
   obtain ⟨B,hB⟩:= FullVolume.financed (C:=C) hM g he hr
   · refine ⟨max 0 B,le_max_left ..,(late (P:=fun i=> ∀ x:Positions n,spaceout C r i (wrap (C.side i.1 i.2) ∘ x) → ‖gKernel C v l i.1 i.2 x‖≤ max 0 B)).mp ?_⟩
     filter_upwards [hB,hv] with i hi ht x hx; rw [←ht]; exact (hi _ hx).trans (le_max_right ..)
theorem genuine (R:Run G)(h:G.Simple): FixedBounds R.family:= funding R.family R.makes fun d x _=> R.financed (C:=‖x‖) h d (w:=fun _=>x) (Eventually.of_forall fun _=> le_rfl) _
end YM.FullVolume
