import YM.MergeProof.Jubilee
import YM.MergeProof.Orchestra
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Commission
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat 
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}{R:Rep G n}{b:Site n}{t:ℝ}
lemma inkL (P : F.Coeff → Coefficient F n) (s:F.Coeff→ℝ)(h:Ledger F n P)(he:∀v,(P v).remBound b R t (s v)) : IsLinearMap ℂ fun i=>profile R.activities (P i).forced :=by
   constructor
   · intro i j; rw [h.f.map_add]; funext p U; change ∑' s:{i//barcode R.activities i=p}, ((P i).forced s.val U+(P j).forced s.val U) =_+_; exact Summable.tsum_add (((rem_dominated (he i)).summable U).comp_injective Subtype.val_injective) (((rem_dominated (he j)).summable U).comp_injective Subtype.val_injective)
   intro c j; rw [h.f.map_smul]; exact profile_scale ..
end YM.MergeProof
