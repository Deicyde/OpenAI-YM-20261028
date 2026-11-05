import YM.MergeProof.Portions
import YM.FullVolume.Dusk.Rupee
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}(H:C.Makes)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Mauve C W u ψ φ δ ζ r D){f:Extraction.Order}
set_option quotPrecheck false
variable {N p d:ℕ}
-- issue from afterL delay and permits. actual
variable (hG:G.Simple)
include H B h hG
variable (hF:Fridge C u ζ)
include hF
lemma onionsT (Z:Trial C) (hp:RawProtected C f Z d)(hZ:Stencilled f Z)(hz:∀ᶠ i in f.fuse,Continuous (Z i.1 i.2 0)) : vet C f d Z:=by
    obtain ⟨E,hE,HZ⟩:= persists H hG hF.full (roof_of_tabs B) hF.candle (hF.path _) (hF.smoke d _) (fun i hi=>(h.grows d i hi).le) hp hz; obtain ⟨v,hv,hV⟩:= served_dollarX H B h hE hZ HZ; exact ⟨v,hv,hV.closes H (by norm_num)⟩
theorem thymeX (x:C.label d)(k:ℕ)(hk:d ≤ k):vet C f k (visits C d x):= onionsT H B h hG hF _ (RawProtected.visits H hG x hk) (Stencilled.visits H x) (Eventually.of_forall fun i=> C.continuousO ..)
theorem loftyX (x:C.label d)(a:Axis):vet C f (d+1) (heighten C d x a):= onionsT H B h hG hF _ (RawProtected.heighten H hG x (hF.shifts f) a) (Stencilled.heighten H x a) (Eventually.of_forall fun i=> ((C.continuousO i.1 i.2 _ _ (0+step a)).sub (C.continuousO ..)).const_smul _)
end YM.MergeProof
#print axioms YM.MergeProof.onionsT
#print axioms YM.MergeProof.thymeX
#print axioms YM.MergeProof.loftyX
