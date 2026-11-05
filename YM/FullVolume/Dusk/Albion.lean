import YM.FullVolume.Fire
import YM.FullVolume.Dusk.Realt
import YM.FullVolume.Dusk.Peel
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}(H:C.Makes)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Mauve C W u ψ φ δ ζ r D)(hF:Fridge C u ζ){f:Extraction.Order} {N p d:ℕ} (V:∀ d:ℕ,SectionData (C.labels.level d))(R:Mark.Weave G)(hV:∀ d, Mark.Portfolio C.params (V d) (R d))(hG:G.Simple)
set_option quotPrecheck false
include h hV H hG hF B
theorem fireguard (hb:∀ d:ℕ,∃ a: ℕ→ℝ,Braze (C:=C) (V d) a): ∃ P b, Hearthside C V R P b ζ:=by
    choose P hp using hb; choose E Y U hY using fun d=> solarQ H B h hF (V d) (hV d).valid hG (hp d)
    choose M hm hM using fun d:ℕ=> Mark.potage (C.labels.level d); choose F hK hQ hs using fun d:ℕ=> fun i:Cutoffs => hM d (catalog C R d i.1 i.2 (Y d i.1 i.2)); let b:Presentation C:=⟨F,fun d i=> (hK d i).stable⟩
    refine ⟨fun d i=> Y d i.1 i.2,b,⟨fun f=> ?_,fun d=>?_,fun d N p=>hK d (N,p), fun f d=>?_⟩,fun d=> ⟨E d,U d,hY d⟩,fun d=> ⟨_,hQ d⟩⟩
    · exact ⟨fun d p=>⟨_,(hm d).le,Eventually.of_forall fun j=> hQ d (f.mesh j,p)⟩, fun d=>⟨_,(hm d).le, Eventually.of_forall fun p=> Eventually.of_forall fun j=> hQ d (f.mesh j,f.per p)⟩⟩
    · filter_upwards [catalog_symm H (V d) R (hV d) _ (hY d)] with i hi p; obtain ⟨hv,hh⟩:=hi p; refine ⟨hv,hh,hs d (i,p) ?_⟩; let L:= bindP C R d i p (Y d i p); constructor
      · intro s x h; obtain ⟨w,hw,hW⟩:=h; subst x; exact ⟨_,Mark.turn_ideal s hw,hh w s⟩
      intro x hx; obtain ⟨w,hw,hW⟩:=hx; subst x; exact ⟨_,Mark.conjugate_ideal hw,hv w⟩
    refine ⟨fun x hx hv=> marshal H B (V d) R (hV _) _ (hY d) _ hv (fun j=> ((hK d j).ker) ▸ (show x j∈LinearMap.ker (F d j).toLinearMap from LinearMap.mem_ker.mpr (hx j))),fun w hw x=> thymeX H B h hG hF x d hw,fun x a=> loftyX H B h hG hF x a⟩
end YM.MergeProof
#print axioms YM.MergeProof.fireguard
