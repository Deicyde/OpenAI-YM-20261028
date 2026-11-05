import YM.TraceExtension.Prom.Zoom.Mast
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n k N p l:ℕ} {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (B:Binding C)(H:C.Makes)(O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "S'"=> Cells.standard C
variable (F : Extraction.Order)(a : (Cells.standard C).Hierarchy)
variable {S: Table C.book} (P:F.Ordered C S) (hs:S.Hierarchy)(he:F.PointLimits C S)
-- no proof of Exact topology of phase here. for this S. record actual ranks. NOTE not Stable.rise and not claiming meter
structure StarPath (F : Extraction.Order)(a : (Cells.standard C).Hierarchy)(X: Scaling S) (h : S.Hierarchy)(𝓛: Ultrafilter (ℕ×ℕ)): Prop where
   approach : Approaches (path X) (isoPanel X)
   units : ∀ d,∀ᶠ i in atTop, Coherent a.spin h.spin d (X.U i d) ∧ X.U i d ((Cells.standard C).unit d)=S.unit d
   money : ∃ V:∀ d,Vane C d,Tendsto (fun i=> (V i).k) atTop atTop ∧ (∀ i,(V i).checked F a i ∧ (V i).wheel.r=X.r i)∧
       ∀ d,∀ᶠ k in atTop,∀ i:Fin (k+1),i.val=d →∃ Y:Next.UVStress.Lifts C k,Tendsto (V k).wheel.atCut (𝓛:Filter _) (𝓝 Y)∧∀ z,X.U k i z=S.project i (Y i z)
include he P
theorem pays_sky (hG:G.Simple)(hX: Scrim C W u ψ φ δ (fly C.path.levels) r L) {z:ℕ →ℝ}
   (hZ:∀ i j, i≤j→ generator G i≤z j) (h : ∀ d,FiresSky B H O J d (z d))(hD:DimAbove S) (𝓛:Ultrafilter (ℕ×ℕ))(hℓ:(𝓛:Filter _)≤ F.fuse) (s:ℕ→ℝ)(hS:Tendsto s atTop (𝓝 0))(hp:∀ i,0<s i): ∃ f:ℕ→ℕ,StrictMono f ∧ ∃ X:Scaling S,X.r=s ∘ f ∧ StarPath F a X hs 𝓛:= by
   obtain ⟨v,V,hF,h',hκ,hV⟩:= wakesSky B H O J F a P hs.smooth he hG hX hZ h s hS hp
   let X:Zoom:=⟨s∘v,(fun _=> hp _),h', hS.comp hF.tendsto_atTop⟩
   obtain ⟨Y,hY,hA,hu,hZ⟩:= dockedSky hs P a H X V (fun i=> (hV i).1) (fun i=> (hV i).2) 𝓛 hℓ hD
   have hr:Y.r=s ∘ v:= congr_arg Zoom.r hY
   exact ⟨v,hF,Y,hr,⟨hA,hu,V,hκ,fun i=> ⟨(hV i).1,(hV i).2.trans (congr_fun hr i).symm⟩, hZ⟩⟩
#print axioms submits
#print axioms embalms
#print axioms pays_sky
end YM.MergeProof.East
