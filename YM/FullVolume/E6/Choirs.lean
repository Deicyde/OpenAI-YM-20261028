import YM.FullVolume.E6.Params
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open FullVolume.Shadow
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{j:ℕ}{x:E}{Λ:Era G S}{K H:ℕ→ Epoch Λ}{U V:ℕ→ E→ Config G c}
lemma keeping {R T:ℕ→ E→ Pay G}{A B:ℕ→ E→ G.Color}(h:Frill φ j x R T)(he:Frill φ j x A B): Frill φ j x (fun n y=> R n y (A n y)) (fun n y=> T n y (B n y)):= h.combines he (contDiff_fst.clm_apply contDiff_snd)
lemma bearing {R T:ℕ→ E→ Pay G}{A B:ℕ→ E→ G.Color}(h:Frill φ j x R T)(he:Frill φ j x A B): Frill φ j x (fun n y=> (R n y).adjoint (A n y)) (fun n y=> (T n y).adjoint (B n y)):=by
    let L:Pay G ≃ₗᵢ[ℝ] Pay G:= ContinuousLinearMap.adjoint
    exact keeping (h.via L.toContinuousLinearEquiv.contDiff) he
namespace Finish
variable (h:Finish φ K H) (hx:Quincy φ j x U V)
include h hx
lemma overC (p k): Frill φ j x (fun n y=> (K n).tubes.Xn k (U n y) p) (fun n y=> (H n).tubes.Xn k (V n y) p):= h.down.stain _ S.patch.L.property hx ..
omit hx in
lemma overF {U V:ℕ→ E→ Config G f}(hx: Quincy φ j x U V)(p k): Frill φ j x (fun n y=> (K n).tubes.Xf k (U n y) p) (fun n y=> (H n).tubes.Xf k (V n y) p):= h.up.stain _ (by norm_num : 0<1) hx ..
open Scroll
lemma higherF (p k): Frill φ j x (fun n y=> canopyF (K n).tubes k (U n y) p) (fun n y=> canopyF (H n).tubes k (V n y) p):= Frill.buds Finset.univ fun i _=> keeping (h.taps hx ..) (h.overC hx i _)
lemma higherI (p k): Frill φ j x (fun n y=> canopyI (K n).tubes k (U n y) p) (fun n y=> canopyI (H n).tubes k (V n y) p):= Frill.buds Finset.univ fun i _=> keeping (h.toes hx ..) (h.overC hx i _)
lemma higherN (p k): Frill φ j x (fun n y=> canopyN (K n).tubes k (U n y) p) (fun n y=> canopyN (H n).tubes k (V n y) p):= Frill.buds Finset.univ fun i _=> keeping (h.boots hx ..) (h.overC hx i _)
lemma highV (k p) : Frill φ j x (fun n y=> visual (K n).tubes k (U n y) p) (fun n y=> visual (H n).tubes k (V n y) p):=by
    rcases p with i|i; · exact h.higherF hx i k
    exact h.higherI hx i k
variable {u v:ℕ→ E→ Directions G f}(hv:Frill φ j x u v)
omit hx in
include hv in
lemma barstool (k p): Frill φ j x (fun n y=> barField (K n).tubes k (u n y) p) (fun n y=> barField (H n).tubes k (v n y) p):=by
    rcases p with ⟨p,j'|j'⟩ | p
    · have he := Frill.still (x:=x) (n:=j) (φ:=φ) (Real.sqrt Λ.high.direct); refine he.fee (hv.via (Q:=fun y=> Work.F03.faceCurl p (toLog y)) ?_); simp_rw [curl_eq]; fun_prop
    · obtain ⟨A,hA⟩:= tagSet k
      have hs (T:Epoch Λ) (z:Directions G f): barField T.tubes k z (.inl (p,true))=∑ i∈A,(if (Beacon.flag i).length≤k then T.up.fare p.2 i • Work.F03.faceCurl (Work.F03.slotFace (Beacon.flag i) p.1) (toLog z) else 0):= tsum_eq_sum fun i hi=> if_neg fun h=> hi (hA i h)
      simp_rw [hs]; apply Frill.buds A; intro i hi
      split
      · refine (Frill.bare (h.up.1 p.2 i)).fee (hv.via (Q:=fun y=> Work.F03.faceCurl (Work.F03.slotFace (Beacon.flag i) p.1) (toLog y)) ?_); simp_rw [curl_eq]; fun_prop
      exact Frill.still _
    refine hv.via (Q:=fun y=> Next.Fluctuations.zLin S (toLog y) 0 p) ?_
    simp_rw [zLin_eq, toLog]; fun_prop
include hv
open Channel
lemma frameZ (k s p) : Frill φ j x (fun n y=> orientedRow (K n).tubes k s p (U n y) (u n y)) (fun n y=> orientedRow (H n).tubes k s p (V n y) (v n y)):=by
    have hz i: Frill φ j x (fun n y=> displacement s (u n y) (replica S.ratio (U n y)) i) (fun n y=> displacement s (v n y) (replica S.ratio (V n y)) i):=by
        dsimp only [displacement]; split
        · exact (Strand.nuptX ((hx.books S _).inverse) (hv.cross _)).neg
        exact hv.cross _
    let F n (y:E) := spinRow S (carrier (focus S p) (pull s 0 (U n y))) (displacement s (u n y) (replica S.ratio (U n y)))
    let G' n (y:E) := spinRow S (carrier (focus S p) (pull s 0 (V n y))) (displacement s (v n y) (replica S.ratio (V n y)))
    exact h.barstool (show Frill φ j x F G' from Frill.stocks fun i=> (((hx.turn s).weft _ _).nuptX (hz i))) k p
end Finish
end YM.ConnectedActivityE6.Lim
