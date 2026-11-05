import YM.FullVolume.E6.Loom
import YM.FullVolume.E6.Rings
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
open FullVolume.Shadow FullVolume.Shadow.Frill
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ:Filter ℕ}{j:ℕ}{x:E}{X Y R Q :ℕ→ E→ G.El}
-- pair form needed to combine ops with V arguments but often X=Y
abbrev Strand (φ:Filter ℕ)(j:ℕ)(x:E)(X Y:ℕ→ E→ G.El):= Frill φ j x (fun n y=> G.mat (X n y)) (fun n y=> G.mat (Y n y))
namespace Strand
lemma glowing (h:Strand φ j x X Y)(he:Strand φ j x R Q): Strand φ j x (fun n y=> X n y*R n y) (fun n y=> Y n y*Q n y):=by simp only [Strand,Gauge.mat_mul]; exact h.combines he contDiff_mul
lemma frozen (a:G.El): Strand φ j x (fun _ _=>a) (fun _ _=>a):= Frill.still _
lemma inverse (h:Strand φ j x X Y): Strand φ j x (fun i y=>(X i y)⁻¹) (fun i y=> (Y i y)⁻¹) :=by simp only [Strand,Gauge.mat_inv]; exact h.via ((starL' ℝ (A:=G.Mat)).toContinuousLinearMap.contDiff)
private def nudge (G:Gauge)(M:G.Mat): Pay G:= G.projectColor.toContinuousLinearMap.comp ((ContinuousLinearMap.mulLeftRight ℝ G.Mat M (star M)).comp (G.colorMat.toContinuousLinearMap))
private lemma nudgeE (G:Gauge)(u:G.El) : nudge G (G.mat u)=(G.adjoint u).toContinuousLinearMap:=by ext1 x; rfl
lemma nupt (h:Strand φ j x X Y):Frill φ j x (fun i y=> (G.adjoint (X i y)).toContinuousLinearMap) (fun i y=>(G.adjoint (Y i y)).toContinuousLinearMap):=by
    have hd: ContDiff ℝ (↑j) (fun M:G.Mat=> ContinuousLinearMap.mulLeftRight ℝ G.Mat M (star M)):= ((ContinuousLinearMap.mulLeftRight ℝ G.Mat).contDiff).clm_apply ((starL' ℝ (A:=G.Mat)).toContinuousLinearMap.contDiff)
    have hc : ContDiff ℝ j (fun M:G.Mat=> ((ContinuousLinearMap.mulLeftRight ℝ G.Mat M (star M)).comp G.colorMat.toContinuousLinearMap)):= hd.clm_comp contDiff_const
    have he : ContDiff ℝ j (nudge G):=by unfold nudge; exact contDiff_const.clm_comp hc
    simpa only [nudgeE] using h.via he
lemma nuptX {u v:ℕ→ E→G.Color}(h:Strand φ j x X Y)(he:Frill φ j x u v): Frill φ j x (fun i y=> G.adjoint (X i y) (u i y)) (fun i y=> G.adjoint (Y i y) (v i y)):= h.nupt.combines he (f:=fun S Y=> _root_.id (S Y)) (contDiff_fst.clm_apply contDiff_snd)
lemma songs (h:Strand φ j x X Y): Frill φ j x (fun i y=> G.curvature (X i y)) (fun i y=> G.curvature (Y i y)):=by
   simp only [Gauge.curvature,Gauge.mat_inv]; exact h.via ((G.projectColor.toContinuousLinearMap.contDiff).comp ((contDiff_id.sub ((starL' ℝ (A:=G.Mat)).toContinuousLinearMap.contDiff)).const_smul (1/2:ℝ)))
attribute [local instance] Gauge.frobInner

lemma chordwise (h:Strand φ j x X Y): Frill φ j x (fun i y=> G.chord (X i y)^2) (fun i y=> G.chord (Y i y)^2):=by
    simp_rw [Gauge.chord,div_pow]; exact h.via (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _)
lemma flawing (h:Strand φ j x X Y): Frill φ j x (fun i y=> flaw (X i y)) (fun i y=> flaw (Y i y)):=by
    refine (h.chordwise.sub (h.songs.via (contDiff_norm_sq ℝ))).via (Q:=fun s:ℝ=> s/2) ?_
    exact contDiff_id.div_const _
lemma banners (μ:Ultrafilter ℕ) (p:ℕ→ G.El): Strand μ j x (fun i _=> p i) (fun i _=> p i):= Frill.bare ((FullVolume.Shadow.sails isCompact_univ (show ∀ᶠ i in (μ:Filter ℕ), p i∈Set.univ from Eventually.of_forall fun _=>trivial)).bin (fun _ _=> G.continuous_mat.continuousAt))
end Strand
abbrev Quincy {A:Type} (φ:Filter ℕ)(j:ℕ)(x:E)(U V:ℕ→E→ Links A G.El):=∀ i,Strand φ j x (fun n y=> U n y i) (fun n y=>V n y i)
namespace Quincy
section sturdy
variable {A:Type}[AddCommGroup A][One A]{X Y:ℕ→ E→ Links A G.El}
lemma shoe (h:Quincy φ j x X Y)(p : Four A)(b : Step) : Strand φ j x (fun i y=> b.read (X i y) p) (fun i y=> b.read (Y i y) p):=by
   rcases b with ⟨i,n|n⟩; · exact h _
   exact (h _|>.inverse)
lemma weft (h:Quincy φ j x X Y)(p:Four A)(w:Walk): Strand φ j x (fun i y=> travel (X i y) p w) (fun i y=> travel (Y i y) p w):=by
    induction w generalizing p with
    | nil => simp only [travel]; exact Strand.frozen _
    | cons a b ih => simp only [travel]; exact (h.shoe _ a).glowing (ih _)
lemma pores (h:Quincy φ j x X Y)(p:Face A): Strand φ j x (fun i y=> faceValue (X i y) p) (fun i y=> faceValue (Y i y) p):= h.weft _ _
lemma turn (h: Quincy φ j x X Y)(s:Signed): Quincy φ j x (fun i y=> pull s 0 (X i y)) (fun i y=> pull s 0 (Y i y)):=fun _=> h.shoe _ _
end sturdy
variable {U V: ℕ→ E→ Config G c}
lemma books (h: Quincy φ j x U V)(S:StepData c f): Quincy φ j x (fun i y=> replica S.ratio (U i y)) (fun i y=>replica S.ratio (V i y)):=by
    intro i; by_cases hv:S.ratio.parent (i.1+Lattice.step i.2)=S.ratio.parent i.1 <;> simp only [replica,hv,↓reduceIte]
    · exact Strand.frozen _
    exact h _
lemma atspot (h: Quincy φ j x U V)(s:Slot)(i:Site c): Frill φ j x (fun n y=> s.atSite (U n y) i) (fun n y=> s.atSite (V n y) i):=by
    let C (n:ℕ)(y:E):= expandAt i (U n y); let D(n:ℕ)(y:E):= expandAt i (V n y)
    have hx:Quincy φ j x C D:=fun i=> h _; exact (hx.weft _ _).nuptX (hx.pores _|>.songs)
lemma standards (μ:Ultrafilter ℕ) (p:ℕ→ Config G c): Quincy μ j x (fun i _=> p i) (fun i _=>p i):= fun i=> Strand.banners μ (fun k=>p k i)
end Quincy
end YM.ConnectedActivityE6.Lim
