import YM.FullVolume.E6.Clouds
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
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
lemma switch {Y:Type} [TopologicalSpace Y]{a b c d:ℕ→Y}(h: Glints J a b)(he:Glints J c d)(P:ℕ→Prop): Glints J (fun i=> if P i then a i else c i) (fun i=> if P i then b i else d i) :=by
    rcases J.em P with hv|hv
    · exact h.carve (hv.mono fun i hi=> (if_pos hi).symm) (hv.mono fun i hi=> (if_pos hi).symm)
    exact he.carve (hv.mono fun i hi=> (if_neg hi).symm) (hv.mono fun i hi=> (if_neg hi).symm)
lemma wear {t:ℕ}(slot:Fin t→Slot)(A B:ℕ→(Fin t→G.ColorIndex)→ℝ) (U V:ℕ→ E→ Config G c)(h:Quincy φ j p U V)(he:∀ i,Glints φ (fun n=> A n i) (fun n=> B n i))(i:Site c):
    Frill φ j p (fun n y=> (Atom.mk slot (A n)).unmasked (U n y) i) (fun n y=> (Atom.mk slot (B n)).unmasked (V n y) i):= Frill.buds Finset.univ fun k _=> (Frill.bare (he k)).times (Frill.pears Finset.univ (fun b _=> pointed (h.atspot (slot b) i) (k b)))
lemma stare {t:ℕ}(slot:Fin t→Slot)(A B:ℕ→(Fin t→G.ColorIndex)→ℝ)(U:ℕ→ Config G c)(T:BudgetPoint)(he:∀ i,Glints J (fun n=> A n i) (fun n=> B n i))(i:Site c): Glints J (fun n=> (Atom.mk slot (A n)).placed T (U n) i) (fun n=> (Atom.mk slot (B n)).placed T (U n) i):=
    switch ((wear slot A B (fun i _=> U i) (fun i _=> U i) (φ:=J) (p:=(0:ℝ)) (j:=0) (Quincy.standards J U) he i).crest) ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩ (fun v=> Healthy T.threshold ((Atom.mk slot (A 0)).footprint i) (U v))
lemma Soul.pullE {V:ℕ→ E→ Config G c}{K H:ℕ→ Cad G}(h:Soul φ K H) (hx:Quincy φ j p U V)(i: Cell c)(z:ℕ) : Frill φ j p (fun n y=> (K n).path.ellTerms i z (U n y)) (fun n y=> (H n).path.ellTerms i z (V n y)):= (Frill.bare (h.1 i.2 z)).fee (hx.atspot _ _)
lemma Soul.tears {K H:ℕ→ Cad G}(h:Soul J K H)(A:Clip)(U:ℕ→ Config G c)(x:Cell c)(b:ℕ×ℕ)(R d t): Glints J (fun n=>pairTail (K n).path A R d t x (U n) b) (fun n=> pairTail (H n).path A R d t x (U n) b):=by
    have hz:= switch ((((h.pullE (E:=ℝ) (Quincy.standards J U) (j:=0) (p:=0) x b.1).inn (h.pullE (Quincy.standards J U) x b.2)).via (contDiff_id.div_const 2)).crest) ⟨(0:ℝ),tendsto_const_nhds,tendsto_const_nhds⟩ (fun n=> long (K 0|>.path) R d x.2 b ∧ PathData.kept A t x.1 (U n))
    refine hz.carve ?_ ?_ <;> filter_upwards with k <;> simp [pairTail,long, Cad.path]
lemma Soul.paired {K H:ℕ→ Cad G}(h:Soul φ K H) (hx:Quincy φ j p U U)(x:Cell c)(b:ℕ×ℕ)(R d): Frill φ j p (fun n y=> Polar.twin (K n).path x R d (U n y) b) (fun n y=> Polar.twin (H n).path x R d (U n y) b):=by
    by_cases hh:long (K 0).path R d x.2 b; · exact ((((h.pullE hx x b.1).inn (h.pullE hx x b.2)).via (contDiff_id.div_const 2))).alter (Eventually.of_forall fun i=> Eventually.of_forall fun y=> (if_pos (show long (K i).path R d x.2 b from hh)).symm) (Eventually.of_forall fun i=> Eventually.of_forall fun y=> (if_pos (show long (H i).path R d x.2 b from hh)).symm)
    refine (Frill.still (0:ℝ)).alter (Eventually.of_forall fun i=> Eventually.of_forall fun y=> (if_neg (show ¬ long (K i).path R d x.2 b from hh)).symm) (Eventually.of_forall fun i=> Eventually.of_forall fun y=> (if_neg (show ¬ long (H i).path R d x.2 b from hh)).symm)
lemma Soul.roof {K H:ℕ→ Cad G}(h:Soul J K H)(A:Clip)(U:ℕ→ Config G c)(x:Cell c)(R d:ℕ)(t:ℝ)(he:0<d): Glints J (fun n=> Pressure.crown (K n).path A R d t (U n) x) (fun n=> Pressure.crown (H n).path A R d t (U n) x):=by
    have hc:=h.stain A he (Quincy.standards J U) (E:=ℝ) (x:=0) (j:=0) (x,true) R
    have hk:Glints J (fun n=> trunk (K n).path A R d t (U n) x) (fun n=> trunk (H n).path A R d t (U n) x):=switch ((hc.via ((contDiff_norm_sq ℝ).div_const 2)).crest) ⟨(0:ℝ),tendsto_const_nhds,tendsto_const_nhds⟩ (fun n=> PathData.kept A t x.1 (U n))
    let v(n:ℕ):=G.chord (faceValue (U n) x); let D(n:ℕ):= PathData.clipped A t (v n); have hv:Glints J v v:= (FullVolume.Shadow.sails isCompact_univ (f:=fun n=> faceValue (U n) x) (μ:=J) (Eventually.of_forall fun _=>trivial)).bin (Q:=G.chord) (fun _ _=>G.continuous_chord.continuousAt)
    have hD:Glints J D D:=switch (hv.bin (fun _ _=> Continuous.continuousAt (f:=fun s=>A.direct*s^2/2) (by fun_prop))) (hv.bin (fun _ _=> Continuous.continuousAt (f:=fun s=> A.linear*t*s) (by fun_prop))) (fun n=>v n ≤ t)
    exact hk.prods hD (Q:=fun x y:ℝ=> x+y) continuous_add
end YM.ConnectedActivityE6.Lim
