import YM.Further.QUANTUM_RATES_PORT.RelativePrice
import YM.MergeProof.East.Gran
import YM.MergeProof.West.Orange
import YM.UVNext.ANNULUS_COMPARISON.Bases


-- adaptation YM.Next.UV_STRESS.Foundation at `zones`
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Acme
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Cells Spec
open Next.UVStress
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {S : Table C.book} {W : DiffPlan S}
theorem readyA (hC : C.Makes) (h : F.Ordered C S) (hp : F.PointLimits C S) (H : S.Hierarchy)
    (hx : CellHyp C F) (hw : W.Inclusions S) (hv : W.Derivatives S)
    (above : DimAbove S) (T : Lighthouse C.book) (a : (Bel C.book).Hierarchy)
    (u : T.W.Inclusions (Bel C.book)) (v : T.W.Derivatives (Bel C.book)) (p : T.W.Orientation a.spin) (hF : FreeDiv T a p) (he : Stations C F a.spin)
    (budget : Aroma C) :
    W.Orientation H.spin ∧ ∃ (I : IR (C:=C) S) (X : Scaling S),
      I.J≠0 ∧ I.J∈KernelSpace H.spin ∧ 
        Approaches (path X) (isoPanel X) ∧ Stable H.spin a.spin W T.W X ∧
          X.meter I.J T.J ∧ Pre H W I.J I.p I.Y ∧ ActLaw W T I.J H.spin a.spin := by
  have hh := Work.D06.answer hC H.smooth H.laws.toSymmetric hp W hv hw H.spin
  obtain ⟨Y,hY,hy⟩ := Stations.equivalences H h a he hw hh u p above
  obtain ⟨J,X,hn,hJ,hX,hZ,ha⟩ := produce_current H hv hh a T v p hF Y hY hy
  have hc := (linear_cons W H.spin hh J).1 hJ
  have ht := focused H hv a T v X hX hZ _ ha
  obtain ⟨p,A,hA⟩ := shells_law hC hx hp H hv J.val hc budget
  exact ⟨hh,⟨J.val,p,A⟩,X,hn,J.property,hX,hZ,ha,⟨hc,(sym_mem.mp (kernel_mem.mp J.property).1).2.2,hA⟩,ht⟩
lemma emanate (H : Aroma C) (hq:G.Simple) (ht:Grill C F) (he:MergeProof.East.CompleteWeak C F)(s:Seed C F S)(hi : W.Inclusions S)(hD : W.Derivatives S) :∃ (M:MaxwellData C)(I:IR (C:=C) S), I.J≠0 ∧ UV C F S W M I:=by
    obtain ⟨T,_,_⟩:= Maxwell.Free.maxwell_supplies C hq 1 one_ne_zero
    obtain ⟨M, _, _, _, _, _, _, hd⟩ := YM.UVNext.FreeStress.fire hq T 1 one_ne_zero
    have hh := M.hT.smooth
    have hS := realizes_stations s.cutoff s.generic s.ordered s.kernel.smooth hh M.hT.spin (fun N D R hr=> he N D R (zero_lt_one.trans_le hr) hh _)
    obtain ⟨hf,I,X,hI,hX,hY,hZ,hM,hp,ha⟩ := readyA s.cutoff s.ordered s.generic s.kernel s.copies hi hD (cap_given s.corrected) M.T M.hT M.lit.edges M.lit.pales M.lit.hers hd hS H
    exact ⟨M,I,hI,s,hf,hp,ha,ht⟩
end YM.MergeProof.Acme
