import YM.MergeProof.Summit
import YM.Pert.Deeper
import YM.Pert.Weak

/-!
One set of actual nonperturbative witnesses, with stronger weak UV receipt than
CLOSED. f is already upstream of the choices, there is no switch of tables
between the weak comparison and Final. Import-only ingredient (no baseline
changes).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pert
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Cells Spec Next.UVStress
open scoped Topology ContDiff BigOperators
variable {G : Gauge}
section
variable {C : Family G} {F : Extraction.Order} {S : Table C.book}
    {W : DiffPlan S} {M : MaxwellData C} {I : IR (C:=C) S}

lemma withFinal (hY : Calibrated C) (H : UV C F S W M I) (c U J) (T : Tab S W M I H c U J)
    {K : Boundary.Spins S} (hK : K.Descends (mill M I c U) H.basis.kernel.spin) :
    ∃ h : Final C F S, h.sector = (⟨W,mill M I c U,J⟩ : Spec.Algebra S) := by
  let X : Spec.Algebra S := ⟨W, mill M I c U, J⟩
  have he := Bid.Looms YM.Next.Phase.seats Work.B01.answer Work.B02.answer Work.B03.answer Work.B04.answer
    Work.B05.answer Work.B06.answer Work.B07.answer Work.B08.answer Work.B09.answer
    Work.B10.answer Work.B11.answer Work.B12.answer Work.B13.answer Work.B14.answer
    Work.B15.answer Work.B16.answer Work.B17.answer Work.B18.answer H.tables H.basis X
  obtain ⟨α, hα⟩ := he.cleanse T.locality
  obtain ⟨x, y, Z, hZ, h, hu, hw⟩ := YM.Next.BOUNDARY.after_materializes (s:=H.basis) hα K hK
  exact ⟨⟨hY, H.basis, X, α, hα, x, y, Z, h⟩,rfl⟩
end
open MergeProof.Acme in
lemma fromBaseline (hG : G.Simple) {b : ℝ} (hb : 0<b) :∃ C:Family G,
    C.path.levels.clock.kernel.penalty=b ∧ Extraction.Wcmain C ∧ MergeProof.Ribbons.Materials C ∧ MergeProof.Ribbons.Plenty C ∧ ∃ M : MaxwellData C,M.T.W = Maxwell.Free.scheme C.labels ∧ M.T.K = Maxwell.Free.gear C.labels ∧
    M.T.J = YM.UVNext.FreeStress.torch C.book.grid 1 ∧ Tensorial M.T.K M.T.J ∧ ∀ f : Extraction.Order,
    ∃ (g:Extraction.Order) (S:Table C.book)(I:IR (C:=C) S)(W:DiffPlan S)
      (X : Scaling S) (c : ℝ) (U : ∀ d, Spin.change S d) (J : S.Stress),
      ∃ l : Supplier (f.refine g) W M I X, Tab S W M I l.uv c U J ∧
      ∃ h : Final C (f.refine g) S, h.sector=⟨W,mill M I c U,J⟩ := by
  obtain ⟨C,hB,hP,hMat,hC,hM,hW,H,hQ,hF⟩:= deeper hG hb
  obtain ⟨T',hM0,_⟩:= Maxwell.Free.maxwell_supplies C hG 1 one_ne_zero
  obtain ⟨M, hJ, hM, hK, _, _, ht0, hd⟩ := YM.UVNext.FreeStress.fire hG T' 1 one_ne_zero
  refine ⟨C,hB,hW,hMat,hP,M,hM.trans (congr_arg Lighthouse.W hM0),hK.trans (congr_arg Lighthouse.K hM0),hJ,hK.symm ▸ ht0,fun f => ?_⟩
  obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF f
  obtain ⟨hs,hG'⟩:= hQ (f.refine g) s.copies
  have hh := M.hT.smooth
  have hS := realizes_stations s.cutoff s.generic s.ordered s.kernel.smooth hh M.hT.spin (fun N D R hr=>
    hG' N D R (zero_lt_one.trans_le hr) hh _)
  obtain ⟨hf,I,X,hI,hX,hY,hZ,hM',hp,ha⟩ := readyA s.cutoff s.ordered s.generic s.kernel s.copies hA.clean.ready
    hA.clean.tilt (cap_given s.corrected) M.T M.hT M.lit.edges M.lit.pales M.lit.hers hd hS H
  let p : Supplier (f.refine g) E M I X :=
    ⟨⟨s,hf,hp,ha,hs⟩,hA.clean.ready,hA.clean.tilt,hI,hX,hd,hY,hZ,hM'⟩
  have ht := Bid.station M E I p.uv YM.Outer.miles Work.A01.answer Work.A02.answer Work.A03.answer
    Work.A04.answer Work.A05.answer Work.A06.answer Work.A07.answer Work.A08.answer
    Work.A09.answer Work.A10.answer Work.A11.answer Work.A13.answer Work.A14.answer
    Work.A15.answer Work.A16.answer Work.A17.answer
  obtain ⟨c, U, J, T, K, hK'⟩ := ht.picks E M I p.uv p.ider p.deriv
  exact ⟨g,_,I,E,X,c,U,J,p,T,withFinal hC p.uv c U J T hK'⟩
end YM.Pert
