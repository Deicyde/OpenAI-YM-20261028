import YM.OPE.Nesting.Endpoint
import YM.Pert.FirstTarget

/-!
# Joint supplier: actual weak free measuring frames and common OPE

Take the same stronger start as F3's `OPE.through_final` (here using the
same `noel_columns` instance directly), keeping the Maxwell-Emanate branch
and its leading `Pert.FirstExtension` data. Do NOT conjoin existential
answers about theories picked independently. Proof below modifies the argument
of `Pert.Construction.fromBaseline` / `Pert.FirstTarget.firstTarget` to run on
those strengthened receipts. We don't alter imported proofs. Leading data
only; no coupling-power convergence or all-order comparison asserted here.
This can also use the arbitrary intermediate horizons of `Nesting.uniform` on
that one Final.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Measuring
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Cells Spec Next.UVStress
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}
open Pert MergeProof.Acme Orbits

lemma assembled (hG : G.Simple) {b : ℝ} (hb : 0<b) :∃ C:Family G,
    C.path.levels.clock.kernel.penalty=b ∧ Extraction.Wcmain C ∧ ∃ M : MaxwellData C,M.T.W = Maxwell.Free.scheme C.labels ∧ M.T.K = Maxwell.Free.gear C.labels ∧
    M.T.J = YM.UVNext.FreeStress.torch C.book.grid 1 ∧ Tensorial M.T.K M.T.J ∧ ∀ f : Extraction.Order,
    ∃ (g:Extraction.Order) (S:Table C.book)(I:IR (C:=C) S)(W:DiffPlan S)
      (X : Scaling S) (c : ℝ) (U : ∀ d, Spin.change S d) (J : S.Stress),
      ∃ l : Supplier (f.refine g) W M I X, Services C (f.refine g) S ∧ Tab S W M I l.uv c U J ∧
      ∃ h : Final C (f.refine g) S, h.sector=⟨W,mill M I c U,J⟩ := by
  obtain ⟨C,hB,hC,hM,hW,hpkg,H,hQ,hF⟩:= YM.PhysicalNext.Repeat.Legato.noel_columns hG hb
  obtain ⟨T',hM0,_⟩:= Maxwell.Free.maxwell_supplies C hG 1 one_ne_zero
  obtain ⟨M, hJ, hM, hK, _, _, ht0, hd⟩ := YM.UVNext.FreeStress.fire hG T' 1 one_ne_zero
  refine ⟨C,hB,hW,M,hM.trans (congr_arg Lighthouse.W hM0),hK.trans (congr_arg Lighthouse.K hM0),hJ,hK.symm ▸ ht0,fun f => ?_⟩
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
  obtain ⟨c, U, J, b, K, hK'⟩ := ht.picks E M I p.uv p.ider p.deriv
  exact ⟨g,T,I,E,X,c,U,J,p,⟨hs,hG,hpkg,A,L,R,E,hA⟩, b,withFinal hC p.uv c U J b hK'⟩

open Maxwell
set_option maxHeartbeats 900000 in
theorem simultaneous (G:Gauge) (hg : G.Simple) (β : ℝ) (hb : 0<β) : ∃ C : Family G, C.path.levels.clock.kernel.penalty = β ∧
    Extraction.Wcmain C ∧ ∀ f : Extraction.Order,
    ∃ (g : Extraction.Order) (S : Table C.book), Services C (f.refine g) S ∧ ∃ (h : Final C (f.refine g) S) (R:Reader h.sector.derivatives h.sector.turns h.room.kernel.spin) (X : Scaling S),
      FirstExtension h X ∧ Nesting.Uniform h R ∧ Foundation h R ∧ Approaches (path X) (isoPanel X) := by
  obtain ⟨C,hc,hW,M,hd,hK,hj,hT,hp⟩ := assembled hg hb
  refine ⟨C,hc,hW,fun f => ?_⟩
  obtain ⟨g,S,I,W,X,c,U,J,p,hs,h,b,eqb⟩ := hp f
  have hm : (M.T.κ)⁻¹ • M.T.J = freeStress C.labels := by
    rw [kappa_eq hg hd hj,inv_neg,inv_one,neg_smul,one_smul,hj,common_stress]
    rfl
  let t:=b.phase.transport
  obtain ⟨R,hR⟩:= Prescription.chosen b.room.kernel.laws.toSymmetric t.injection
  let r:Reader b.sector.derivatives b.sector.turns b.room.kernel.spin := ⟨R,hR,b.room.kernel,t.injection,t.rights,t.spots⟩
  have hf:= Orbits.produce b r hs
  refine ⟨g,S,hs,b,r,X,?_,Nesting.uniform b r hs,hf,p.limit_⟩
  clear hf
  -- same leading comparison proof
  have he : b.sector.derivatives=W := congrArg Spec.Algebra.derivatives eqb
  refine ⟨?_,fun n j q is a K hK hsep ε he => ?_,?_,fun d => ?_,fun j d => ?_⟩
  · rw [← hd,he]; exact p.fit
  · rw [(congrArg Spec.Algebra.energy eqb : b.sector.energy=J)]
    have hh := mixed_leading p h q is a j hK hsep he
    rw [hm] at hh; exact hh
  · clear r R hR t
    revert he; cases b with | _ _ _ Z α phase B A action realization => cases Z with | _ E K' J' =>
      rintro rfl; exact one_line p
  · rw [he,← hd]; exact for_derivative p d
  rw [eqb,← hK]
  exact rotation_lead p h d j
end YM.OPE.Measuring
