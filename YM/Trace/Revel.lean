import YM.MergeProof.Summit
import YM.Trace.Estate
import YM.Trace.Center

set_option autoImplicit false
set_option maxRecDepth 12000
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000

noncomputable section
namespace YM.Trace
open Function Filter Set OS OS.Ground Word Maxwell Table Pairing Next.UVStress Climb Org Org.Phase Cells Extraction Spec
open scoped Topology ENNReal BigOperators ContDiff RealInnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} {Q : MaxwellData C}
variable {V : DiffPlan S} {I : IR (C:=C) S} {qH : Org.UV C f S V Q I} {c : ℝ} {U : ∀ d, Spin.change S d} {Y : S.Stress}

-- midpoint translation in genuine selected phase
lemma midpoint (A : Final C f S) (e s : ℝ) (hs : 0<s) : frontCount (state A) s (energyLine A.sector.energy s e) = (s:ℂ)^8* restTrace A e s := by
   have H := A.phase.phase.states A.α.atPoint
   let v := s • (2:ℝ)⁻¹ • basis timeAxis
   let x := points (![0,s • basis timeAxis] : Fin 2 → E4)
   have h : Points.across v (s • joined) = x := by
     apply PiLp.ext
     intro j
     rcases eq_or_ne j (0:Fin 2) with rfl|h
     · rw [Points.across_coord]
       change s • joined (Fin.castAdd 1 (0:Fin 1)) + _ = 0; unfold v joined; rw [Pairing.enter]
       ext1 i; simp only [Pairing.ride]; change s * Ortho.move _ _ i + _ = _; rw [Signed.mirrored]; exact (by
         change s*(if i=timeAxis then -ticking (2:ℝ)⁻¹ _ i else ticking (2:ℝ)⁻¹ _ i)+s*((2:ℝ)⁻¹ * (basis timeAxis) i) = 0
         unfold ticking; split_ifs with hp
         · change s*(-((2:ℝ)⁻¹ * (basis timeAxis) i))+ s*((2:ℝ)⁻¹ * (basis timeAxis) i)=0; ring
         change s*((2:ℝ)⁻¹ * (basis timeAxis) i)+_=0
         simp [basis_eq,hp])
     · have he : j=1 := by fin_cases j; contradiction; rfl
       rw [he, Points.across_coord]
       change s • joined (Fin.natAdd 1 (0:Fin 1)) + _ = s • _; unfold v joined; rw [Pairing.leave]
       change s • (2:ℝ)⁻¹ • _ + _ = _
       module
   have hx := Work.A05.smul_conf hs joined_free
   let q := theta A e
   let T := state A
   have hp : frontCount T s q = restTrace A e s := by
      change T.read (s • joined) (unlabel q) = T.read x (unlabel q)
      rw [← h,H.translations _ _ hx]

   unfold frontCount energyLine
   rw [(S.classMoment (state A) (fun _ => 4) _).map_smul_univ (fun _ => (↑(s^4:ℝ):ℂ)) (fun _ => q),
       smul_eq_mul]
   rw [show S.classMoment T (fun _ : Fin 2=>4) (s • joined) (fun _=>q)= _ from hp]
   rw [Fin.prod_univ_two]; push_cast; ring

noncomputable def centerFor (A : Final C f S) : S.Field 4 →ₗ[ℂ] S.Field 4 := LinearMap.id -
     (oneptL A 4).smulRight (S.unit 4)
lemma centerFor_unit (A : Final C f S) : centerFor A (S.unit 4) = 0 := by change S.unit 4 - (oneptL A 4 (S.unit 4):ℂ) • S.unit 4 = 0; rw [onept_unit,one_smul,sub_self]
lemma centerFor_trace (A : Final C f S) : centerFor A (sumTrace A.sector.energy)=traceField A := by
    unfold centerFor; change (sumTrace A.sector.energy) - (oneptL A 4 _) • S.unit 4=_
    have hm : theta A 0 = sumTrace A.sector.energy := by simp [withoutMean]
    rw [← hm,mean_correct,traceField_eq]

/-- A stronger witness along one subsequential unselected UV comparison and
    with a heat-unique phase chosen respecting the engineering two-point
    limit. No logarithmic precision, coupling representation or exclusion by
    itself. Uses the same actual Wilson cap-four fields, with the displayed
    free scalar at one quarter of the axis sum. `d` is an exact (not jet-truncated)
    real coefficient in these moving frames. These matrices need not yet be
    calibrated to the continuous homogeneous X scheme. -/
structure Echo (C : Family G) (f : Order) (S : Table C.book) where
  final : Final C f S
  reference : MaxwellData C
  ir : IR (C:=C) S
  regime : UV C f S final.sector.derivatives reference ir
  c : ℝ
  U : ∀ d, Spin.change S d
  tabulate : Tab S final.sector.derivatives reference ir regime c U final.sector.energy
  canonical : reference.T.J = UVNext.FreeStress.torch C.book.grid 1
  factor : reference.T.κ = -1
  path : Scaling S
  comes : Approaches (Next.UVStress.path path) (isoPanel path)
  stable : Stable regime.basis.kernel.spin reference.hT.spin final.sector.derivatives reference.T.W path
  source_alive : ir.J≠0
  source_centered : ir.J ∈ KernelSpace regime.basis.kernel.spin
  produces : path.meter ir.J reference.T.J
  reference_law : FreeDiv reference.T reference.hT reference.lit.hers
  reference_rank_two : Tensorial reference.T.K reference.T.J
  coeff : ℕ→ℝ
  along : ℕ→ℕ
  rate : StrictMono along
  damp : Tendsto coeff atTop (𝓝 0)
  scalarizes : ∀ᶠ k in atTop, (path.r k)^4 • traceField final = (4 * coeff k) • centerFor final (actAt path k)
  retreats : ∀ e : ℝ, Tendsto (fun i => (path.r (along i):ℂ)^8 * restTrace final e (path.r (along i))) atTop (𝓝 0)

-- adapt Loom.cleanse. One common choice can be made for the heat law AND the
-- trace along a further sequence, not a claim on every pure phase or upgrading
-- by interchanging limits.
set_option maxHeartbeats 4000000 in
lemma echo_tab (hG : G.Simple) (hc : Calibrated C) (hT : Tab S V Q I qH c U Y)
    (hzI : I.J≠0) (he : I.J∈KernelSpace qH.basis.kernel.spin) (hq : FreeDiv Q.T Q.hT Q.lit.hers)
    (X : Scaling S) (hX : Approaches (path X) (isoPanel X)) (hS : Stable qH.basis.kernel.spin Q.hT.spin V Q.T.W X)
    (hm : Q.T.J = UVNext.FreeStress.torch C.book.grid 1) (hTensor : Tensorial Q.T.K Q.T.J)
    (hMeter : X.meter I.J Q.T.J) (ht : ∃ K0 : Boundary.Spins S,
        K0.Descends (mill Q I c U) qH.basis.kernel.spin) : Nonempty (Echo C f S) := by
  let s := qH.basis
  let J0 : Spec.Algebra S := ⟨V,mill Q I c U,Y⟩
  have h0 := Bid.Looms YM.Next.Phase.seats Work.B01.answer Work.B02.answer Work.B03.answer Work.B04.answer
    Work.B05.answer Work.B06.answer Work.B07.answer Work.B08.answer Work.B09.answer
    Work.B10.answer Work.B11.answer Work.B12.answer Work.B13.answer Work.B14.answer
    Work.B15.answer Work.B16.answer Work.B17.answer Work.B18.answer qH.tables s J0
  obtain ⟨D⟩ := OS.realization s.kernel timeAxis
  obtain ⟨A,hA⟩ := h0.first hT.locality D
  have hp : Stall J0 D A f := h0.sale hT.locality D A hA
  have hv : Steady D := fun x i => inert D s.kernel J0.turns hT.locality.motion _ x
  obtain ⟨u,hu⟩ := hp.characters
  obtain ⟨R,hR⟩ := OS.Ground.resolution A J0.turns hT.locality.motion s.kernel u hu
  letI hμ := hR.normalized
  have hw := hp.drives R hR
  obtain ⟨p,B⟩ := hw.emits
  let K (i : R.X) : Chamber (p i) timeAxis := Classical.choice (OS.realization (B.loci i) _)
  obtain ⟨q,hq⟩ := hw.horizon B K
  have hHeat := Cluster.lifts K q hq s.kernel hv B.loci hR B.reads
  obtain ⟨d,hd,hO⟩ := exists_moneypath hT hzI he (Q:=Q) (U:=U) (V:=V) (H:=qH) ‹FreeDiv ..› X hX hS hm hMeter hG
  obtain ⟨n,hn,hE⟩ := submits J0 (H:=qH) hT.locality D A R p B hR X (raw_endpoint hT hzI he ‹FreeDiv ..› X hX hS hm hMeter hG)
     (fun y hy => zero_uv hT X hX y hy joined_free)
  obtain ⟨w,hi,hW⟩ := (hHeat.and hE).exists
  obtain ⟨W,hW'⟩ := hw.bags B w (K w)
  let α0 : Selection S := ⟨D,A,R,p,w,K w,W⟩
  have hM : Materializes (C:=C) J0 α0 s.kernel.spin := by
    refine ⟨hT.locality,hA,hv,hR,B.reads,B.loci,B.translations,fun j d => ?_,B.incl,B.deriv,B.fluxes,hW',hi⟩
    obtain ⟨x,T,H'⟩ := s.corrected d
    exact Retain.lift_detect T H' A R (hp.funds d x T H') hR (B.reads j) (B.loci j).laws.toSymmetric (B.sees j)
  obtain ⟨P,hP⟩ := ht
  obtain ⟨B₀,A',Z,hZ,H₀,_,_⟩ := Next.BOUNDARY.after_materializes (s:=s) hM P hP
  let P0 : Final C f S := ⟨hc,s,J0,α0,hM,B₀,A',Z,H₀⟩
  have hz (y) : centerFor P0 (centering S 4 y) = centerFor P0 y := by
      simp only [value_center,map_sub,map_smul,centerFor_unit,smul_zero,sub_zero]
  refine ⟨⟨P0,Q,I,qH,c,U,hT,hm,UVNext.FreeStress.required 1 hG Q hm,X,hX,hS,hzI,he,hMeter,
       ‹FreeDiv Q.T Q.hT Q.lit.hers›,hTensor,d,n,hn,hd,hO.mono fun i hh => ?_, fun e => ?_⟩⟩
  · have h' := congr_arg (fun t => centerFor P0 t) hh
    have hl (b : ℝ) (x) : centerFor P0 (b • x) = b • centerFor P0 x := ((centerFor P0).restrictScalars ℝ).map_smul ..
    simp only [hl,hz] at h'
    rw [← centerFor_trace]; exact h'
  apply (hW e).congr
  intro z
  exact midpoint P0 e (X.r (n z)) (X.positive _)
end YM.Trace

namespace YM.Trace
open Function Filter Set OS Maxwell Labels Analysis Table Pairing Next.UVStress Climb Org Cells Extraction Spec MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {S : Table C.book} {W : DiffPlan S}
lemma graduated_echo (H : MergeProof.Acme.Aroma C) (h : G.Simple) (hc : Calibrated C) (ht : Grill C F) (he : MergeProof.East.CompleteWeak C F) (s : Seed C F S)
    (hi : W.Inclusions S) (hD : W.Derivatives S) : Nonempty (Echo C F S) := by
    obtain ⟨T,_,_⟩:= Maxwell.Free.maxwell_supplies C h 1 one_ne_zero
    obtain ⟨M, htM, _, hRot, _, _, hTensor, hd⟩ := YM.UVNext.FreeStress.fire h T 1 one_ne_zero
    have hh := M.hT.smooth
    have hS := realizes_stations s.cutoff s.generic s.ordered s.kernel.smooth hh M.hT.spin (fun N D R hr=> he N D R (zero_lt_one.trans_le hr) hh _)
    obtain ⟨hf,I,X,hI,hX,hY,hZ,hM,hp,ha⟩ := MergeProof.Acme.readyA s.cutoff s.ordered s.generic s.kernel s.copies hi hD (cap_given s.corrected) M.T M.hT M.lit.edges M.lit.pales M.lit.hers hd hS H
    have hqH : UV C F S W M I := ⟨s,hf,hp,ha,ht⟩
    have ht := Bid.station M W I hqH YM.Outer.miles Work.A01.answer Work.A02.answer Work.A03.answer
      Work.A04.answer Work.A05.answer Work.A06.answer Work.A07.answer Work.A08.answer
      Work.A09.answer Work.A10.answer Work.A11.answer Work.A13.answer Work.A14.answer
      Work.A15.answer Work.A16.answer Work.A17.answer
    obtain ⟨c, U, J, root, hK⟩ := ht.picks W M I hqH hi hD
    exact echo_tab h hc root hI hX hd X hY hZ htM (hRot.symm ▸ hTensor) hM hK

-- same Wilson-family production as the Emanate/Summit route retaining the
-- actual UV curve information.
theorem actual_echo (h : G.Simple) (b : ℝ) (hb : 0<b) (f : Extraction.Order) : ∃ C : Family G,C.Makes ∧ Calibrated C ∧ C.path.levels.clock.kernel.penalty=b ∧ Wcmain C ∧
    ∃ (g : Order) (T : Table C.book), Nonempty (Echo C (f.refine g) T) := by
    obtain ⟨C,hB,hC,hM,hW,H,hQ,hF⟩:= YM.PhysicalNext.Repeat.Legato.noel h hb
    obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF f
    obtain ⟨hs,hG⟩ := hQ (f.refine g) s.copies
    exact ⟨C,hM,hC,hB,hW,g,T,graduated_echo (W:=E) H h hC hs hG s hA.clean.ready hA.clean.tilt⟩
end YM.Trace
