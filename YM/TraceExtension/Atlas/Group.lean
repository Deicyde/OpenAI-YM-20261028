import YM.TraceExtension.Atlas.Pilot
import YM.TraceExtension.Atlas.Moons
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction OS OS.Ground Spec MeasureTheory Wilson
open RG Terrace MergeProof.East Next.Rank Next.Rank.East Next.UVStress Further.CorrectedLift Climb
open Analysis TraceExtension Boundary Over Org Work.A05 Table
open scoped Topology BigOperators InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} {F:Final C f S}
variable {H:(Cells.standard C).Hierarchy}{J:Scaling S}{V:∀ i,Vane C i}
variable {Z:Terrace.Arch C}
local notation "F₀"=> Bel C.book
lemma baseRights (h:G.Simple): (turns C).Laws (Maxwell.Free.scheme C.book.grid) H.spin :=by
    obtain ⟨s,q,hK,hS,hE,hR⟩:=stages (C:=C) h
    have hx:=s.lit.turns; rwa[q,hK] at hx

theorem compass(h:G.Simple): Spin.Port (turns C) H.spin := let hp:=baseRights (C:=C) (H:=H) h; ⟨hp.spin,hp.fixes,hp.group,hp.signed,hp.real,hp.infinitesimal⟩
theorem compassF(F: Final C f S): Spin.Port F.sector.turns F.room.kernel.spin := let hp:=F.phase.transport.spots; ⟨hp.spin,hp.fixes,hp.group,hp.signed,hp.real,hp.infinitesimal⟩
-- transform rows. first harmonic.
variable (h:G.Simple)(h₁:Scribe f J V Z F.sector 𝓛 F.room.kernel H)
private lemma cog_linear {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E][NormedSpace ℝ E][IsScalarTower ℝ ℂ E]{G:Gauge}{L:Register G}{S:Table L}{d:ℕ}{R:Rotation S}{H:S.RealSpin}(h:Spin.Port R H)(U:E≃ₗ[ℂ] S.Field d): IsLinearMap ℝ (cog h U):=by
   constructor; intro a b;ext1 x
   · change U.symm (R.lie d (a+b) _)= _; rw[map_add]; change U.symm (R.lie d a _+R.lie d b _)=_; rw[map_add];rfl
   intro a b; ext1 x; change U.symm (R.lie d (a • b) (U x))= _; rw[map_smul]; exact (U.symm.toLinearMap.restrictScalars ℝ).map_smul a _
include h h₁
lemma travels(d:ℕ)(p:Ortho.Skew):
    let W(k):= J.U k d
    Tendsto (fun k=> cog (compassF F) (W k) p) atTop (𝓝 (cog (compass (C:=C) (H:=H) h) (LinearEquiv.refl ℂ ((Bel C.book).Field d)) p)):=by
    intro W; let U:= cog (compass (C:=C) (H:=H) h) (LinearEquiv.refl ℂ ((Bel C.book).Field d))
    have he:= cog_linear (compass (C:=C) (H:=H) h) (LinearEquiv.refl ℂ ((Bel C.book).Field d)); have hv(k):= cog_linear (compassF F) (W k)
    let s (K:Ortho.Skew):= Tendsto (fun k=> cog (compassF F) (W k) K) atTop (𝓝 (U K))
    have hp : p∈ Submodule.span ℝ (Set.range Spin.K):= by rw [Spin.spans]; trivial
    change s p; apply Submodule.span_induction (p:=fun x _=>s x) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨i,rfl⟩; exact stagesL F h h₁ d i
    · unfold s U; simp_rw [(hv _).map_zero, he.map_zero]; exact tendsto_const_nhds
    · intro u v hu hU ha hb; unfold s U; simp_rw [(hv _).map_add, he.map_add]; exact (show Tendsto _ _ _ from Tendsto.add ha hb)
    intro a u hu hv'; unfold s U; simp_rw [(hv _).map_smul,he.map_smul]; exact Tendsto.const_smul hv' _
lemma acts_tends (d:ℕ)(g:Ortho): Tendsto (fun i=> circle (compassF F) (J.U i d) g) atTop (𝓝 (circle (compass (C:=C) (H:=H) h) (LinearEquiv.refl ℂ ((Bel C.book).Field d)) g)):=by
    let M(i):= circle (compassF F) (J.U i d); let w':= LinearEquiv.refl ℂ ((Bel C.book).Field d); let w:=circle (compass (H:=H) h) w'; let E:= (Bel C.book).Field d
    let T (s):=Tendsto (fun i=>M i s) atTop (𝓝 (w s))
    have he1:T 1:=by unfold T; simp only [map_one]; exact tendsto_const_nhds
    have hG:g∈Bid.AxisGens:=by rw [ (Work.A13.answer :Bid.AxisGens=⊤)]; trivial
    apply Subgroup.closure_induction (p:=fun g _=> T g) ?_ he1 ?_ ?_ hG
    · rintro K (⟨q,rfl⟩|⟨p,t,rfl⟩)
      · apply tendsto_const_nhds.congr'; filter_upwards[h₁.monorail.units d] with i hi
        ext1 x; change (turns C).act d q.ortho x=(J.U i d).symm _; change _=(J.U i d).symm (F.sector.turns.act d q.ortho _); rw [(baseRights (H:=H) h).signed,F.phase.transport.spots.signed]; exact ((J.U i d).eq_symm_apply).2 (hi.1.signed ..)
      unfold T w M; apply clm_convergence; intro v
      exact raygo _ _ _ _ _ _ v (travels h h₁ d p)
    · intro u v hu hv ha hb; unfold T; simp_rw [map_mul]; exact Tendsto.mul ha hb
    intro u hu h; exact inv_way M w u h
end YM.Trace.Pilot
