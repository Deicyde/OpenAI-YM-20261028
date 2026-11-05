import YM.TraceExtension.Atlas.Trail
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East Next.Rank
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S){H:(Bel C.book).Hierarchy}
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{J:Scaling S}{V:∀ i,Vane C i}{Z:Arch C}
variable (h₁:Scribe X J V Z F.sector 𝓛 F.room.kernel H)

abbrev stepField(C:Family G):= OScale C.book
include h
lemma underLine {v:change S 4}(g: AlignV F.room.kernel F.sector H v) : ∃ c:ℝ,v.symm (lum F)=c • stepField C:=by
    let K:= F.sector.turns;let x:=lum F; let t:= stepField C
    have he : expectation (F₀) 4 (v.symm x)=0:=by rw[← g.cent,v.apply_symm_apply]; exact lum_active F
    let P:Active (F₀):=⟨v.symm x, he⟩
    refine scale_vector h H P ?_ ?_
    · apply Subtype.ext; rw [star_act]; apply v.injective; change v _=v (v.symm _);rw [g.align.real,v.apply_symm_apply]; exact lum_real F
    intro s; apply Subtype.ext; rw[swing_act]; apply v.injective;change _=v (v.symm x); rw[← (baseRights (C:=C) (H:=H) h).signed,g.align.axis];change K.act _ _ (v (v.symm x))=v (v.symm x);rw [v.apply_symm_apply]; exact lum_spin F _
include h h₁
lemma legitimacy : ( (F₀).conj H.spin 4 (stepField C)=stepField C)∧ (∀ g, (turns C).act 4 g (stepField C)=stepField C):=by
    obtain ⟨U,hU,hk⟩:= fulfill F h h₁; obtain ⟨i,hi⟩:= hk.exists; let v:= U i; let P:=hi.frame; let K:= F.sector.turns
    obtain ⟨c,hc⟩:=underLine F h P; let t:= stepField C; let x:=lum F
    have he : c≠0:=by
        intro ht; rw [ht,zero_smul] at hc; apply unselected_alive F h h₁; exact v.symm.injective (hc.trans (map_zero _).symm)
    have hV : c • (v t)=x:= by change (c:ℝ) • v t=x; rw[← (show v (c • t)=c • (v t) from (v.toLinearMap.restrictScalars ℝ|>.map_smul ..)), ← hc,v.apply_symm_apply]
    constructor
    · let m:=StressFlux.conjQ (d:=4) H.spin; apply v.injective; apply smul_right_injective _ he; change c • v (m t)=c • v t; rw [← show v (c • m t)=c • v (m t) from (v.toLinearMap.restrictScalars ℝ).map_smul ..,← m.map_smul, hV]; change v ((F₀).conj H.spin 4 _)=_; rw [P.align.real, ← hc,v.apply_symm_apply]; exact lum_real ..
    intro g'; apply v.injective; apply smul_right_injective _ he; rw[P.align.axis]; change c • K.act 4 g' (v t)=c • v t; rw[← show K.act 4 g' (c • v t)=c • K.act _ g' (v t) from ((K.act _ _).toLinearMap.restrictScalars ℝ|>.map_smul ..),hV]; exact lum_spin ..

lemma activeShip {r:ℝ}{T:change S 4} (hp:XScope (H:=H) F h r T): ∃ U:Active (F₀)≃ₗ[ℂ] Active S, AngularH F.room.kernel H r (coverV H F.room.kernel U) ∧ Favor F.room.kernel H U ∧ LiftB U.toLinearMap (scannerX F.room.kernel r).val=(scannerX H 1).val∧ (coverV H F.room.kernel U) (stepField C)=T (stepField C):=by
    obtain ⟨v,⟨⟨U,hv,hg,hu⟩⟩,he⟩:= hp.precess
    have hV: AngularH F.room.kernel H r (coverV H F.room.kernel U):=⟨U,rfl,hg,hu⟩
    refine ⟨U,hV,hg,hu,?_⟩
    rw[he,← hv]; obtain ⟨hz,hM⟩:=legitimacy F h h₁
    let t:=stepField C;let W:=v t; let q:=T.symm W;let A:= F.sector.turns; let S':= F₀
    have hh: realH F.room.kernel.spin H.spin v:=by
       rw[hv];exact ⟨fun k x=> (coverV_H _ _ _ hg.twist hg.bar _).2 _,fun x=>(coverV_H _ _ _ hg.twist hg.bar _).1⟩
    have hf: Coherent H.spin F.room.kernel.spin _ T:= ⟨hp.frame.align.real,fun s x=>by rw [← (baseRights (C:=C) (H:=H) h).signed,hp.frame.align.axis]; exact F.phase.transport.spots.signed ..⟩
    have hw: S.conj F.room.kernel.spin 4 W=W ∧ ∀ g,S.mirror F.room.kernel.spin 4 g W=W:=by
       unfold W; refine ⟨?_,?_⟩
       · rw[← hh.2,hz]
       intro u; rw[← hh.1,← (baseRights (C:=C) (H:=H) h).signed,hM]
    have hi: expectation S' 4 q=0:=by rw[← hp.frame.cent q, show T q=W from T.apply_symm_apply _]; unfold W; rw[hv,coverV_scale]; exact sceneV H
    let p:Active (F₀):=⟨q,hi⟩; obtain ⟨c,hc⟩:=scale_vector h H p (by apply Subtype.ext; rw[star_act]; change _=T.symm W;rw [← (flips hf).stars,hw.1]) (fun s=>Subtype.ext (by rw[swing_act];change _=T.symm W;rw[← (flips hf).signed,hw.2])); change q=c • t at hc
    have hP(s): A.act 4 s W=W:=by
       let u:= (turns C).act 4 s; have hU:W=T (c • t):=by rw[← hc]; exact (T.apply_symm_apply _).symm
       rw [hU,← hp.frame.align.axis, (show u (c • t)=c • u t from (u.toLinearMap.restrictScalars ℝ).map_smul ..),show u t=t from hM s]
    let f:=circle (compassF F) v; let g:= circle (compass (C:=C) (H:=H) h) (LinearEquiv.refl ℂ ((F₀).Field 4))
    exact congr_arg v (mean_fixed f g (circle_cont ..) (circle_cont ..) t (fun i=>by change v.symm (A.act 4 i W)=_; rw[hP]; exact LinearEquiv.symm_apply_apply ..) hM).symm
end YM.Trace.Pilot
