import YM.TraceExtension.Atlas.Sara
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace StressFlux TraceExtension MergeProof.East Next.Rank
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{C:Family G}{X:Extraction.Order}{S:Table C.book}(F:Final C X S){H:(Bel C.book).Hierarchy}(h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{Z:Arch C} (hq:Bliss F 𝓛 Z H)
local notation "F₀"=> Bel C.book
structure Another (Q P:ℝ→change S 4): Prop where
    spun : ∀ᶠ i in trail,AlignV F.room.kernel F.sector H (Q i)
    near : Tendsto (fun i=> moveV (S:=S) 4 (Q i) (P i)) trail (𝓝 1)
include h hq
lemma skyline : ∃ J V,Scribe X J V Z F.sector 𝓛 F.room.kernel H:=by obtain ⟨i,hi,J,hJ,V,hV⟩:= hq.picks costHint cost_clears cost_pos; exact ⟨J,V,hV⟩
lemma across (P Q:ℝ→change S 4)(hp:PlotX F H 𝓛 h P)(hv:Another (H:=H) F Q P)(f:ℝ→ℝ) (hD:TendC F P f): ∃ g:ℝ→ℝ,TendC F Q g∧ ∃ t:ℝ→ℝ,Tendsto t trail (𝓝 1)∧ ∀ᶠ i in trail,g i=f i*t i:=by
    let T:= stepField C; let H':= F.room.kernel; obtain ⟨J,V,hV⟩:= skyline F h hq
    have he:∀ᶠ i in trail,∃ t:ℝ,(Q i).symm (P i T)=t • T:=by
        filter_upwards[hp,hv.spun] with i hi ht; let U:= P i; let L:= Q i;let A:= L.symm (U T); have hz : expectation (F₀) 4 A=0:=by rw[← ht.cent A,show L A = U T from L.apply_symm_apply _,hi.1.frame.cent]; exact sceneV H
        obtain ⟨ha,hF⟩:= legitimacy F h hV; let v:Active (F₀):=⟨A,hz⟩
        apply scale_vector h H v
        · apply Subtype.ext; rw [star_act]; apply L.injective; rw[ht.align.real];change S.conj _ 4 (L (L.symm _))=L (L.symm _); rw[L.apply_symm_apply, ← hi.1.frame.align.real, ha]
        intro s; apply Subtype.ext; rw [swing_act,← (baseRights (C:=C) (H:=H) h).signed]; apply L.injective; rw[ht.align.axis]; change F.sector.turns.act _ _ (L (L.symm _)) = L (L.symm _); rw[L.apply_symm_apply,← hi.1.frame.align.axis,hF]
    let t(i:ℝ):=if he:∃ t:ℝ,(Q i).symm (P i T)=t • T then he.choose else 0; have ht:= he.mono (fun i hi=> (show _ = t i • T from by unfold t; rw[dif_pos hi]; exact hi.choose_spec))
    let v:= trace_none C
    have hz:Tendsto t trail (𝓝 1):=by
        let U (i):= moveV (S:=S) 4 (Q i) (P i) T
        have hp:Tendsto U trail (𝓝 T):= Dash.arcing hv.near (tendsto_const_nhds (x:=T))
        let p:ℝ→ₗ[ℝ] (Bel C.book).Field 4:= LinearMap.toSpanSingleton ℝ _ T
        obtain ⟨W,hW⟩:=p.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (show Injective p from smul_left_injective ℝ (scale_alive h H)))
        have hF:P=P:=rfl; have hh(c:ℝ): W (c • T)=c:=LinearMap.congr_fun hW _; have he: W T=1:= (show T=(1:ℝ) • T from (one_smul ..).symm) ▸ hh 1
        have hx:= W.continuous_of_finiteDimensional.continuousAt.tendsto.comp hp; rw[he] at hx;exact hx.congr' (ht.mono (fun i hi=> by change W ((Q i).symm (P i T))=_; rw[hi,hh]))
    have hP: ∀ᶠ i in trail,i^4 • lum F= (4*(f i*t i)) • Q i T:=by
        have hz:∀ᶠ i in trail,i^4 • lum F= (4*f i) • P i T:=by
            obtain ⟨c,hc⟩:= hD.centered; filter_upwards [hc,hp] with i hi hv
            let t:= stressTrace F.sector.energy; let q:= euclideanVEV S S t-euclideanVEV S (selected F) t;let p:= S.unit 4; let L:=(centering S 4).restrictScalars ℝ; let K:=H'.laws
            have he:= congr_arg L hi; rw [show center F=lum F+q • p from ?_,smul_add, map_add,map_add, L.map_smul (i^(4:ℕ)) _, L.map_smul (i^(4:ℕ)) _, L.map_smul (4*f i) _,L.map_smul (i^(4:ℕ)) _,show L (lum F)=lum F from zero_center (⟨_,lum_active F⟩: Active S), show L (q • p)=0 from ?_,show L ((P i) T)=P i T from ?_, show L (c • p)=0 from ?_] at he
            · simpa using he
            · change centering S 4 _=_; rw [map_smul, show centering S 4 p=0 from const_out K,smul_zero]
            · exact zero_center (⟨P i T,(show expectation S 4 _=0 by rw[hv.1.frame.cent];exact sceneV H)⟩:Active S)
            · change centering S 4 _=_; rw [map_smul, show centering S 4 p=0 from const_out K,smul_zero]
            unfold q; change t-_=t-_+_; rw[sub_smul];abel
        filter_upwards[hz,ht] with i hi he; apply hi.trans; rw [← LinearEquiv.apply_symm_apply (Q i) (P i T),he, show Q i (t i • T)=t i • Q i T from ((Q i).toLinearMap.restrictScalars ℝ).map_smul .., smul_smul,mul_assoc]
    refine ⟨fun i=> f i*t i, ⟨fun g hG=>?_, ?_, (hP.and hv.spun).mono fun i hi=> measure_energy F h i (Q i) hi.2 _ hi.1⟩,t,hz, Eventually.of_forall fun _=>rfl⟩
    · have hp:= (hD.measures _ hG).mul hz; rw[mul_one] at hp; exact hp.congr (fun i=> by simp only[div_mul_eq_mul_div])
    obtain ⟨c,hc⟩:= hD.centered; refine ⟨c,(hc.and ht).mono (fun i ⟨hi,he⟩=> ?_)⟩; rw [hi, ← LinearEquiv.apply_symm_apply (Q i) (P i T),he,show Q i (t i • T)=t i • Q i T from ((Q i).toLinearMap.restrictScalars ℝ).map_smul ..,smul_smul,mul_assoc]
end YM.Trace.Pilot
