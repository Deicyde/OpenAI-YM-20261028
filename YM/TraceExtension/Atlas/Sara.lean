import YM.TraceExtension.Atlas.Global
import YM.TraceExtension.WilsonTrace
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace StressFlux TraceExtension MergeProof.East Next.Rank
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{C:Family G}{X:Extraction.Order}{S:Table C.book}(F:Final C X S){H:(Bel C.book).Hierarchy}(h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{Z:Arch C} (hq:Bliss F 𝓛 Z H)
local notation "F₀"=> Bel C.book
lemma trace_none (C:Family G): ∑ i:Axis,standard4 C i i=0:=by
    let A:= Bel C.book; have ht : standard4 C= -StressFlux.material A weyl:=by unfold standard4 Shelves.materialB; rw [show Fin.cons _ _ = -weyl from Over.FZone_c G, material_neg]
    rw[ht]; simp only[Pi.neg_apply,Finset.sum_neg_distrib,StressFlux.material, ← map_sum, show ∑ i:Axis,stress G weyl i i=0 from Trace.conformal G,map_zero,neg_zero]
include h
lemma measure_energy (s:ℝ)(U:change S 4)(ht: AlignV F.room.kernel F.sector H U)(f:ℝ)(hx:s^4 • lum F=(4*f) • U (stepField C)): ∃ a e:ℝ, ∀ i j,U.symm (s^4 • F.sector.energy i j)=a • standard4 C i j+(if i=j then f • stepField C+e • ((F₀).unit 4) else 0):=by
    obtain ⟨a,d,e,he⟩:= exactEnergy F h s U ht
    let v:= stressTrace F.sector.energy; let τ:= expectation S 4 v; let X':= centering (Bel C.book) 4; let E:= (4*d) • stepField C
    have ht0:X' (stepField C)=stepField C:=zero_center (⟨_,sceneV H⟩:Active _)
    have hY : U.symm (s^4 • v) = E + (4*e) • ((Bel C.book).unit 4):=by
       unfold v stressTrace; rw[Finset.smul_sum,map_sum]; simp only[he,if_true, Finset.sum_add_distrib, ← Finset.smul_sum]; rw[trace_none C,smul_zero,zero_add]; rw [Finset.sum_const, Finset.sum_const]; simp only[Finset.card_univ,Fintype.card_fin]; unfold E; module
    have hp: lum F=v-τ • S.unit 4:=by change v-_ = _; rw [show euclideanVEV S S v= τ from (onepoint S v).symm]
    have hs: X' (U.symm (s^4 • lum F))=E :=by
        let V:=(Bel C.book).unit 4; have hh(c:ℝ)(x):X' (c • x)=c • X' x:= (X'.restrictScalars ℝ).map_smul ..
        rw [hp,smul_sub,map_sub,hY,map_sub,map_add, show X' E=E from by unfold E; rw[hh,ht0],hh (4*e),show U.symm (s^(4:ℕ) • _) = s^(4:ℕ) • U.symm (τ • S.unit 4) from (U.symm.toLinearMap.restrictScalars ℝ).map_smul .., hh (s^ (4:ℕ)) _]
        rw [U.symm.map_smul,← ht.align.unit,U.symm_apply_apply,X'.map_smul,show X' V=0 from const_out H.laws];simp
    have hD:d=f:=by rw [hx,show U.symm _= (4*f) • U.symm (U (stepField C)) from (U.symm.toLinearMap.restrictScalars ℝ).map_smul .., U.symm_apply_apply, show X' _=(4*f) • X' (stepField C) from (X'.restrictScalars ℝ).map_smul ..,ht0] at hs; exact mul_left_cancel₀ (by norm_num:(4:ℝ)≠0) (smul_left_injective ℝ (scale_alive h H) hs.symm)
    exact ⟨a,e,hD ▸ he⟩
structure TendC (P:ℝ→change S 4) (f:ℝ→ ℝ): Prop where
    measures : ∀ g:ℝ→ℝ,Coupling G g→ Tendsto (fun s=> f s / g s^ (2:ℕ)) trail (𝓝 (-b0 G/2))
    centered : ∃ c:ℂ,∀ᶠ i in trail,i^(4:ℕ) • center F=(4*f i) • P i (stepField C) + i^ (4:ℕ) • (c • S.unit 4)
    tensor : ∀ᶠ i in trail,∃ a e:ℝ,∀ j k:Axis,(P i).symm (i^ (4:ℕ) • F.sector.energy j k)= a • standard4 C j k + (if j=k then f i • stepField C + e • ((F₀).unit 4) else 0)
include h hq
lemma margaret (P:ℝ→change S 4)(hp:PlotX F H 𝓛 h P): ∃ f:ℝ→ℝ,TendC F P f:=by
    obtain ⟨f,hf,hz⟩:= s_color F h hq P hp; let v:=stressTrace F.sector.energy;let c:=euclideanVEV S S v-euclideanVEV S (selected F) v
    refine ⟨f,fun w p=> force_b G▸ hz w p, ⟨c,?_⟩, (hp.and hf).mono (fun i hi=> measure_energy F h i (P i) hi.1.1.frame (f i) hi.2)⟩
    refine hf.mono fun i hi=>?_ ; rw [show center F=lum F + c • S.unit 4 from ?_,smul_add,hi]; unfold c; change v-_=v-_+_; rw[sub_smul];abel
end YM.Trace.Pilot
