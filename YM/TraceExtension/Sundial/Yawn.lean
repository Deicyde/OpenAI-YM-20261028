import YM.TraceExtension.Atlas.Energy
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge}{C:Family G}{X:Extraction.Order}{L:Register G}
variable {S:Table C.book}(F: Spec.Final C X S){H:(Bel C.book).Hierarchy}
local notation "F₀"=> Bel C.book
open StressFlux TraceExtension Over
variable (h:G.Simple)
-- stress formula in aligned cap-four fields. unselected stress.V.theta
include h
lemma grossEnergy (s:ℝ)(P:change S 4)(he:AlignO F.sector F.room.kernel.spin H 4 P): ∃ a d e:ℝ, ∀ i j, P.symm (s^4 • F.sector.energy i j)=a • standard4 C i j +(if i=j then d • stepField C+e • ((F₀).unit 4) else 0):=by
    let R:= F.sector.energy; let V(i j:Axis):= P.symm (s^4 • R i j); let K:= F.sector.turns; let L:=turns C; let hp:=F.phase.transport; let y:=standard4 C
    have ht : Tensorial L V:=by
         intro A i j; apply P.injective; unfold V; rw [he.axis,map_sum]; simp_rw [map_sum,map_smul,P.apply_symm_apply]; let f:= (K.act 4 A).toLinearMap.restrictScalars ℝ
         rw [show K.act 4 A (s^4 • R i j)=s^4 • (K.act 4 A (R i j)) from f.map_smul ..,show K.act 4 A (R i j)= _ from hp.spin ..]
         simp only [Finset.smul_sum]; exact Finset.sum_congr rfl fun _ _=>Finset.sum_congr rfl fun _ _=> smul_comm ..
    have he1: V∈ SymSpace H.spin:=by
         refine sym_mem.mpr ⟨fun i j=>by unfold V;rw[show R i j=R j i from hp.conserved.symmetric ..],fun i j=>?_,fun A i j=>?_⟩
         · apply P.injective; rw[he.real]; unfold V;rw[P.apply_symm_apply]
           let f:= StressFlux.conjQ (d:=4) F.room.kernel.spin; change f (s^4 • _)= _; rw [map_smul,show f _=R i j from hp.conserved.real ..]
         rw[← (baseRights (C:=C) (H:=H) h).signed]; exact ht A.ortho i j
    obtain ⟨w,hw⟩:= (free_stress_bij (L:=C.book) h H.spin).2 ⟨V,(Further.PhysicalPeriodLimitF933.two _ _).2 he1⟩
    have hv : V= StressFlux.material (F₀) w:= (congr_arg Subtype.val hw).symm; let c:= -(w 3)
    have hy : y=StressFlux.material (F₀) (-weyl):=by unfold y standard4 Shelves.materialB; rw [show Fin.cons _ _ = -weyl from Over.FZone_c G]
    let T:= V - c • y
    have hY: y∈SymSpace H.spin:= (Further.PhysicalPeriodLimitF933.two _ _).1 (by rw [hy]; exact (tableStress H.spin (-weyl)).property)
    obtain ⟨u,q,hK,hT,-,hτ⟩:= stages (C:=C) h; rw[hK,hT] at hτ
    have hw : T∈ SymSpace H.spin:= Submodule.sub_mem _ he1 ((SymSpace H.spin).smul_mem c hY)
    have hh : Tensorial L T:= residual_sigma _ _ ht hτ _
    have ho(i j:Axis)(he:i≠j): T i j=0:=by
         unfold T; rw[hv,hy]; simp only [StressFlux.material,stress_of,if_neg he,map_smul,Pi.sub_apply,Pi.smul_apply,Pi.neg_apply,c]; change w 3 • _-(-w 3) • ((-(1:ℝ)) • _)=_;rw [smul_smul,neg_mul_neg,mul_one,sub_self]
    have hT(i): T i i=T 0 0:= flat_diag T hh ho ..
    let A':=stressTrace T; have hg:A'=(4:ℝ) • T 0 0:=by unfold A' stressTrace;
                                                             rw [Fin.sum_univ_four,hT (1:Axis),hT (2:Axis),hT (3:Axis)]; module
    obtain ⟨v,hV⟩:= Scalar_onto (C:=C) (H:=H) h A' (by rw[hg,map_smul]; exact congr_arg _ ((sym_mem.mp hw).2.1 ..)) (fun i=> by change (F₀).mirror H.spin 4 i A'= _; rw[← (baseRights (C:=C) (H:=H) h).signed]; exact stressTrace_turn hh _)
    rw[scalar_cod, hg] at hV
    refine ⟨c,v 1, v 0/4,fun i j=> ?_⟩
    suffices hx:T i j=(if i=j then _ else _) by change V i j=c • y i j+_; rw[← hx];change _= _+(V i j- _); exact (add_sub_cancel ..|>.symm)
    split_ifs with e
    · subst j;rw[hT]; apply smul_right_injective _ (by norm_num : (4:ℝ)≠0); change (4:ℝ) • T 0 0=_;rw[← hV]; unfold stepField; module
    exact ho _ _ e
end YM.Trace.Pilot
