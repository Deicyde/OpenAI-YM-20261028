import YM.TraceExtension.Atlas.Purse
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

open StressFlux TraceExtension
-- unselected centering. Selected follows later by fixed linear relation.
abbrev lum(F: Final C X S) := TraceExtension.theta S F.sector.energy
lemma sceneV (H:(Bel C.book).Hierarchy) : expectation (F₀) 4 (OScale C.book)=0:=by
    have hu : expectation (F₀) 4 ((4:ℝ) • OScale C.book)=0:=by rw[← sum_delta (C:=C),map_sum]; apply Finset.sum_eq_zero; intro i _; rw [Further.PhysicalPeriodLimitF933.expectation_is]; unfold Shelves.materialB; rw [show oneStress _ _ _ _ _=_ from oneStress_formula (L:=C.book) _ i i 0]; norm_num
    exact (smul_eq_zero.mp ( ((expectation (F₀) 4).restrictScalars ℝ).map_smul (4:ℝ) _|>.symm.trans hu)).resolve_left (by norm_num)
lemma scalar_cod (v : Over.CP): ScalarP C v= v 0 • ((F₀).unit 4)+(4*v 1) • OScale C.book:=by change v 0 • _+v 1 • ((4:ℝ) • OScale C.book)=_;rw[smul_smul,mul_comm ((4:ℝ))]
lemma lum_real: S.conj F.room.kernel.spin 4 (lum F)=lum F:= trace_real F.phase.transport.conserved (fun _=> le_rfl) F.room.kernel
lemma lum_active: expectation S 4 (lum F)=0:=by rw[onepoint]; exact centerIn_vac (fun _=>le_rfl) F.room.kernel ..
lemma lum_spin(g): F.sector.turns.act 4 g (lum F)=lum F:= trace_turn F.phase.transport.spin F.phase.transport.spots g
lemma force_neg(h:G.Simple): d2 G < 0:=by rw[force_b]; unfold b0; have hx:= Gauge.casimir_pos h; rw[neg_div]; simp only [Left.neg_neg_iff]; positivity
lemma scale_alive(h:G.Simple)(H:(Bel C.book).Hierarchy): OScale C.book≠0:=by
    intro ht; let v : Over.CP:= ![0,1]; have he: v=0:= Scalar_inj h H (show ScalarP C v=ScalarP C 0 by rw[scalar_cod, ht,map_zero];simp[v]); exact one_ne_zero (show (1:ℝ)=0 from congr_fun he 1)
lemma scale_vector(h:G.Simple)(H:(Bel C.book).Hierarchy)(v:Active (Bel C.book))(ht:starA H v=v)(hh:∀ s,swingA H s v=v): ∃ c:ℝ,v.val=c • OScale C.book:=by
   obtain ⟨w,hw⟩:=Scalar_onto (C:=C) (H:=H) h (v.val) (show (Bel C.book).conj H.spin 4 v.val = v.val by rw[← star_act H, ht]) (fun s=> show (F₀).mirror H.spin 4 s v.val=v.val by rw [← swing_act H,hh])
   let p:= ((expectation (F₀) 4).restrictScalars ℝ); have hv:= congr_arg p hw; rw[scalar_cod, map_add,map_smul,map_smul,show p ((F₀).unit 4)=1 from mean_unit H.laws, show p (OScale C.book)=0 from sceneV H, show p v.val=0 from v.property,smul_zero,add_zero] at hv
   have hE:w 0=0:=by simpa [Complex.real_smul] using hv
   rw[scalar_cod,hE,zero_smul,zero_add] at hw; exact ⟨_,hw.symm⟩
-- anchor calibration using *only* UV station choices before O alignment. Not defined by stress tests!
def BranchV (F:Final C X S)(𝓛:Ultrafilter (ℕ×ℕ))(H:(Bel C.book).Hierarchy)(v:S.Field 4): Prop:= ∃ (J:Scaling S), StarPath X H J F.room.kernel 𝓛 ∧
    ∀ᶠ i in atTop, ∃ c:ℝ,0<c ∧ c • centering S 4 (J.U i 4 (OScale C.book))=v
include h h₁
lemma sees_l : ∃ d e:ℕ→ℝ, Tendsto (fun i=> BQ Z V i*d i) atTop (𝓝 (d2 G)) ∧
    ∀ᶠ i in atTop,d i<0 ∧ J.U i 4 (ScalarP C (![e i,d i]))= ((J.r i)^ (4:ℕ)) • lum F:=by
    obtain ⟨d,e,hg,hD,hE⟩:= h₁.gallery S F.room.kernel (fun _=> le_rfl)
    refine ⟨d,e,hD,?_⟩; filter_upwards[hg,hD.eventually (gt_mem_nhds (force_neg h)),h₁.grows.eventually_gt_atTop 0] with i hi hv hu; rw[← hi]; refine ⟨?_,(J.U i 4).apply_symm_apply _⟩; nlinarith
lemma branch_loss : ∀ᶠ i in atTop, ∃ c:ℝ,0<c∧ c • centering S 4 ((J.U i 4) (OScale C.book))= -lum F:=by
    obtain ⟨d,e,hq,hV⟩:= sees_l F h h₁
    let K:= F.room.kernel; filter_upwards[hV,h₁.monorail.units 4] with i hi ht
    let A:=J.U i 4; let P:= A.toLinearMap.restrictScalars ℝ; let r:= J.r i^ (4:ℕ); have hr:0 < r:= pow_pos (J.positive i) _; let p:=4*d i; let L:= (centering S 4).restrictScalars ℝ
    have he:=congr_arg L hi.2; rw[scalar_cod] at he; change L (P (e i • ((F₀).unit 4)+p • OScale C.book))= L (r • lum F) at he; rw [map_add,map_smul,map_smul,map_add,map_smul,map_smul, show P ((F₀).unit 4)=S.unit 4 from ht.2,show L (S.unit 4)=0 from const_out K.laws,smul_zero,zero_add,map_smul,show L _ = lum F from zero_center (⟨lum F,lum_active F⟩:Active S)] at he
    refine ⟨(-p)/r, div_pos ?_ hr,?_⟩
    · have ht:= hi.1;unfold p;linarith
    change (-p/r) • L _=_; rw[neg_div,neg_smul]; congr 1; rw[div_eq_mul_inv,mul_comm,← smul_smul]; change r⁻¹ • p • L (P (OScale C.book))=_; rw [he,inv_smul_smul₀ hr.ne']
lemma unselected_alive : lum F ≠ 0:=by
    intro he; have ht:= h₁.goal S
    rw[show TraceExtension.theta S _=0 from he ] at ht; unfold ZoomValue at ht; simp_rw[smul_zero,map_zero] at ht; have hx:= (smul_ne_zero (show (4*d2 G)≠0 from mul_ne_zero (by norm_num) (force_neg h).ne) (scale_alive h H)).symm
    exact hx (tendsto_nhds_unique tendsto_const_nhds ht)
lemma reach_right : BranchV F 𝓛 H (-lum F) := ⟨J,h₁.monorail,branch_loss F h h₁⟩
omit h₁ in
lemma gardens (a: S.Field 4)(ha: BranchV F 𝓛 H a)(hp: ∀ (J : Scaling S), StarPath X H J F.room.kernel 𝓛 → ∀ V Y,Gondola X H J 𝓛 V Y→ Scribe X J V Z F.sector 𝓛 F.room.kernel H): ∃ u:ℝ,0 < u∧ a=u • (-lum F):=by
    obtain ⟨J,HJ,hA⟩:=ha
    obtain ⟨V,Y,hY⟩:= gravity F.room.kernel HJ
    obtain ⟨i,⟨c,hc,hc'⟩,b,hb,hb'⟩:= ((branch_loss F h (hp J HJ _ _ hY)).and hA).exists
    refine ⟨b/c, by positivity,?_⟩; rw[← hb',← hc',smul_smul,div_mul_cancel₀ _ hc.ne']
omit h h₁ in
lemma illuminated {a}(hs:BranchV F 𝓛 H a)(u:ℝ)(hu:0<u):BranchV F 𝓛 H (u • a):=by
    obtain ⟨J,h,H⟩:= hs; refine ⟨J,h,H.mono fun i hi=> ?_⟩; obtain ⟨c,hc,hc'⟩:= hi; exact ⟨u*c, mul_pos hu hc,by rw[← hc',smul_smul]⟩
end YM.Trace.Pilot
